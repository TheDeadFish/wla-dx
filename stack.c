
#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdarg.h>

#include "defines.h"

#include "hashmap.h"
#include "parse.h"
#include "pass_1.h"
#include "stack.h"
#include "include_file.h"
	
static
int is_end_token(char e) {
	return e == ' ' || e == ')' || e == '|' || e == '&' || e == '+' 
		|| e == '-' || e == '*' || e == '/' || e == ',' || e == '^' || e == '<' 
		|| e == '>' || e == '#' || e == '~' || e == ']' || e == '=' || e == '!'
		|| e == '?' || e == ':' || isNewLn(e);
}

extern int input_number_error_msg, bankheader_status, input_float_mode;
extern int i, size, d, macro_active, string_size, section_status, parse_floats;
extern char *buffer, tmp[4096], expanded_macro_string[256], label[MAX_NAME_LENGTH + 1];
extern struct definition *tmp_def;
extern struct map_t *defines_map;
extern struct active_file_info *active_file_info_first, *active_file_info_last, *active_file_info_tmp;
extern struct macro_runtime *macro_runtime_current;
extern struct section_def *sec_tmp;
extern double parsed_double;

int latest_stack = 0, stacks_inside = 0, stacks_outside = 0, stack_id = 0;
struct stack *stacks_first = NULL, *stacks_tmp = NULL, *stacks_last = NULL;
struct stack *stacks_header_first = NULL, *stacks_header_last = NULL;

#ifndef GB
extern int stack_inserted;
#endif

static	
int num_error(const char* fmt, ...) 
{
	char xyz[512];
	va_list va; va_start (va, fmt);
  vsprintf (xyz,fmt, va);
	print_error(xyz, ERROR_NUM); 
	return FAILED;
}

static	
int stack_error(const char* fmt, ...) 
{
	char xyz[512];
	va_list va; va_start (va, fmt);
  vsprintf (xyz,fmt, va);
	print_error(xyz, ERROR_STC); 
	return FAILED;
}

#if defined(MCS6502) || defined(W65816) || defined(MCS6510) || defined(WDC65C02) || defined(HUC6280) || defined(MC6800)
extern int operand_hint;

int stack_parseDot(char* in)
{
	int d = operand_hint; char e = in[1];
	if (e == 'b' || e == 'B') { operand_hint = HINT_8BIT; }
	else if (e == 'w' || e == 'W') { operand_hint = HINT_16BIT; }
#if defined(W65816)
	else if (e == 'l' || e == 'L') { operand_hint = HINT_24BIT; }
#endif
	else { stack_error("invalid operand hint!\n"); return 0; }
	if (d != HINT_NONE && d != operand_hint) {
		stack_error("Confusing operand hint!\n"); }
	return 2;
}

#define HAS_OPHINT
#endif

static int _stack_insert(void) {

  /* outside bankheader sections */
  if (bankheader_status == OFF) {
    if (stacks_first == NULL) {
      stacks_first = stacks_tmp;
      stacks_last = stacks_tmp;
    }
    else {
      stacks_last->next = stacks_tmp;
      stacks_last = stacks_tmp;
    }
    stacks_outside++;

#ifndef GB
    stack_inserted = STACK_OUTSIDE;
#endif
  }
  /* inside a bankheader section */
  else {
    if (stacks_header_first == NULL) {
      stacks_header_first = stacks_tmp;
      stacks_header_last = stacks_tmp;
    }
    else {
      stacks_header_last->next = stacks_tmp;
      stacks_header_last = stacks_tmp;
    }
    stacks_inside++;

#ifndef GB
    stack_inserted = STACK_INSIDE;
#endif
  }

  stacks_tmp->id = stack_id;
  stacks_tmp->section_status = section_status;
  if (section_status == ON)
    stacks_tmp->section_id = sec_tmp->id;
  else
    stacks_tmp->section_id = 0;

  latest_stack = stack_id;
  stack_id++;

  return SUCCEEDED;
}


static int _break_before_value_or_string(int i, struct stack_item *si) {

  /* we use this function to test if the previous item in the stack
     is something that cannot be followed by a value or a string.
     in such a case we'll stop adding items to this stack computation */
  
  if (i <= 0)
    return FAILED;

  si = &si[i-1];
  if (si->type == STACK_ITEM_TYPE_VALUE)
    return SUCCEEDED;
  if (si->type == STACK_ITEM_TYPE_STRING)
    return SUCCEEDED;
  if (si->type == STACK_ITEM_TYPE_STRVAL)
    return SUCCEEDED;
  if (si->type == STACK_ITEM_TYPE_OPERATOR && si->value == SI_OP_RIGHT)
    return SUCCEEDED;

  return FAILED;
}

char* stack_parseNum(double* out, char* in, int base)
{
	/* parse the number */
	char* end; int e;	
	if(isspace(*in)) { end = in; } else 
	if(base) { *out = strtoul(in, &end, base); }
	else { *out = strtod(in, &end); base = 10; }
	
	/* check end token */
	e = *end; 
	if(in != end) {
		if(is_end_token(e) || e == '.') return end;
		if(base == 16 && (e == 'h' || e == 'H')) 
			return end+1; 
	}

	/* print error message */
	if (input_number_error_msg == YES)
		num_error("Got '%c' (%d) when expected [0-%X].\n", e, e, base-1);
	return NULL;
}


char* stack_parseDec(double* value, char* in) 
{
	int k;
	for(k = 0;; k++) {
		if(isdigit(in[k])) continue;
		if(isalpha(in[k])) return stack_parseNum(value, in, 16);
		if(in[k] == '.') {
			if(isdigit(in[k+1]) && parse_floats)
				return stack_parseNum(value, in, 0); }
		return stack_parseNum(value, in, 10);
	}
}

char* stack_parseChar(double* value, char* in) 
{
	if(isNewLn(in[0])||(in[1] != '\'')) {
		num_error("Bad character literal");
		return NULL; }
	*value = in[0]; return in+2;
}

static 
int is_operand_hint(char* in)
{
	return (in[0] == '.' && (in[1] == 'b' || in[1] == 'B' || 
		in[1] == 'w' || in[1] == 'W' || in[1] == 'l' || in[1] == 'L') 
		&& is_end_token(in[2]));
}

typedef struct {
	char str[2]; 
	char binop, uniop;
} op_table;


enum {
	/* internal operators */
	SI_OP_UNIPLUS = 23,
	
	SI_OP_PLUS_PAIR,
	SI_OP_MINUS_PAIR,
	SI_OP_BREAK,
	
	SI_OP_DOT,
	SI_OP_INVALID,
	SI_OP_TERNARY2,
	
	/* value or string */
	SI_OP_DOLLAR, SI_OP_DECIMAL,
	SI_OP_PERCENT, SI_OP_CHAR,
	SI_OP_STRING, SI_OP_STRVAL
};

int op_presidence(int code)
{
	switch(code & 255) {
	case SI_OP_NEGATE:
	case SI_OP_LOW_BYTE:
	case SI_OP_HIGH_BYTE:
		/* right to left */
		if(code < 0) return -1;
		return 0;
	case SI_OP_PLUS:
	case SI_OP_MINUS:
		return 2;
		
	case SI_OP_TERNARY:
	case SI_OP_TERNARY2:
		/* right to left */
		if(code < 0) return 200-1;
		return 200;
		
	case SI_OP_RIGHT: return 244;
	case SI_OP_LEFT: return 255;
	default: return 1;
	}
}

op_table opList[] = {

	/* main operators */
	{"+",  SI_OP_PLUS          ,SI_OP_UNIPLUS},
	{"-",  SI_OP_MINUS         ,SI_OP_NEGATE},
	{"*",  SI_OP_MULTIPLY      ,-SI_OP_INVALID },
	{"(",  -SI_OP_INVALID       ,SI_OP_LEFT},
	{")",  -SI_OP_RIGHT         ,-SI_OP_INVALID},      
	{"|",  SI_OP_OR            ,-SI_OP_INVALID}, 
	{"&",  SI_OP_AND           ,-SI_OP_INVALID}, 
	{"/",  SI_OP_DIVIDE        ,-SI_OP_INVALID},
	{"^",  SI_OP_POWER         ,-SI_OP_INVALID},
	{"<<", SI_OP_SHIFT_LEFT    ,-SI_OP_INVALID},
	{">>", SI_OP_SHIFT_RIGHT   ,-SI_OP_INVALID},
	{"#",  SI_OP_MODULO        ,-SI_OP_INVALID},
	{"~",  SI_OP_XOR           ,-SI_OP_INVALID},
	{"<",  SI_OP_CMP_LESS       ,SI_OP_LOW_BYTE},
	{">",  SI_OP_CMP_GRTH       , SI_OP_HIGH_BYTE},
	
	
	/* comparison operators */
	{"==", SI_OP_CMP_EQU       ,-SI_OP_INVALID},
	{"!=", SI_OP_CMP_NEQU      ,-SI_OP_INVALID},
	{">=", SI_OP_CMP_GREQ      ,-SI_OP_INVALID},
	{"<=", SI_OP_CMP_LTEQ      ,-SI_OP_INVALID},
	
	/* internal operators */
	{"++", -SI_OP_INVALID       ,-SI_OP_PLUS_PAIR},
	{"--", -SI_OP_INVALID       ,-SI_OP_MINUS_PAIR},
	{"$", -SI_OP_BREAK        ,SI_OP_DOLLAR},
	{"%", -SI_OP_BREAK        ,SI_OP_PERCENT},
	{"\'", -SI_OP_BREAK        ,SI_OP_CHAR},
	{"\"", -SI_OP_BREAK        ,SI_OP_STRVAL},
	
	{":", SI_OP_TERNARY        ,-SI_OP_STRING},
	{"?", SI_OP_TERNARY2        ,-SI_OP_INVALID},
	
	
	
	
	
	
	
	
	
	
#ifdef HAS_OPHINT
	{".", -SI_OP_DOT         ,-SI_OP_INVALID},
#endif

	{"", 0, 0 }
};



static op_table decOp = {"", -SI_OP_BREAK, -SI_OP_DECIMAL};
static op_table strOp = {"", -SI_OP_BREAK, -SI_OP_STRING};

typedef struct {
	char* in; int code;
} op_result;

op_result op_list_lookup(char* in, int valBefore)
{
	op_table* pos = opList;
	op_table* op = &strOp;
	op_result ret;
	
	for(;*in == ' '; in++);
	if(isNewLn(*in) || *in == ',' || *in == ']') {
		ret.code = SI_OP_BREAK; goto OP_RET2; }
	if(isdigit(*in)) { op = &decOp; goto OP_RET; }
		
	/* lookup operator */
	for(;pos->str[0]; pos++) {
		if(pos->str[0] != in[0]) continue;
		if(pos->str[1] == in[1]) { op = pos; break; }
		if(pos->str[1] == 0) { op = pos; }
	}
	
	/* return operator */
OP_RET:
	ret.code = valBefore>0 ? op->binop : op->uniop;
	if(ret.code < 0) { ret.code = -ret.code; }
	else { if(op->str[1]) in++; in++; }
OP_RET2: ret.in = in; return ret;
}

#define STACK_VALUE_ITEM(xxx) { if(!(in=xxx)) return FAILED; \
	si[q].type = STACK_ITEM_TYPE_VALUE; q++; continue; }

int stack_calculate(char *in, int *value) {

  int q = 0, b = 0, d, k, op[256];
  struct stack_item si[256], ta[256];
  struct stack s;
  unsigned char e;
  double dou = 0.0;
	op_result opi;


  /* initialize (from Amiga's SAS/C) */
  for (k = 0; k < 256; k++) {
    si[k].type = STACK_ITEM_TYPE_VALUE;
    si[k].value = 0.0;
    si[k].string[0] = 0;
  }
  
  /* slice the data into infix format */
  while (1) {
	
    /* init the stack item */
    si[q].type = 0x123456;
    si[q].value = 0x123456;
    si[q].string[0] = 0;
		
		
		/* get the operator */
		opi = op_list_lookup(in, 
			_break_before_value_or_string(q, si));
		in = opi.in;
		
		
		/*printf("op: %d\n", opi.code);*/
		
		switch(opi.code)
		{
		case SI_OP_UNIPLUS: continue;
		case SI_OP_BREAK:	goto LOOP_BREAK;
		
		/* local labels */
		case SI_OP_PLUS_PAIR:
		case SI_OP_MINUS_PAIR: e = *in;			
			for (k = 0; *in == e && k < 32; k++, in++)
				 si[q].string[k] = e;
			si[q].type = STACK_ITEM_TYPE_STRING;
			q++; break;
			
		/* parentheses */
		case SI_OP_LEFT: 
			b++; goto SIMPLE_OPERATOR;
		case SI_OP_RIGHT:
			if(--b < 0) goto LOOP_BREAK;
			in++; goto SIMPLE_OPERATOR;
			
		/* comparison operators */
		case SI_OP_CMP_EQU: case SI_OP_CMP_NEQU:
		case SI_OP_CMP_LESS: case SI_OP_CMP_GRTH:
		case SI_OP_CMP_LTEQ: case SI_OP_CMP_GREQ:

		/* simple operators */
		case SI_OP_TERNARY: case SI_OP_TERNARY2:
		case SI_OP_PLUS: case SI_OP_MINUS: case SI_OP_MULTIPLY:
		case SI_OP_DIVIDE: case SI_OP_OR: case SI_OP_AND:
		case SI_OP_POWER: case SI_OP_MODULO: case SI_OP_XOR:
		case SI_OP_SHIFT_LEFT: case SI_OP_SHIFT_RIGHT:
		case SI_OP_NEGATE: case SI_OP_HIGH_BYTE:	case SI_OP_LOW_BYTE:
	SIMPLE_OPERATOR:
			si[q].type = STACK_ITEM_TYPE_OPERATOR;
			si[q].value = opi.code; q++; break;

#ifdef HAS_OPHINT
		case SI_OP_DOT: d = stack_parseDot(in);
			if(!d){ return FAILED; } in += d; break;
#endif
		
		/* value items */
		case SI_OP_PERCENT:
			STACK_VALUE_ITEM(stack_parseNum(&si[q].value, in, 2));
		case SI_OP_DOLLAR:
			STACK_VALUE_ITEM(stack_parseNum(&si[q].value, in, 16));
		case SI_OP_DECIMAL:
			STACK_VALUE_ITEM(stack_parseDec(&si[q].value, in));
		case SI_OP_CHAR:
			STACK_VALUE_ITEM(stack_parseChar(&si[q].value, in));
			
		case SI_OP_STRVAL:
			for (k = 0; (e = *in++) != '"'; k++) {
				if(isNewLn(e)) { num_error("String wasn't "
					"terminated properly.\n"); return FAILED; }
				if(k >= MAX_NAME_LENGTH) { num_error("The string is too long "
					"(max %d characters allowed).\n", MAX_NAME_LENGTH); return FAILED; }
				if (e == '\\' && *in == '"') { e = *in++; } si[q].string[k] = e; }
			si[q].type = STACK_ITEM_TYPE_STRVAL;
			si[q].string[k] = 0; q++; break;

		case SI_OP_STRING:
			for (k = 0; k < 63; k++, in++) {
				if((is_end_token(*in))||is_operand_hint(in)) 
					break; else si[q].string[k] = *in; }
			si[q].type = STACK_ITEM_TYPE_STRING;
			si[q].string[k] = 0; q++; break;
			
		default:;
			stack_error("invalid use of operator (%c)\n", *in);
			return FAILED;
		}

    if (q == 255) {
      print_error("Out of stack space.\n", ERROR_STC);
      return FAILED;
    }
  }
LOOP_BREAK:

  if (b != 0) {
    print_error("Unbalanced parentheses.\n", ERROR_STC);
    return FAILED;
  }

#ifdef SPC700
  /* check if the computation is of the form "y+X" or "y+Y" and remove that "+X" or "+Y" */
  if (q > 2 && si[q - 2].type == STACK_ITEM_TYPE_OPERATOR && si[q - 2].value == SI_OP_PLUS) {
    if (si[q - 1].type == STACK_ITEM_TYPE_STRING && si[q - 1].string[1] == 0) {
      char w = si[q - 1].string[0];

      if (w == 'x' || w == 'X' || w == 'y' || w == 'Y') {
	q -= 2;
	while (*in != '+')
	  in--;
      }
    }
  }
#endif

#if 0
  /* calculate all X.length strings */
  for (k = 0; k < q; k++) {
    if (si[k].type == STACK_ITEM_TYPE_STRING) {
      if (is_string_ending_with(si[k].string, ".length") > 0 ||
	  is_string_ending_with(si[k].string, ".LENGTH") > 0) {
	/* we have a X.length -> parse */
	strcpy(label, si[k].string);
	label[strlen(label) - 7] = 0;

	hashmap_get(defines_map, label, (void*)&tmp_def);

	if (tmp_def != NULL) {
	  if (tmp_def->type == DEFINITION_TYPE_STRING) {
	    memcpy(label, tmp_def->string, tmp_def->size);
	    label[tmp_def->size] = 0;

	    si[k].value = strlen(label);
	    si[k].type = STACK_ITEM_TYPE_VALUE;
	  }
	}
      }
    }
  }
#endif

  /* update the source pointer */
  i = (int)(in - buffer);

  /* convert infix stack into postfix stack */
  for (b = 0, k = 0, d = 0; k < q; k++) {
    /* operands pass through */
    if (si[k].type == STACK_ITEM_TYPE_VALUE) {
      ta[d].type = si[k].type;
      ta[d].value = si[k].value;
      d++;
    }
    else if ((si[k].type == STACK_ITEM_TYPE_STRING)
			|| (si[k].type == STACK_ITEM_TYPE_STRVAL)) 
		{
      ta[d].type = si[k].type;
      strcpy(ta[d].string, si[k].string);
      d++;
    }
    /* operators get inspected */
    else if (si[k].type == STACK_ITEM_TYPE_OPERATOR) {
			int value = si[k].value;
			
			/* evict items from stack */
			b--; if (value != SI_OP_LEFT) {
				int p = op_presidence(value|INT_MIN);
				for(;b >= 0 && op_presidence(op[b]) <= p; b--, d++) {
					ta[d].type = STACK_ITEM_TYPE_OPERATOR; ta[d].value = op[b]; }
			}
			
			/* insert item into stack */
			if (value != SI_OP_RIGHT) { 
				b++; op[b] = value; b++; }
		}
	}

  /* empty the operator stack */
  while (b > 0) {
    b--;
    ta[d].type = STACK_ITEM_TYPE_OPERATOR;
    ta[d].value = op[b];
    d++;
  }

  /* are all the symbols known? */
  if (resolve_stack(ta, d) == SUCCEEDED) {
    s.stack = ta;
    s.linenumber = active_file_info_last->line_current;
    s.filename_id = active_file_info_last->filename_id;

		d = compute_stack(&s, d, &dou);
		if((d == FAILED)||(d == INPUT_NUMBER_STRING))
			return d;
    
    parsed_double = dou;

    if (input_float_mode == ON)
      return INPUT_NUMBER_FLOAT;

    *value = (int)dou;

    return SUCCEEDED;
  }

  /* only one string? */
  if (d == 1 && ta[0].type == STACK_ITEM_TYPE_STRING) {
    strcpy(label, ta[0].string);
    return STACK_RETURN_LABEL;
  }

  /*
  printf("%d %d %s\n", d, ta[0].type, ta[0].string);
  */

#if WLA_DEBUG
  /* DEBUG output */
  printf("LINE %5d: (STACK) CALCULATION ID = %d (c%d): ", active_file_info_last->line_current, stack_id, stack_id);
  for (k = 0; k < d; k++) {
    char ar[] = "+-*()|&/^01%~<>";

    if (ta[k].type == STACK_ITEM_TYPE_OPERATOR) {
      int value = (int)ta[k].value;
      char arr = ar[value];

      /* 0 - shift left, 1 - shift right, otherwise it's the operator itself */
      if (arr == '0')
	printf("<<");
      else if (arr == '1')
	printf(">>");
      else
	printf("%c", arr);
    }
    else if (ta[k].type == STACK_ITEM_TYPE_VALUE)
      printf("V(%f)", ta[k].value);
    else if (ta[k].type == STACK_ITEM_TYPE_STACK)
      printf("C(%d)", (int)ta[k].value);
    else
      printf("S(%s)", ta[k].string);

    if (k < d-1)
      printf(", ");
  }
  printf("\n");
#endif

  /* we have a stack full of computation and we save it for wlalink */
  stacks_tmp = calloc(sizeof(struct stack), 1);
  if (stacks_tmp == NULL) {
    print_error("Out of memory error while allocating room for a new stack.\n", ERROR_STC);
    return FAILED;
  }
  stacks_tmp->next = NULL;
  stacks_tmp->type = STACKS_TYPE_UNKNOWN;
  stacks_tmp->bank = -123456;
  stacks_tmp->stacksize = d;
  stacks_tmp->relative_references = 0;
  stacks_tmp->stack = calloc(sizeof(struct stack_item) * d, 1);
  if (stacks_tmp->stack == NULL) {
    free(stacks_tmp);
    print_error("Out of memory error while allocating room for a new stack.\n", ERROR_STC);
    return FAILED;
  }

  stacks_tmp->linenumber = active_file_info_last->line_current;
  stacks_tmp->filename_id = active_file_info_last->filename_id;

  /* all stacks will be definition stacks by default. pass_4 will mark
     those that are referenced to be STACK_POSITION_CODE stacks */
  stacks_tmp->position = STACK_POSITION_DEFINITION;

  for (q = 0; q < d; q++) {
    if (ta[q].type == STACK_ITEM_TYPE_OPERATOR) {
      stacks_tmp->stack[q].type = STACK_ITEM_TYPE_OPERATOR;
      stacks_tmp->stack[q].value = ta[q].value;
    }
    else if (ta[q].type == STACK_ITEM_TYPE_VALUE) {
      stacks_tmp->stack[q].type = STACK_ITEM_TYPE_VALUE;
      stacks_tmp->stack[q].value = ta[q].value;
    }
    else if (ta[q].type == STACK_ITEM_TYPE_STACK) {
      stacks_tmp->stack[q].type = STACK_ITEM_TYPE_STACK;
      stacks_tmp->stack[q].value = ta[q].value;
    }
    else {
      stacks_tmp->stack[q].type = STACK_ITEM_TYPE_STRING;
      strcpy(stacks_tmp->stack[q].string, ta[q].string);
    }
  }

  _stack_insert();

  return INPUT_NUMBER_STACK;
}


int resolve_stack(struct stack_item s[], int x) {

  struct macro_argument *ma;
  struct stack_item *st;
  int a, b, k, q = x, cannot_resolve = 0;
  char c;


  st = s;
  while (x > 0) {
    if (s->type == STACK_ITEM_TYPE_STRING) {
      if (macro_active != 0 && s->string[0] == '\\') {
	if (s->string[1] == '@' && s->string[2] == 0) {
	  s->type = STACK_ITEM_TYPE_VALUE;
	  s->value = macro_runtime_current->macro->calls - 1;
	}
	else {
	  for (a = 0, b = 0; s->string[a + 1] != 0 && a < 10; a++) {
	    c = s->string[a + 1];
	    if (c < '0' && c > '9') {
	      print_error("Error in MACRO argument number definition.\n", ERROR_DIR);
	      return FAILED;
	    }
	    b = (b * 10) + (c - '0');
	  }
	  
	  if (b > macro_runtime_current->supplied_arguments) {
			stack_error("Reference to MACRO argument number %d is out of range.\n", b);
	    return FAILED;
	  }
	  
	  /* return the macro argument */
	  ma = macro_runtime_current->argument_data[b - 1];
	  k = ma->type;
	  
	  if (k == INPUT_NUMBER_ADDRESS_LABEL)
	    strcpy(label, ma->string);
	  else if (k == INPUT_NUMBER_STRING) {
	    strcpy(label, ma->string);
	    string_size = (int)strlen(ma->string);
	  }
	  else if (k == INPUT_NUMBER_STACK)
	    latest_stack = ma->value;
	  else if (k == SUCCEEDED) {
	    d = ma->value;
	    parsed_double = ma->value;
	  }
	  
	  if (!(k == SUCCEEDED || k == INPUT_NUMBER_ADDRESS_LABEL || k == INPUT_NUMBER_STACK))
	    return FAILED;
	  
	  if (k == SUCCEEDED) {
	    s->type = STACK_ITEM_TYPE_VALUE;
	    s->value = parsed_double;
	  }
	  else if (k == INPUT_NUMBER_STACK) {
	    s->type = STACK_ITEM_TYPE_STACK;
	    s->value = latest_stack;
	  }
	  else
	    strcpy(s->string, label);
	}
      }
      else {
	if (macro_active != 0) {
	  /* expand e.g., \1 and \@ */
	  if (expand_macro_arguments(s->string) == FAILED)
	    return FAILED;
	}

        hashmap_get(defines_map, s->string, (void*)&tmp_def);
        if (tmp_def != NULL) {
          if (tmp_def->type == DEFINITION_TYPE_STRING) {
						strcpy(s->string, tmp_def->string);
						s->type = STACK_ITEM_TYPE_STRVAL;
          }
          else if (tmp_def->type == DEFINITION_TYPE_STACK) {
	    /* skip stack definitions -> use its name instead, thus do nothing here */
          }
	  else if (tmp_def->type == DEFINITION_TYPE_ADDRESS_LABEL) {
	    /* wla cannot resolve address labels (unless outside a section) -> only wlalink can do that */
	    cannot_resolve = 1;
	    strcpy(s->string, tmp_def->string);
	  }
	  else {
            s->type = STACK_ITEM_TYPE_VALUE;
            s->value = tmp_def->value;
          }
        }
      }
    }
    s++;
    x--;
  }

  if (cannot_resolve != 0)
    return FAILED;

  /* find a string or a stack and fail */
  while (q > 0) {
    if (st->type == STACK_ITEM_TYPE_STRING || st->type == STACK_ITEM_TYPE_STACK)
      return FAILED;
    q--;
    st++;
  }

  return SUCCEEDED;
}

static	
int op_nArgs(int x) 
{
	switch(x) {
	case SI_OP_LOW_BYTE:
	case SI_OP_HIGH_BYTE:
	case SI_OP_NEGATE: return 1;
	default: return 2;
	}
}


#define EXEC_OP(op, fn) case op: v[t].v.f = fn; break;
#define STRI_OP(op, fn) case op: v[t].v.f = fn; v[t].type = 0; break;

struct comput_val { int type;
	union { double f; char* s; } v;
};


int compute_stack(struct stack *sta, int x, double *result) {

  struct stack_item *s;
  struct comput_val v[256];
  int r, t;
	double a1, a2;
	int i1, i2;
	char *s1, *s2;
	
	

	v[0].v.f = 0.0;
	v[0].type = STACK_ITEM_TYPE_VALUE;

  s = sta->stack;
  for (r = 0, t = -1; r < x; r++, s++) {
	/*printf("%d, %d\n", s->type, (int)s->value);*/
	
	
    if (s->type == STACK_ITEM_TYPE_VALUE) {
			t++; v[t].type = 0; v[t].v.f = s->value; }
		else if(s->type == STACK_ITEM_TYPE_STRVAL) {
			t++; v[t].type = 1; v[t].v.s = s->string; }
		
    else {
		
			int code = (int)s->value;
			
			/* ternary operator */
			if(code == SI_OP_TERNARY) { t--; t--;
				if(v[t].type != 0) { stack_error(
					"invalid operand type\n"); return FAILED; }
				v[t] = v[t].v.f ? v[t+1] : v[t+2]; 
				continue; }

			if(v[t].type != 0) {
			
				/* fetch string args */
				s2 = v[t].v.s;
				if(op_nArgs(code) > 1) { t--;
					if(v[t].type == 0) { stack_error(
						"invalid operand type\n"); return FAILED; }}
				s1 = v[t].v.s;
				
				switch(code) {
				
				/* string comparison */
				STRI_OP(SI_OP_CMP_EQU, strcmp(s1, s2)==0);
				STRI_OP(SI_OP_CMP_NEQU, strcmp(s1, s2)!=0);
				STRI_OP(SI_OP_CMP_LESS, strcmp(s1, s2)<0);
				STRI_OP(SI_OP_CMP_GRTH, strcmp(s1, s2)>0);			
				STRI_OP(SI_OP_CMP_GREQ, strcmp(s1, s2)<=0);
				STRI_OP(SI_OP_CMP_LTEQ, strcmp(s1, s2)>=0);
				
				default:
					stack_error("invalid operand type\n"); 
					return FAILED;
				}
				
			} else {
			
				/* fetch number args */
				a2 = v[t].v.f;
				if(op_nArgs(code) > 1) { t--;
					if(v[t].type != 0) { stack_error(
						"invalid operand type\n"); return FAILED; }}
				a1 = v[t].v.f; i1 = a1; i2 = a2;
				
				switch (code) {
				
				/* arithmetic operators */
				EXEC_OP(SI_OP_PLUS, a1+a2);
				EXEC_OP(SI_OP_MINUS, a1+a2);
				EXEC_OP(SI_OP_MULTIPLY, a1*a2);
				EXEC_OP(SI_OP_DIVIDE, a1/a2);
				EXEC_OP(SI_OP_POWER, pow(a1,a2));
				EXEC_OP(SI_OP_MODULO, i1%i2);
				
				/* comparison operators */
				EXEC_OP(SI_OP_CMP_EQU, a1 == a2);
				EXEC_OP(SI_OP_CMP_NEQU, a1 != a2);
				EXEC_OP(SI_OP_CMP_LESS, a1 < a2);
				EXEC_OP(SI_OP_CMP_GRTH, a1 > a2);			
				EXEC_OP(SI_OP_CMP_GREQ, a1 <= a2);
				EXEC_OP(SI_OP_CMP_LTEQ, a1 >= a2);
				
				/* binrary operations */
				EXEC_OP(SI_OP_XOR, i1 ^ i2)
				EXEC_OP(SI_OP_AND, i1 & i2)
				EXEC_OP(SI_OP_OR, i1 | i2)
				EXEC_OP(SI_OP_SHIFT_LEFT, i1 << i2)
				EXEC_OP(SI_OP_SHIFT_RIGHT, i1 >> i2)

				/* unaray operators */
				EXEC_OP(SI_OP_NEGATE, -a1)
				EXEC_OP(SI_OP_LOW_BYTE, i1 & 0xFF);
				EXEC_OP(SI_OP_HIGH_BYTE, (i1>>8) & 0xFF);
				}		
			}
    }
  }

  /*
#ifdef W65816
  if (v[0] < -8388608 || v[0] > 16777215) {
    print_error("Out of 24-bit range.\n", ERROR_STC);
    return FAILED;
  }
#else
  if (v[0] < -32768 || v[0] > 65536) {
    print_error("Out of 16-bit range.\n", ERROR_STC);
    return FAILED;
  }
#endif
  */
	
	
	if(v[0].type) {
		strcpy(label, v[0].v.s); 
		string_size = strlen(label);
		return INPUT_NUMBER_STRING; }

  *result = v[0].v.f;

  return SUCCEEDED;
}


int stack_create_label_stack(char *label) {

  if (label == NULL)
    return FAILED;

  /* we need to create a stack that holds just one label */
  stacks_tmp = calloc(sizeof(struct stack), 1);
  if (stacks_tmp == NULL) {
    print_error("Out of memory error while allocating room for a new stack.\n", ERROR_STC);
    return FAILED;
  }
  stacks_tmp->next = NULL;
  stacks_tmp->type = STACKS_TYPE_UNKNOWN;
  stacks_tmp->bank = -123456;
  stacks_tmp->stacksize = 1;
  stacks_tmp->relative_references = 0;
  stacks_tmp->stack = calloc(sizeof(struct stack_item), 1);
  if (stacks_tmp->stack == NULL) {
    free(stacks_tmp);
    print_error("Out of memory error while allocating room for a new stack.\n", ERROR_STC);
    return FAILED;
  }

  stacks_tmp->linenumber = active_file_info_last->line_current;
  stacks_tmp->filename_id = active_file_info_last->filename_id;

  /* all stacks will be definition stacks by default. pass_4 will mark
     those that are referenced to be STACK_POSITION_CODE stacks */
  stacks_tmp->position = STACK_POSITION_DEFINITION;

  stacks_tmp->stack[0].type = STACK_ITEM_TYPE_STRING;
  strcpy(stacks_tmp->stack[0].string, label);

  _stack_insert();

  return SUCCEEDED;
}
