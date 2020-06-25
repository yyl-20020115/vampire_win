
/*
 * File TPTP.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file Parse/TPTP.cpp
 * Implements class TPTP for parsing TPTP files
 *
 * @since 08/04/2011 Manchester
 */

#include <fstream>

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"

#include "Lib/Int.hpp"
#include "Lib/Environment.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Theory.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/DistinctGroupExpansion.hpp"

#include "Indexing/TermSharing.hpp"

#include "Parse/TPTP.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;
using namespace Parse;

#define DEBUG_SHOW_TOKENS 0
#define DEBUG_SHOW_UNITS 0
#define DEBUG_SOURCE 0

DHMap<unsigned, vstring> TPTP::_axiomNames;

/**
 * Create a parser, parse the input and return the parsed list of units.
 * @since 13/07/2011 Manchester
 */
UnitList* TPTP::parse(istream& input)
{
  Parse::TPTP parser(input);
  try{
    parser.parse();
  }
  catch (UserErrorException& exception) {
    vstring msg = exception.msg();
    throw ParseErrorException(msg,parser.lineNumber());
  }
  return parser.units();
}

/**
 * Initialise a lexer.
 * @since 27/07/2004 Torrevieja
 */
TPTP::TPTP(istream& in)
  : _containsConjecture(false),
    _allowedNames(0),
    _in(&in),
    _includeDirectory(""),
    _currentColor(COLOR_TRANSPARENT),
    _modelDefinition(false),
    _insideEqualityArgument(0),
    _unitSources(0),
    _filterReserved(false),
    _seenConjecture(false)
{
} // TPTP::TPTP

/**
 * The destructor, does nothing.
 * @since 09/07/2012 Manchester
 */
TPTP::~TPTP()
{
} // TPTP::~TPTP

/**
 * Read all tokens one by one 
 * @since 08/04/2011 Manchester
 */
void TPTP::parse()
{
  CALL("TPTP::parse");

  // bulding tokens one by one
  _gpos = 0;
  _cend = 0;
  _tend = 0;
  _lineNumber = 1;
  _states.push(Parse::TPTP::State::UNIT_LIST);
  while (!_states.isEmpty()) {
    State s = _states.pop();
#ifdef DEBUG_SHOW_STATE
    cout << "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~" << endl;
    cout << toString(s) << endl;
#endif
    switch (s) {
    case Parse::TPTP::State::UNIT_LIST:
      unitList();
      break;
    case Parse::TPTP::State::FOF:
      _isFof = true;
      fof(true);
      break;
    case Parse::TPTP::State::TFF:
    case Parse::TPTP::State::THF:
      _isFof = false;
      tff();
      break;
    case Parse::TPTP::State::CNF:
      _isFof = true;
      fof(false);
      break;
    case Parse::TPTP::State::FORMULA:
      formula();
      break;
    case Parse::TPTP::State::FUN_APP:
      funApp();
      break;
    case Parse::TPTP::State::ARGS:
      args();
      break;
    case Parse::TPTP::State::TERM:
      term();
      break;
    case Parse::TPTP::State::TERM_INFIX:
      termInfix();
      break;
    case Parse::TPTP::State::END_TERM:
      endTerm();
      break;
    case Parse::TPTP::State::END_ARGS:
      endArgs();
      break;
    case Parse::TPTP::State::FORMULA_INFIX:
      formulaInfix();
      break;
    case Parse::TPTP::State::END_EQ:
      endEquality();
      break;
    case Parse::TPTP::State::MID_EQ:
      midEquality();
      break;
    case Parse::TPTP::State::VAR_LIST:
      varList();
      break;
    case Parse::TPTP::State::TAG:
      tag();
      break;
    case Parse::TPTP::State::END_FOF:
      endFof();
      break;
    case Parse::TPTP::State::SIMPLE_FORMULA:
      simpleFormula();
      break;
    case Parse::TPTP::State::END_FORMULA:
      endFormula();
      break;
    case Parse::TPTP::State::FORMULA_INSIDE_TERM:
      formulaInsideTerm();
      break;
    case Parse::TPTP::State::END_FORMULA_INSIDE_TERM:
      endFormulaInsideTerm();
      break;
    case Parse::TPTP::State::END_TERM_AS_FORMULA:
      endTermAsFormula();
      break;
    case Parse::TPTP::State::INCLUDE:
      include();
      break;
    case Parse::TPTP::State::TYPE:
      type();
      break;
    case Parse::TPTP::State::SIMPLE_TYPE:
      simpleType();
      break;
    case Parse::TPTP::State::END_TYPE:
      endType();
      break;
    case Parse::TPTP::State::END_TFF:
      endTff();
      break;
    case Parse::TPTP::State::UNBIND_VARIABLES:
      unbindVariables();
      break;
    case Parse::TPTP::State::VAMPIRE:
      vampire();
      break;
    case Parse::TPTP::State::END_ITE:
      endIte();
      break;
    case Parse::TPTP::State::LET_TYPE:
      letType();
      break;
    case Parse::TPTP::State::END_LET_TYPES:
      endLetTypes();
      break;
    case Parse::TPTP::State::DEFINITION:
      definition();
      break;
    case Parse::TPTP::State::MID_DEFINITION:
      midDefinition();
      break;
    case Parse::TPTP::State::END_DEFINITION:
      endDefinition();
      break;
    case Parse::TPTP::State::SYMBOL_DEFINITION:
      symbolDefinition();
      break;
    case Parse::TPTP::State::TUPLE_DEFINITION:
      if(!env.options->newCNF()){ USER_ERROR("Set --newcnf on if using tuples"); }
      tupleDefinition();
      break;
    case Parse::TPTP::State::END_LET:
      endLet();
      break;
    case Parse::TPTP::State::END_THEORY_FUNCTION:
      endTheoryFunction();
      break;
    case Parse::TPTP::State::END_TUPLE:
      if(!env.options->newCNF()){ USER_ERROR("Set --newcnf on if using tuples"); }
      endTuple();
      break;
    default:
#if VDEBUG
      throw ParseErrorException(((vstring)"Don't know how to process state ")+toString(s),_lineNumber);
#else
      throw ParseErrorException("Don't know how to process state ",_lineNumber);
#endif
    }
#ifdef DEBUG_SHOW_STATE
    cout << "----------------------------------------" << endl;
    printStacks();
    cout << "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~" << endl << endl;
#endif
  }
} // TPTP::parse()

/**
 * Return either the content or the string for this token
 * @since 11/04/2011 Manchester
 */
vstring TPTP::Token::toString() const
{
  vstring str = TPTP::toString(tag);
  return str == "" ? content : str;
} // Token::toString

/**
 * Return the string representation of this tag or "" is the representation
 * is not fixed (e.g. for T_NAME)
 * @since 11/04/2011 Manchester
 */
vstring TPTP::toString(Tag tag)
{
  switch (tag) {
  case Parse::TPTP::Tag::T_EOF:
    return "<eof>";
  case Parse::TPTP::Tag::T_LPAR:
    return "(";
  case Parse::TPTP::Tag::T_RPAR:
    return ")";
  case Parse::TPTP::Tag::T_LBRA:
    return "[";
  case Parse::TPTP::Tag::T_RBRA:
    return "]";
  case Parse::TPTP::Tag::T_COMMA:
    return ",";
  case Parse::TPTP::Tag::T_COLON:
    return ":";
  case Parse::TPTP::Tag::T_NOT:
    return "~";
  case Parse::TPTP::Tag::T_AND:
    return "&";
  case Parse::TPTP::Tag::T_EQUAL:
    return "=";
  case Parse::TPTP::Tag::T_NEQ:
    return "!=";
  case Parse::TPTP::Tag::T_FORALL:
    return "!";
  case Parse::TPTP::Tag::T_EXISTS:
    return "?";
  case Parse::TPTP::Tag::T_PI:
    return "??";
  case Parse::TPTP::Tag::T_SIGMA:
    return "!!";
  case Parse::TPTP::Tag::T_IMPLY:
    return "=>";
  case Parse::TPTP::Tag::T_XOR:
    return "<~>";
  case Parse::TPTP::Tag::T_IFF:
    return "<=>";
  case Parse::TPTP::Tag::T_REVERSE_IMP:
    return "<=";
  case Parse::TPTP::Tag::T_DOT:
    return ".";
  case Parse::TPTP::Tag::T_OR:
    return "|";
  case Parse::TPTP::Tag::T_ASS:
    return ":=";
  case Parse::TPTP::Tag:: T_LAMBDA:
    return "^";
  case Parse::TPTP::Tag:: T_APP:
    return "@";
  case Parse::TPTP::Tag:: T_STAR:
    return "*";
  case Parse::TPTP::Tag:: T_UNION:
    return "+";
  case Parse::TPTP::Tag:: T_ARROW:
    return ">";
  case Parse::TPTP::Tag:: T_SUBTYPE:
    return "<<";
  case Parse::TPTP::Tag:: T_NOT_OR:
    return "~|";
  case Parse::TPTP::Tag:: T_NOT_AND:
    return "~&";
  case Parse::TPTP::Tag:: T_SEQUENT:
    return "-->";
  case Parse::TPTP::Tag:: T_THF_QUANT_ALL:
    return "!>";
  case Parse::TPTP::Tag:: T_THF_QUANT_SOME:
    return "?*";
  case Parse::TPTP::Tag:: T_APP_PLUS:
    return "@+";
  case Parse::TPTP::Tag:: T_APP_MINUS:
    return "@-";
  case Parse::TPTP::Tag:: T_TRUE:
    return "$true";
  case Parse::TPTP::Tag:: T_FALSE:
    return "$false";
  case Parse::TPTP::Tag:: T_TTYPE:
    return "$tType";
  case Parse::TPTP::Tag:: T_BOOL_TYPE:
    return "$o";
  case Parse::TPTP::Tag:: T_DEFAULT_TYPE:
    return "$i";
  case Parse::TPTP::Tag:: T_RATIONAL_TYPE:
    return "$rat";
  case Parse::TPTP::Tag:: T_REAL_TYPE:
    return "$real";
  case Parse::TPTP::Tag:: T_INTEGER_TYPE:
    return "$int";
  case Parse::TPTP::Tag:: T_TUPLE:
    return "$tuple";
  case Parse::TPTP::Tag:: T_THEORY_SORT:
    return "";
  case Parse::TPTP::Tag:: T_THEORY_FUNCTION:
    return "";
  case Parse::TPTP::Tag:: T_FOT:
    return "$fot";
  case Parse::TPTP::Tag:: T_FOF:
    return "$fof";
  case Parse::TPTP::Tag:: T_TFF:
    return "$tff";
  case Parse::TPTP::Tag:: T_THF:
    return "$thf";
  case Parse::TPTP::Tag:: T_ITE:
    return "$ite";
  case Parse::TPTP::Tag:: T_LET:
    return "$let";
  case Parse::TPTP::Tag:: T_NAME:
  case Parse::TPTP::Tag:: T_REAL:
  case Parse::TPTP::Tag:: T_RAT:
  case Parse::TPTP::Tag:: T_INT:
  case Parse::TPTP::Tag:: T_VAR:
  case Parse::TPTP::Tag:: T_DOLLARS:
  case Parse::TPTP::Tag:: T_STRING:
    return "";
#if VDEBUG
  default:
    ASS(false);
#endif
  }
} // toString(Tag)

/**
 * Read all tokens one by one
 * @since 08/04/2011 Manchester
 */
bool TPTP::readToken(Token& tok)
{
  CALL("TPTP::readToken");

  skipWhiteSpacesAndComments();
  tok.start = _gpos;
  switch (getChar(0)) {
  case 0:
    tok.tag = Tag::T_EOF;
    return false;
  case 'a':
  case 'b':
  case 'c':
  case 'd':
  case 'e':
  case 'f':
  case 'g':
  case 'h':
  case 'i':
  case 'j':
  case 'k':
  case 'l':
  case 'm':
  case 'n':
  case 'o':
  case 'p':
  case 'q':
  case 'r':
  case 's':
  case 't':
  case 'u':
  case 'v':
  case 'w':
  case 'x':
  case 'y':
  case 'z':
    tok.tag = Tag::T_NAME;
    readName(tok);
    return true;
  case '$':
    readReserved(tok);
    return true;
  case 'A':
  case 'B':
  case 'C':
  case 'D':
  case 'E':
  case 'F':
  case 'G':
  case 'H':
  case 'I':
  case 'J':
  case 'K':
  case 'L':
  case 'M':
  case 'N':
  case 'O':
  case 'P':
  case 'Q':
  case 'R':
  case 'S':
  case 'T':
  case 'U':
  case 'V':
  case 'W':
  case 'X':
  case 'Y':
  case 'Z':
  case '_':
    tok.tag = Tag::T_VAR;
    readName(tok);
    return true;
  case '0':
  case '1':
  case '2':
  case '3':
  case '4':
  case '5':
  case '6':
  case '7':
  case '8':
  case '9':
    tok.tag = readNumber(tok);
    return true;
  case '"':
    tok.tag = Tag::T_STRING;
    readString(tok);
    return true;
  case '\'':
    tok.tag = Tag::T_NAME;
    readAtom(tok);
    return true;
  case '(':
    tok.tag = Tag::T_LPAR;
    resetChars();
    return true;
  case ')':
    tok.tag = Tag::T_RPAR;
    resetChars();
    return true;
  case '[':
    tok.tag = Tag::T_LBRA;
    resetChars();
    return true;
  case ']':
    tok.tag = Tag::T_RBRA;
    resetChars();
    return true;
  case ',':
    tok.tag = Tag::T_COMMA;
    resetChars();
    return true;
  case ':':
    if (getChar(1) == '=') {
      tok.tag = Tag::T_ASS;
      resetChars();
      return true;
    }
    tok.tag = Tag::T_COLON;
    shiftChars(1);
    return true;
  case '~':
    if (getChar(1) == '&') {
      tok.tag = Tag::T_NOT_AND;
      resetChars();
      return true;
    }
    if (getChar(1) == '|') {
      tok.tag = Tag::T_NOT_OR;
      resetChars();
      return true;
    }
    tok.tag = Tag::T_NOT;
    shiftChars(1);
    return true;
  case '=':
    if (getChar(1) == '>') {
      tok.tag = Tag::T_IMPLY;
      resetChars();
      return true;
    }
    tok.tag = Tag::T_EQUAL;
    shiftChars(1);
    return true;
  case '&':
    tok.tag = Tag::T_AND;
    resetChars();
    return true;
  case '^':
    tok.tag = Tag::T_LAMBDA;
    resetChars();
    return true;
  case '@':
    if (getChar(1) == '+') {
      tok.tag = Tag::T_APP_PLUS;
      resetChars();
      return true;
    }
    if (getChar(1) == '-') {
      tok.tag = Tag::T_APP_MINUS;
      resetChars();
      return true;
    }
    tok.tag = Tag::T_APP;
    shiftChars(1);
    return true;
  case '*':
    tok.tag = Tag::T_STAR;
    resetChars();
    return true;
  case '>':
    tok.tag = Tag::T_ARROW;
    resetChars();
    return true;
  case '!':
    if (getChar(1) == '=') {
      tok.tag = Tag::T_NEQ;
      resetChars();
      return true;
    }
    if (getChar(1) == '>') {
      tok.tag = Tag::T_THF_QUANT_ALL;
      resetChars();
      return true;
    }
    if (getChar(1) == '!') {
      tok.tag = Tag::T_SIGMA;
      resetChars();
      return true;
    }
    tok.tag = Tag::T_FORALL;
    shiftChars(1);
    return true;
  case '?':
    if (getChar(1) == '?') {
      tok.tag = Tag::T_PI;
      resetChars();
      return true;
    }
    if (getChar(1) == '*') {
      tok.tag = Tag::T_THF_QUANT_SOME;
      resetChars();
      return true;
    }
    tok.tag = Tag::T_EXISTS;
    shiftChars(1);
    return true;
  case '<':
    if (getChar(1) == '<') {
      tok.tag = Tag::T_SUBTYPE;
      resetChars();
      return true;
    }
    if (getChar(1) == '~' && getChar(2) == '>') {
      tok.tag = Tag::T_XOR;
      resetChars();
      return true;
    }
    if (getChar(1) != '=') {
      PARSE_ERROR("unrecognized symbol",_gpos);
    }
    if (getChar(2) == '>') {
      tok.tag = Tag::T_IFF;
      resetChars();
      return true;
    }
    tok.tag = Tag::T_REVERSE_IMP;
    shiftChars(2);
    return true;
  case '.':
    tok.tag = Tag::T_DOT;
    resetChars();
    return true;
  case '|':
    tok.tag = Tag::T_OR;
    resetChars();
    return true;
  case '-':
    if (getChar(1) == '-' && getChar(2) == '>') {
      tok.tag = Tag::T_SEQUENT;
      resetChars();
      return true;
    }
    tok.tag = readNumber(tok);
    return true;
  case '+':
    if (getChar(1) < '0' || getChar(1) > '9') {
      tok.tag = Tag::T_UNION;
      shiftChars(1);
      return true;
    }
    tok.tag = readNumber(tok);
    return true;
  default:
    PARSE_ERROR("Bad character",_gpos);
  }
} // TPTP::readToken()

/**
 * Skip all white spaces and comments in the input file
 * @since 08/04/2011 Manchester
 */
void TPTP::skipWhiteSpacesAndComments()
{
  CALL("TPTP::skipWhiteSpacesAndComments");

  for (;;) {
    switch (getChar(0)) {
    case 0: // end-of-file
      return;

    case '\n':
    case '\r':
      _lineNumber++;
    case ' ':
    case '\t':
    case '\f':
      resetChars();
      break;

    case '%': // end-of-line comment
    resetChars();
    for (;;) {
      int c = getChar(0);
      if (c == 0) {
	return;
      }
      resetChars();
      if (c == '\n') {
        _lineNumber++;
	break;
      }
    }
    break;

    case '/': // potential comment
      if (getChar(1) != '*') {
	return;
      }
      resetChars();
      // search for the end of this comment
      for (;;) {
	int c = getChar(0);
        if( c == '\n' || c == '\r'){ _lineNumber++; }
	if (!c) {
	  return;
	}
	resetChars();
	if (c != '*') {
	  continue;
	}
	// c == '*'
	c = getChar(0);
	resetChars();
	if (c != '/') {
	  continue;
	}
	break;
      }
      break;

    // skip to the end of comment
    default:
      return;
    }
  }
} // TPTP::skipWhiteSpacesAndComments

/**
 * Read the name
 * @since 08/04/2011 Manchester
 */
void TPTP::readName(Token& tok)
{
  CALL("TPTP::readName");
  for (int n = 1;;n++) {
    switch (getChar(n)) {
    case 'A':
    case 'B':
    case 'C':
    case 'D':
    case 'E':
    case 'F':
    case 'G':
    case 'H':
    case 'I':
    case 'J':
    case 'K':
    case 'L':
    case 'M':
    case 'N':
    case 'O':
    case 'P':
    case 'Q':
    case 'R':
    case 'S':
    case 'T':
    case 'U':
    case 'V':
    case 'W':
    case 'X':
    case 'Y':
    case 'Z':
    case '_':
    case 'a':
    case 'b':
    case 'c':
    case 'd':
    case 'e':
    case 'f':
    case 'g':
    case 'h':
    case 'i':
    case 'j':
    case 'k':
    case 'l':
    case 'm':
    case 'n':
    case 'o':
    case 'p':
    case 'q':
    case 'r':
    case 's':
    case 't':
    case 'u':
    case 'v':
    case 'w':
    case 'x':
    case 'y':
    case 'z':
    case '$':
    case '0':
    case '1':
    case '2':
    case '3':
    case '4':
    case '5':
    case '6':
    case '7':
    case '8':
    case '9':
      break;
    default:
      ASS(_chars.content()[0] != '$');
      tok.content.assign(_chars.content(),n);
      shiftChars(n);
      return;
    }
  }
} // readName

/**
 * Read a reserved name (starting with a $)
 * @since 10/07/2011 Manchester
 */
void TPTP::readReserved(Token& tok)
{
  CALL("TPTP::readReserved");

  int n = 1;
  for (;;n++) {
    switch (getChar(n)) {
    case 'A':
    case 'B':
    case 'C':
    case 'D':
    case 'E':
    case 'F':
    case 'G':
    case 'H':
    case 'I':
    case 'J':
    case 'K':
    case 'L':
    case 'M':
    case 'N':
    case 'O':
    case 'P':
    case 'Q':
    case 'R':
    case 'S':
    case 'T':
    case 'U':
    case 'V':
    case 'W':
    case 'X':
    case 'Y':
    case 'Z':
    case '_':
    case 'a':
    case 'b':
    case 'c':
    case 'd':
    case 'e':
    case 'f':
    case 'g':
    case 'h':
    case 'i':
    case 'j':
    case 'k':
    case 'l':
    case 'm':
    case 'n':
    case 'o':
    case 'p':
    case 'q':
    case 'r':
    case 's':
    case 't':
    case 'u':
    case 'v':
    case 'w':
    case 'x':
    case 'y':
    case 'z':
    case '$':
    case '0':
    case '1':
    case '2':
    case '3':
    case '4':
    case '5':
    case '6':
    case '7':
    case '8':
    case '9':
      break;
    default:
      tok.content.assign(_chars.content(),n);
      //shiftChars(n);
      goto out;
    }
  }
 out:
  if (tok.content == "$true") {
    tok.tag = Tag::T_TRUE;
  }
  else if (tok.content == "$false") {
    tok.tag = Tag::T_FALSE;
  }
  else if (tok.content == "$ite_f" || tok.content == "$ite_t" || tok.content == "$ite") {
    tok.tag = Tag::T_ITE;
    // $ite_t and $ite_f are left for compatibility, $ite is a generalisation of them
    tok.content = "$ite";
  }
  else if (tok.content == "$let_tt" || tok.content == "$let_tf" || tok.content == "$let_ft" || tok.content == "$let_ff" || tok.content == "$let") {
    tok.tag = Tag::T_LET;
    // all tokens of the form $let_XY are left for compatibility, $let is a generalisation of them
    tok.content = "$let";
  }
  else if (tok.content == "$tType") {
    tok.tag = Tag::T_TTYPE;
  }
  else if (tok.content == "$o" || tok.content == "$oType") {
    tok.tag = Tag::T_BOOL_TYPE;
  }
  else if (tok.content == "$i" || tok.content == "$iType") {
    tok.tag = Tag::T_DEFAULT_TYPE;
  }
  else if (tok.content == "$int") {
    tok.tag = Tag::T_INTEGER_TYPE;
  }
  else if (tok.content == "$rat") {
    tok.tag = Tag::T_RATIONAL_TYPE;
  }
  else if (tok.content == "$real") {
    tok.tag = Tag::T_REAL_TYPE;
  }
  else if (tok.content == "$tuple") {
      tok.tag = Tag::T_TUPLE;
  }
  else if (isTheoryFunction(tok.content)) {
    tok.tag = Tag::T_THEORY_FUNCTION;
  }
  else if (isTheorySort(tok.content)) {
    tok.tag = Tag::T_THEORY_SORT;
  }
  else if (tok.content == "$fot") {
    tok.tag = Tag::T_FOT;
  }
  else if (tok.content == "$fof") {
    tok.tag = Tag::T_FOF;
  }
  else if (tok.content == "$tff") {
    tok.tag = Tag::T_TFF;
  }
  else if (tok.content == "$thf") {
    tok.tag = Tag::T_THF;
  }
  else if (tok.content.substr(0,2) == "$$" && !_filterReserved) {
      tok.tag = Tag::T_DOLLARS;
  }
  else {
      
      // If _filterReserved is on then filter "$" from content
      if(_filterReserved){
          unsigned c=0;
          for(;;c++){ if(getChar(c)!='$') break;}
          shiftChars(c);
          n=n-c;
          tok.content.assign(_chars.content(),n);
      }
      
      tok.tag = Tag::T_NAME;
  }
  // Moved from above so that _filterReserved works
  shiftChars(n);
} // readReserved

/**
 * Read a string
 * @since 08/04/2011 Manchester
 */
void TPTP::readString(Token& tok)
{
  CALL("TPTP::readString");
  for (int n = 1;;n++) {
    int c = getChar(n);
    if (!c) {
      PARSE_ERROR("non-terminated string",_gpos);
    }
    if (c == '\\') { // escape
      c = getChar(++n);
      if (!c) {
	PARSE_ERROR("non-terminated string",_gpos);
      }
      continue;
    }
    if (c == '"') {
      tok.content.assign(_chars.content()+1,n-1);
      resetChars();
      return;
    }
  }
} // readString

/**
 * Read a quoted atom
 * @since 08/04/2011 Manchester
 */
void TPTP::readAtom(Token& tok)
{
  CALL("TPTP::readAtom");

  for (int n = 1;;n++) {
    int c = getChar(n);
    if (!c) {
      PARSE_ERROR("non-terminated quoted atom",_gpos);
    }
    if (c == '\\') { // escape
      c = getChar(++n);
      if (!c) {
	PARSE_ERROR("non-terminated quoted atom",_gpos);
      }
      continue;
    }
    if (c == '\'') {
      tok.content.assign(_chars.content()+1,n-1);
      resetChars();
      return;
    }
  }
} // readAtom

TPTP::ParseErrorException::ParseErrorException(vstring message,int pos, unsigned ln) : _ln(ln)
{
  _message = message + " at position " + Int::toString(pos);
} // TPTP::ParseErrorException::ParseErrorException

TPTP::ParseErrorException::ParseErrorException(vstring message,Token& tok, unsigned ln) : _ln(ln)
{
  _message = message + " at position " + Int::toString(tok.start) + " (text: " + tok.toString() + ')'; 
} // TPTP::ParseErrorException::ParseErrorException

/**
 * Exception printing a message. Currently computing a position is simplified
 * @since 08/04/2011 Manchester
 */
void TPTP::ParseErrorException::cry(ostream& str)
{
  str << "Parsing Error on line " << _ln << "\n";
  str << _message << "\n";
}

/**
 * Read a number
 * @since 08/04/2011 Manchester
 */
TPTP::Tag TPTP::readNumber(Token& tok)
{
  CALL("TPTP::readNumber");

  // skip the sign
  int c = getChar(0);
  ASS(c);
  int pos = decimal((c == '+' || c == '-') ? 1 : 0);
  switch (getChar(pos)) {
  case '/':
    pos = positiveDecimal(pos+1);
    tok.content.assign(_chars.content(),pos);
    shiftChars(pos);
    return Tag::T_RAT;
  case 'E':
  case 'e':
    {
      char c = getChar(pos+1);
      pos = decimal((c == '+' || c == '-') ? pos+2 : pos+1);
      tok.content.assign(_chars.content(),pos);
      shiftChars(pos);
    }
    return Tag::T_REAL;
  case '.':
    {
      int p = pos;
      do {
        c = getChar(++pos);
      }
      while (c >= '0' && c <= '9');
      if (pos == p+1) {
        // something like 12.
        PARSE_ERROR("wrong number format",_gpos);
      }
      c = getChar(pos);
      if (c == 'e' || c == 'E') {
	c = getChar(pos+1);
	pos = decimal((c == '+' || c == '-') ? pos+2 : pos+1);
      }
      tok.content.assign(_chars.content(),pos);
      shiftChars(pos);
    }
    return Tag::T_REAL;
  default:
    tok.content.assign(_chars.content(),pos);
    shiftChars(pos);
    return Tag::T_INT;
  }
} // readNumber

/**
 * Read a decimal starting at position pos (see the TPTP grammar),
 * return the position after the last character in the decimal.
 * @since 08/04/2011 Manchester
 */
int TPTP::decimal(int pos)
{
  CALL("TPTP::decimal");

  switch (getChar(pos)) {
  case '0':
    return pos+1;
  case '1':
  case '2':
  case '3':
  case '4':
  case '5':
  case '6':
  case '7':
  case '8':
  case '9':
    break;
  default:
    ASSERTION_VIOLATION_REP(getChar(pos));
    PARSE_ERROR("wrong number format",_gpos);
  }

  int c;
  do {
    c = getChar(++pos);
  }
  while (c >= '0' && c <= '9');
  return pos;
} // decimal

/**
 * Read a positive decimal starting at position pos (see the TPTP grammar),
 * return the position after the last character in the decimal.
 * @since 08/04/2011 Manchester
 */
int TPTP::positiveDecimal(int pos)
{
  CALL("TPTP::positiveDecimal");

  switch (getChar(pos)) {
  case '1':
  case '2':
  case '3':
  case '4':
  case '5':
  case '6':
  case '7':
  case '8':
  case '9':
    break;
  default:
    PARSE_ERROR("wrong number format",_gpos);
  }

  int c;
  do {
    c = getChar(++pos);
  }
  while (c >= '0' && c <= '9');
  return pos;
} // positiveDecimal

/**
 * Process unit list declaration. If end of file is reached, terminates. Otherwise,
 * pushes on the state state UNIT_LIST and one of CNF, FOF, VAMPIRE
 * @since 10/04/2011 Manchester
 */
void TPTP::unitList()
{
  CALL("TPTP::unitList");
  if (env.timeLimitReached()) {
    // empty states to avoid infinite loop
    while (!_states.isEmpty()) {
      _states.pop();
    }
    return;
  }

  Token& tok = getTok(0);
  if (tok.tag == Tag::T_EOF) {
    resetToks();
    if (_inputs.isEmpty()) {
      return;
    }
    resetChars();
    {
      BYPASSING_ALLOCATOR; // ifstream was allocated by "system new"
      delete _in;
    }
    _in = _inputs.pop();
    _includeDirectory = _includeDirectories.pop();
    delete _allowedNames;
    _allowedNames = _allowedNamesStack.pop();
    _states.push(State::UNIT_LIST);
    return;
  }
  if (tok.tag != Tag::T_NAME) {
    PARSE_ERROR("cnf(), fof(), vampire() or include() expected",tok);
  }
  vstring name(tok.content);
  _states.push(State::UNIT_LIST);
  if (name == "cnf") {
    _states.push(State::CNF);
    resetToks();
    return;
  }
  if (name == "fof") {
      _states.push(State::FOF);
    resetToks();
    return;
  }
  if (name == "tff") {
    _states.push(State::TFF);
    resetToks();
    return;
  }
  if (name == "thf") {
    _states.push(State::THF);
    resetToks();
    return;
  }
  if (name == "vampire") {
    _states.push(State::VAMPIRE);
    resetToks();
    return;
  }
  if (name == "include") {
    _states.push(State::INCLUDE);
    resetToks();
    return;
  }
  PARSE_ERROR("cnf(), fof(), vampire() or include() expected",tok);
}

/**
 * Process fof() or cnf() declaration. Does the following:
 * <ol>
 *  <li>add 0 to _formulas</li>
 *  <li>save the input type to _lastInputType</li>
 *  <li>add unit name to _strings</li>
 *  <li>add to _states END_FOF,FORMULA</li>
 *  <li>adds to _bools true, if fof and false, if cnf</li>
 * </ol>
 * @since 10/04/2011 Manchester
 */
void TPTP::fof(bool fo)
{
  CALL("TPTP::fof");

  _bools.push(fo);
  consumeToken(Tag::T_LPAR);
  // save the name of this unit
  Token& tok = getTok(0);
  switch(tok.tag) {
  case Tag::T_NAME:
    _strings.push(tok.content);
    resetToks();
    break;
  case Tag::T_INT:
    _strings.push(tok.content);
    resetToks();
    break;
  default:
    PARSE_ERROR("Unit name expected",tok);
  }

  consumeToken(Tag::T_COMMA);
  tok = getTok(0);
  int start = tok.start;
  vstring tp = name();

  _isQuestion = false;
  if(_modelDefinition){
    _lastInputType = UnitInputType::MODEL_DEFINITION;
  }
  else if (tp == "axiom" || tp == "plain") {
    _lastInputType = UnitInputType::AXIOM;
  }
  else if(tp == "extensionality"){
    // this will be transformed to just AXIOM after clausification
    _lastInputType = UnitInputType::EXTENSIONALITY_AXIOM;
  }
  else if (tp == "definition") {
    _lastInputType = UnitInputType::AXIOM;
  }
  else if (tp == "conjecture") {
    _containsConjecture = true;
    _lastInputType = UnitInputType::CONJECTURE;
  }
  else if (tp == "question") {
    _isQuestion = true;
    _containsConjecture = true;
    _lastInputType = UnitInputType::CONJECTURE;
  }
  else if (tp == "negated_conjecture") {
    _lastInputType = UnitInputType::NEGATED_CONJECTURE;
  }
  else if (tp == "hypothesis" || tp == "theorem" || tp == "lemma") {
    _lastInputType = UnitInputType::ASSUMPTION;
  }
  else if (tp == "claim") {
    _lastInputType = UnitInputType::CLAIM;
  }
  else if (tp == "assumption" || tp == "unknown") {
    // MS: we were silently dropping these until now. I wonder why...
    PARSE_ERROR((vstring)"Unsupported unit type '" + tp + "' found",start);
  }
  else {
    PARSE_ERROR((vstring)"unit type, such as axiom or definition expected but " + tp + " found",
		    start);
  }
  consumeToken(Tag::T_COMMA);
  _states.push(State::END_FOF);
  _states.push(State::FORMULA);
} // fof()

/**
 * Process fof() or cnf() declaration. Does the following:
 * <ol>
 *  <li>add 0 to _formulas</li>
 *  <li>save the input type to _lastInputType</li>
 *  <li>add unit name to _strings</li>
 *  <li>add to _states END_FOF,FORMULA</li>
 *  <li>adds to _bools true, if fof and false, if cnf</li>
 * </ol>
 * @since 10/04/2011 Manchester
 * @author Andrei Voronkov
 */
void TPTP::tff()
{
  CALL("TPTP::tff");

  consumeToken(Tag::T_LPAR);
  // save the name of this unit
  Token& tok = getTok(0);
  switch(tok.tag) {
  case Tag::T_NAME:
  case Tag::T_INT:
    _strings.push(tok.content);
    resetToks();
    break;
  default:
    PARSE_ERROR("Unit name expected",tok);
  }

  consumeToken(Tag::T_COMMA);
  tok = getTok(0);
  int start = tok.start;
  vstring tp = name();
  if (tp == "type") {
    // Read a TPTP type declaration. These declarations are ambiguous: they can
    // either be new type declarations, as in tff(1,type,(t: $ttype)) or sort
    // declarations: tff(2,type,(c:t)). What exactly they represent will be known
    // when $ttype is expected.
    consumeToken(Tag::T_COMMA);
    // TPTP syntax allows for an arbitrary number of parentheses around a type
    // declaration
    int lpars = 0;
    for (;;) {
      tok = getTok(0);
      if (tok.tag != Tag::T_LPAR) {
	break;
      }
      lpars++;
      resetToks();
    }
    vstring nm = name();
    consumeToken(Tag::T_COLON);
    tok = getTok(0);
    if (tok.tag == Tag::T_TTYPE) {
      // now we know that this is a new type declaration
      bool added;
      env.sorts->addSort(nm,added,false);
      // GR: Multiple identical type declarations for a symbol are allowed
      //if (!added) {
      //  PARSE_ERROR("Sort name must be unique",tok);
      //}
      resetToks();
      while (lpars--) {
	consumeToken(Tag::T_RPAR);
      }
      consumeToken(Tag::T_RPAR);
      consumeToken(Tag::T_DOT);
      return;
    }
    // the matching number of rpars will be read
    _ints.push(lpars);
    // remember type name
    _strings.push(nm);
    _states.push(Parse::TPTP::State::END_TFF);
    _states.push(Parse::TPTP::State::TYPE);
    return;
  }

  _bools.push(true); // to denote that it is an FOF formula
  _isQuestion = false;
  if (tp == "axiom" || tp == "plain") {
    _lastInputType = UnitInputType::AXIOM;
  }
  else if (tp == "extensionality"){
    // this will be transformed to just AXIOM after clausification
    _lastInputType = UnitInputType::EXTENSIONALITY_AXIOM;
  }
  else if (tp == "definition") {
    _lastInputType = UnitInputType::AXIOM;
  }
  else if (tp == "conjecture") {
    _containsConjecture = true;
    _lastInputType = UnitInputType::CONJECTURE;
  }
  else if (tp == "question") {
    _isQuestion = true;
    _containsConjecture = true;
    _lastInputType = UnitInputType::CONJECTURE;
  }
  else if (tp == "negated_conjecture") {
    _lastInputType = UnitInputType::NEGATED_CONJECTURE;
  }
  else if (tp == "hypothesis" || tp == "theorem" || tp == "lemma") {
    _lastInputType = UnitInputType::ASSUMPTION;
  }
  else if (tp == "assumption" || tp == "unknown") {
    // MS: we were silently dropping these until now. I wonder why...
    PARSE_ERROR((vstring)"Unsupported unit type '" + tp + "' found",start);
  }
  else if (tp == "claim") {
    _lastInputType = UnitInputType::CLAIM;
  }
  else {
    PARSE_ERROR((vstring)"unit type, such as axiom or definition expected but " + tp + " found",
		    start);
  }
  consumeToken(Tag::T_COMMA);
  _states.push(State::END_FOF);
  _states.push(State::FORMULA);
} // tff()

/**
 * Process the end of the $ite expression
 * @since 27/07/2011 Manchester
 * @since 16/04/2015 Gothenburg, major changes to support FOOL
 */
void TPTP::endIte()
{
  CALL("TPTP::endIte");

  TermList elseBranch = _termLists.pop();
  TermList thenBranch = _termLists.pop();
  Formula* condition = _formulas.pop();
  unsigned thenSort = sortOf(thenBranch);
  TermList ts(Term::createITE(condition,thenBranch,elseBranch,thenSort));
  unsigned elseSort = sortOf(elseBranch);
  if (thenSort != elseSort) {
    USER_ERROR("sort mismatch in the if-then-else expression: " +
               thenBranch.toString() + " has the sort " + env.sorts->sortName(thenSort) + ", whereas " +
               elseBranch.toString() + " has the sort " + env.sorts->sortName(elseSort));
  }
  _termLists.push(ts);
} // endIte

/**
 *
 */
void TPTP::endTheoryFunction() {
  CALL("TPTP::endTheoryFunction");

  /**
   * Things get a bit awkward with theories + FOOL, because theory function can
   * return $o in such case be a predicate symbol rather than a function symbol.
   * The current solution is the following -- we always treat application of
   * theory functions as a a term (a formula wrapped inside boolean term, if
   * needed). If later on we discover that we should've taken it as a formula,
   * we simply pull the formula out of the boolean term. This is done in
   * endTermAsFormula().
   */

  Theory::Interpretation itp;
  TermList args[3]; // all theory function use up to 3 arguments as for now
  unsigned arraySort;

  TheoryFunction tf = _theoryFunctions.pop();
  switch (tf) {
  case TheoryFunction::TF_SELECT: {
      TermList index = _termLists.pop();
      TermList array = _termLists.pop();

      arraySort = sortOf(array);
      if (!env.sorts->isOfStructuredSort(arraySort, Sorts::StructuredSort::ARRAY)) {
        USER_ERROR("$select is being incorrectly used on a type of array " + env.sorts->sortName(arraySort) + " that has not be defined");
      }

      unsigned indexSort = env.sorts->getArraySort(arraySort)->getIndexSort();
      if (sortOf(index) != indexSort) {
        USER_ERROR("sort of index is not the same as the index sort of the array");
      }

      args[0] = array;
      args[1] = index;

      if (env.sorts->getArraySort(arraySort)->getInnerSort() == (unsigned)Sorts::DefaultSorts::SRT_BOOL) {
        itp = Theory::Interpretation::ARRAY_BOOL_SELECT;
      } else {
        itp = Theory::Interpretation::ARRAY_SELECT;
      }
      break;
    }
  case TheoryFunction::TF_STORE: {
      TermList value = _termLists.pop();
      TermList index = _termLists.pop();
      TermList array = _termLists.pop();

      arraySort = sortOf(array);
      if (!env.sorts->isOfStructuredSort(arraySort, Sorts::StructuredSort::ARRAY)) {
        USER_ERROR("store is being incorrectly used on a type of array that has not be defined");
      }

      unsigned indexSort = env.sorts->getArraySort(arraySort)->getIndexSort();
      if (sortOf(index) != indexSort) {
        USER_ERROR("sort of index is not the same as the index sort of the array");
      }

      unsigned innerSort = env.sorts->getArraySort(arraySort)->getInnerSort();
      if (sortOf(value) != innerSort) {
        USER_ERROR("sort of value is not the same as the value sort of the array");
      }

      args[0] = array;
      args[1] = index;
      args[2] = value;

      itp = Theory::Interpretation::ARRAY_STORE;

      break;
    }
    default:
      ASSERTION_VIOLATION_REP(tf);
  }

  OperatorType* type = Theory::getArrayOperatorType(arraySort,itp);
  unsigned symbol = env.signature->getInterpretingSymbol(itp, type);
  unsigned arity = Theory::getArity(itp);

  if (Theory::isFunction(itp)) {
    Term* term = Term::create(symbol, arity, args);
    _termLists.push(TermList(term));
  } else {
    Literal* literal = Literal::create(symbol, arity, true, false, args);
    _formulas.push(new AtomicFormula(literal));
    _states.push(State::END_FORMULA_INSIDE_TERM);
  }
} // endTheoryFunction

/**
 * Process include() declaration
 * @since 07/07/2011 Manchester
 */
void TPTP::include()
{
  CALL("TPTP::include");

  consumeToken(Tag::T_LPAR);
  Token& tok = getTok(0);
  if (tok.tag != Tag::T_NAME) {
    PARSE_ERROR((vstring)"file name expected",tok);
  }
  vstring relativeName=tok.content;
  resetToks();
  bool ignore = _forbiddenIncludes.contains(relativeName);
  if (!ignore) {
    _allowedNamesStack.push(_allowedNames);
    _allowedNames = 0;
    _inputs.push(_in);
    _includeDirectories.push(_includeDirectory);
  }

  tok = getTok(0);
  if (tok.tag == Tag::T_COMMA) {
    if (!ignore) {
      _allowedNames = new Set<vstring>;
    }
    resetToks();
    consumeToken(Tag::T_LBRA);
    for(;;) {
      tok = getTok(0);
      if (tok.tag != Tag::T_NAME) {
	PARSE_ERROR((vstring)"formula name expected",tok);
      }
      vstring axName=tok.content;
      resetToks();
      if (!ignore) {
	_allowedNames->insert(axName);
      }
      tok = getTok(0);
      if (tok.tag == Tag::T_RBRA) {
	resetToks();
	break;
      }
      consumeToken(Tag::T_COMMA);
    }
  }
  consumeToken(Tag::T_RPAR);
  consumeToken(Tag::T_DOT);

  if (ignore) {
    return;
  }
  // here should be a computation of the new include directory according to
  // the TPTP standard, so far we just set it to ""
  _includeDirectory = "";
  vstring fileName(env.options->includeFileName(relativeName));
  {
    BYPASSING_ALLOCATOR; // we cannot make ifstream allocated via Allocator
    _in = new ifstream(fileName.c_str());
  }
  if (!*_in) {
    USER_ERROR((vstring)"cannot open file " + fileName);
  }
} // include

/** add a file name to the list of forbidden includes */
void TPTP::addForbiddenInclude(vstring file)
{
  CALL("TPTP::addForbiddenInclude");
  _forbiddenIncludes.insert(file);
}

/**
 * Read the next token that must be a name.
 * @since 10/04/2011 Manchester
 */
vstring TPTP::name()
{
  CALL("TPTP::name");
  Token& tok = getTok(0);
  if (tok.tag != Tag::T_NAME) {
    PARSE_ERROR("name expected",tok);
  }
  vstring nm = tok.content;
  resetToks();
  return nm;
} // name

/**
 * Read the next token that must have a given name.
 * @since 10/04/2011 Manchester
 */
void TPTP::consumeToken(Tag t)
{
  CALL("TPTP::consumeToken");

  Token& tok = getTok(0);
  if (tok.tag != t) {
    vstring expected = toString(t);
    PARSE_ERROR(expected + " expected",tok);
  }
  resetToks();
} // consumeToken

/**
 * Read a formula and save it on the stack of formulas.
 * Adds to _states END_SIMPLE_FORMULA,SIMPLE_FORMULA
 * @since 10/04/2011 Manchester
 */
void TPTP::formula()
{
  CALL("TPTP::formula");

  _connectives.push(-1);
  _states.push(State::END_FORMULA);
  _states.push(State::SIMPLE_FORMULA);
} // formula

/**
 *
 * @since 26/03/2015 Manchester
 */
void TPTP::termInfix()
{
  CALL("TPTP::termInfix");
  Token tok = getTok(0);
  switch (tok.tag) {
    case Tag::T_EQUAL:
    case Tag::T_NEQ:
      _states.push(State::END_FORMULA_INSIDE_TERM);
      _states.push(State::FORMULA_INFIX);
      return;
    case Tag::T_COMMA:
    case Tag::T_RPAR:
    case Tag::T_RBRA:
    case Tag::T_ASS:
      _states.push(State::END_TERM);
      return;
    case Tag::T_AND:
    case Tag::T_NOT_AND:
    case Tag::T_NOT_OR:
    case Tag::T_OR:
    case Tag::T_XOR:
    case Tag::T_IFF:
    case Tag::T_IMPLY:
    case Tag::T_REVERSE_IMP:
      if (_insideEqualityArgument > 0) {
        _states.push(State::END_TERM);
        return;
      }
      _connectives.push(-1);
      _states.push(State::END_FORMULA_INSIDE_TERM);
      _states.push(State::END_FORMULA);
      _states.push(State::FORMULA_INFIX);
      return;
    default:
      PARSE_ERROR("term or formula expected", tok);
  }
} // termInfix

/**
 * Read a TPTP type expression
 * @since 10/04/2011 Manchester
 * @author Andrei Voronkov
 */
void TPTP::type()
{
  CALL("TPTP::type");

  _typeTags.push(TypeTag::TT_ATOMIC);
  _states.push(State::END_TYPE);
  _states.push(State::SIMPLE_TYPE);
} // type

/**
 * Read a function application or a variable and save the resulting literal
 * @since 10/04/2011 Manchester
 */
void TPTP::funApp()
{
  CALL("TPTP::funApp");
  Token tok = getTok(0);
  resetToks();

  if (tok.tag == Tag::T_LBRA) {
    _strings.push(toString(Tag::T_TUPLE));
  } else {
    _strings.push(tok.content);
  }

  switch (tok.tag) {
  case Tag::T_THEORY_FUNCTION:
      consumeToken(Tag::T_LPAR);
      addTagState(Tag::T_RPAR);
      switch (getTheoryFunction(tok)) {
        case Parse::TPTP::TheoryFunction::TF_SELECT:
          _states.push(State::TERM);
          addTagState(Tag::T_COMMA);
          _states.push(State::TERM);
          break;
        case Parse::TPTP::TheoryFunction::TF_STORE:
          _states.push(State::TERM);
          addTagState(Tag::T_COMMA);
          _states.push(State::TERM);
          addTagState(Tag::T_COMMA);
          _states.push(State::TERM);
          break;
        default:
          ASSERTION_VIOLATION_REP(tok.content);
      }
      return;

  case Tag::T_ITE:
      consumeToken(Tag::T_LPAR);
      addTagState(Tag::T_RPAR);
      _states.push(State::TERM);
      addTagState(Tag::T_COMMA);
      _states.push(State::TERM);
      addTagState(Tag::T_COMMA);
      _states.push(State::FORMULA);
      return;

  case Tag::T_LET: {
      consumeToken(Tag::T_LPAR);
      addTagState(Tag::T_RPAR);
      _states.push(State::TERM);
      addTagState(Tag::T_COMMA);
      _states.push(State::DEFINITION);
      _letDefinitions.push(LetDefinitions());
      addTagState(Tag::T_COMMA);

      bool multipleLetTypes = false;
      if (getTok(0).tag == Tag::T_LBRA) {
        resetToks();
        addTagState(Tag::T_RBRA);
        multipleLetTypes = true;
      }
      _bools.push(multipleLetTypes);

      _states.push(State::END_LET_TYPES);
      _states.push(State::LET_TYPE);
      _letTypedSymbols.push(LetSymbols());
      return;
    }

  case Tag::T_LBRA:
      _states.push(State::ARGS);
      _ints.push(1); // the arity of the function symbol is at least 1
      return;

    case Tag::T_VAR:
      _ints.push(-1); // dummy arity to indicate a variable
      return;

    case Tag::T_NAME:
      if (getTok(0).tag == Tag::T_LPAR) {
        resetToks();
        _states.push(State::ARGS);
        _ints.push(1); // the arity of the function symbol is at least 1
      } else {
        _ints.push(0); // arity
      }
      return;

    default:
      PARSE_ERROR("unexpected token", tok);
  }
} // TPTP::funApp

void TPTP::letType()
{
  CALL("TPTP::letType");

  // We cannot use this method in TPTP::tff() because type declarations in the
  // "type" role TFF units allow declarations of types ($tType), which are not
  // allowed inside $lets

  _states.push(State::TYPE);
  addTagState(Tag::T_COLON);
  _strings.push(name());
} // TPTP::letType

void TPTP::endLetTypes()
{
  CALL("TPTP::endLetTypes");

  vstring name = _strings.pop();
  Type* t = _types.pop();
  OperatorType* type = constructOperatorType(t);

  unsigned arity = type->arity();
  bool isPredicate = type->isPredicateType();

  unsigned symbol = isPredicate
                  ? env.signature->addFreshPredicate(arity, name.c_str())
                  : env.signature->addFreshFunction(arity,  name.c_str());

  if (isPredicate) {
    env.signature->getPredicate(symbol)->setType(type);
  } else {
    env.signature->getFunction(symbol)->setType(type);
  }

  LetSymbolName symbolName(name, arity);
  LetSymbolReference symbolReference(symbol, isPredicate);

  LetSymbols scope = _letTypedSymbols.pop();

  if (findLetSymbol(symbolName, scope, symbolReference)) {
    USER_ERROR("The symbol " + name + " of arity " + Int::toString(arity) + " is defined twice in a $let-expression.");
  }

  scope.push(LetSymbol(symbolName, symbolReference));
  _letTypedSymbols.push(scope);

  bool multipleLetTypes = _bools.pop();
  if (multipleLetTypes && getTok(0).tag == Tag::T_COMMA) {
    resetToks();
    _bools.push(multipleLetTypes);
    _states.push(State::END_LET_TYPES);
    _states.push(State::LET_TYPE);
  }
} // TPTP::endLetTypes

void TPTP::definition()
{
  CALL("TPTP::definition");

  // At this point we parse one or more simultaneous definitions.
  // Simultaneous definitions are of the form `[D1, ..., Dn]` and each
  // definition is either of a function/predicate symbol `f(X,Y,Z) := t`
  // or a tuple `[a, b, c] := t`.

  // If the next token is '[', then the definition could either be
  // a single tuple definition or a list of simultaneous definitions.
  // This ambiguity is resolved by the next two tokens:
  // if they are T_NAME and then T_COMMA, then it is a tuple definition,
  // otherwise it is a a simultaneous definition.

  // The challenge here is how to direct the parser while keeping it
  // looking only one token ahead, like in the rest of TPTP.cpp.
  // Essentially, the trick is to
  //   1) have a boolean flag in _bools that tells whether the current let
  //      definition is simultaneous or not;
  //   2) consume the T_NAME token of a symbol definition here and not in
  //      SYMBOL_DEFINITION;
  //   3) consume the sequence T_LBRA, T_NAME, T_COMMA of tokens here and
  //      not in TUPLE_DEFINITION.

  switch (getTok(0).tag) {
    case Tag::T_NAME:
      _bools.push(false); // not a simultaneous definition
      _strings.push(name());
      _states.push(State::SYMBOL_DEFINITION);
      return;

    case Tag::T_LBRA: {
      resetToks();
      switch (getTok(0).tag) {
        case Tag::T_NAME:
          _strings.push(name());
          switch (getTok(0).tag) {
            case Tag::T_ASS:
            case Tag::T_LPAR:
              _bools.push(true); // is a simultaneous definition
              addTagState(Tag::T_RBRA);
              _states.push(State::SYMBOL_DEFINITION);
              return;

            case Tag::T_COMMA:
              resetToks();
              _bools.push(false); // not a simultaneous definition
              _states.push(State::TUPLE_DEFINITION);
              return;

            default:
              PARSE_ERROR(toString(Tag::T_ASS) + " or " + toString(Tag::T_LPAR) + " or " + toString(Tag::T_COMMA) + " expected",
                          getTok(0));
          }
          return;

        case Tag::T_LBRA:
          resetToks();
          _bools.push(true); // is a simultaneous definition
          addTagState(Tag::T_RBRA);
          _states.push(State::TUPLE_DEFINITION);
          return;

        default:
          PARSE_ERROR("name or " + toString(Tag::T_LBRA) + " expected",getTok(0));
      }
    }

    default:
      PARSE_ERROR("name or " + toString(Tag::T_LBRA) + " expected",getTok(0));
  }
} // TPTP::definition

void TPTP::midDefinition()
{
  CALL("TPTP::midDefinition");

  switch (getTok(0).tag) {
    case Tag::T_NAME:
      _strings.push(name());
      _states.push(State::SYMBOL_DEFINITION);
      break;

    case Tag::T_LBRA:
      resetToks();
      _states.push(State::TUPLE_DEFINITION);
      break;

    default:
      PARSE_ERROR("name or " + toString(Tag::T_LBRA) + " expected",getTok(0));
  }
} // TPTP::midDefinition

void TPTP::symbolDefinition()
{
  CALL("TPTP::symbolDefinition");

  vstring nm = _strings.pop();
  unsigned arity = 0;
  Formula::VarList* vs = Formula::VarList::empty();

  Stack<unsigned> vars;
  if (getTok(0).tag == Tag::T_LPAR) {
    resetToks();
    for (;;) {
      if (getTok(0).tag == Tag::T_VAR) {
        int var = _vars.insert(getTok(0).content);
        vars.push(var);
        resetToks();
      } else {
        PARSE_ERROR("variable expected", getTok(0));
      }


      if (getTok(0).tag == Tag::T_COMMA) {
        resetToks();
        continue;
      }

      if (getTok(0).tag == Tag::T_RPAR) {
        resetToks();
        break;
      }

      PARSE_ERROR("comma or closing bracket expected", getTok(0));
    }
    arity = (unsigned)vars.size();
  }

  LetSymbolName name(nm, arity);
  LetSymbolReference ref;
  if (!findLetSymbol(name, _letTypedSymbols.top(), ref)) {
    USER_ERROR("Symbol " + nm + " with arity " + Int::toString(arity) + " is used in a let definition without a declared type");
  }

  unsigned symbol = SYMBOL(ref);
  bool isPredicate = IS_PREDICATE(ref);

  if (arity > 0) {
    OperatorType* type = isPredicate
                       ? env.signature->getPredicate(symbol)->predType()
                       : env.signature->getFunction(symbol)->fnType();

    unsigned index = 0;
    while (vars.isNonEmpty()) {
      int var = vars.pop();
      unsigned sort = type->arg(arity - 1 - index++);
      bindVariable(var, sort);
      vs = new Formula::VarList(var, vs);
    }

    _bindLists.push(vs);
    _states.push(State::UNBIND_VARIABLES);
  }

  LetDefinitions definitions = _letDefinitions.pop();
  definitions.push(LetSymbolReference(symbol, isPredicate));
  _letDefinitions.push(definitions);

  _varLists.push(vs);

  _states.push(State::END_DEFINITION);
  consumeToken(Tag::T_ASS);
  _states.push(State::TERM);
} // TPTP::symbolDefinition

/**
 * Read a non-empty sequence of constants and save the resulting
 * sequence of TermList and their number
 * @since 20/04/2016 Gothenburg
 */
void TPTP::tupleDefinition()
{
  CALL("TPTP::tupleDefinition");

  Set<vstring> uniqueConstants;
  Stack<unsigned> symbols;
  Stack<unsigned> sorts;

  vstring constant = _strings.pop();
  do {
    if (uniqueConstants.contains(constant)) {
      USER_ERROR("The symbol " + constant + " is defined twice in a tuple $let-expression.");
    } else {
      uniqueConstants.insert(constant);
    }

    LetSymbolName constantName(constant, 0);
    LetSymbolReference ref;
    if (!findLetSymbol(constantName, _letTypedSymbols.top(), ref)) {
      USER_ERROR("Constant " + constant + " is used in a tuple let definition without a declared sort");
    }

    unsigned symbol = SYMBOL(ref);
    bool isPredicate = IS_PREDICATE(ref);

    symbols.push(symbol);

    unsigned sort = isPredicate
                  ? (unsigned)Sorts::DefaultSorts::SRT_BOOL
                  : env.signature->getFunction(symbol)->fnType()->result();
    sorts.push(sort);

    if (getTok(0).tag == Tag::T_NAME) {
      constant = name();
      if (getTok(0).tag == Tag::T_COMMA) {
        resetToks();
      }
    } else {
      break;
    }
  } while (true);

  unsigned tupleSort = env.sorts->addTupleSort((unsigned)sorts.length(), sorts.begin());
  unsigned tupleFunctor = Theory::tuples()->getFunctor(tupleSort);

  LetDefinitions definitions = _letDefinitions.pop();
  definitions.push(LetSymbolReference(tupleFunctor, false));
  _letDefinitions.push(definitions);

  IntList* constants = IntList::empty();
  IntList::pushFromIterator(Stack<unsigned>::Iterator(symbols), constants);
  _varLists.push(constants);

  _states.push(State::END_DEFINITION);
  _states.push(State::TERM);
  addTagState(Tag::T_ASS);
  addTagState(Tag::T_RBRA);
} // tupleDefinition

void TPTP::endDefinition() {
  CALL("TPTP::endDefinition");

  LetSymbolReference ref = _letDefinitions.top().top();
  unsigned symbol = SYMBOL(ref);
  bool isPredicate = IS_PREDICATE(ref);

  TermList definition = _termLists.top();
  unsigned definitionSort = sortOf(definition);

  unsigned refSort = isPredicate
                     ? (unsigned)Sorts::DefaultSorts::SRT_BOOL
                     : env.signature->getFunction(symbol)->fnType()->result();

  if (refSort != definitionSort) {
    vstring definitionSortName = env.sorts->sortName(definitionSort);
    vstring refSymbolName = isPredicate
                            ? env.signature->predicateName(symbol)
                            : env.signature->functionName(symbol);
    OperatorType* type = isPredicate
                         ? env.signature->getPredicate(symbol)->predType()
                         : env.signature->getFunction(symbol)->fnType();
    USER_ERROR("The term " + definition.toString() + " of the sort " + definitionSortName +
               " is used as definition of the symbol " + refSymbolName +
               " of the type " + type->toString());
  }

  bool multipleDefinitions = _bools.pop();
  if (multipleDefinitions && getTok(0).tag == Tag::T_COMMA) {
    resetToks();
    _bools.push(multipleDefinitions);
    _states.push(State::MID_DEFINITION);
  } else {
    _letSymbols.push(_letTypedSymbols.pop());
  }
} // endDefinition

bool TPTP::findLetSymbol(LetSymbolName symbolName, LetSymbolReference& symbolReference) {
  CALL("TPTP::findLetSymbol(LetSymbolName,LetSymbolReference)");

  Stack<LetSymbols>::TopFirstIterator scopes(_letSymbols);
  while (scopes.hasNext()) {
    LetSymbols scope = scopes.next();
    if (findLetSymbol(symbolName, scope, symbolReference)) {
      return true;
    }
  }
  return false;
} // findLetSymbol(LetSymbolName,LetSymbolReference)

bool TPTP::findLetSymbol(LetSymbolName symbolName, LetSymbols scope, LetSymbolReference& symbolReference) {
  CALL("TPTP::findLetSymbol(LetSymbolName,LetSymbols,LetSymbolReference)");
  LetSymbols::Iterator symbols(scope);
  while (symbols.hasNext()) {
    LetSymbol symbol = symbols.next();
    if (symbol.first == symbolName) {
      symbolReference = symbol.second;
      return true;
    }
  }
  return false;
} // findLetSymbol(LetSymbolName,LetSymbols,LetSymbolReference)


/**
 * Process the end of the $let expression
 * @since 27/07/2011 Manchester
 */
void TPTP::endLet()
{
  CALL("TPTP::endLet");

  TermList let = _termLists.pop();
  unsigned sort = sortOf(let);

  _letSymbols.pop();
  LetDefinitions scope = _letDefinitions.pop(); // TODO: inlining this crashes the program, WTF?
  LetDefinitions::TopFirstIterator definitions(scope);
  while (definitions.hasNext()) {
    LetSymbolReference ref = definitions.next();
    unsigned symbol = SYMBOL(ref);
    bool isPredicate = IS_PREDICATE(ref);

    Formula::VarList* varList = _varLists.pop();
    TermList definition = _termLists.pop();

    bool isTuple = false;
    if (!isPredicate) {
      unsigned resultSort = env.signature->getFunction(symbol)->fnType()->result();
      isTuple = env.sorts->isOfStructuredSort(resultSort, Sorts::StructuredSort::TUPLE);
    }

    if (isTuple) {
      let = TermList(Term::createTupleLet(symbol, varList, definition, let, sort));
    } else {
      let = TermList(Term::createLet(symbol, varList, definition, let, sort));
    }
  }
  _termLists.push(let);
} // endLet

/**
 * Process the end of the tuple expression
 * @since 19/04/2016 Gothenburg
 */
void TPTP::endTuple()
{
  CALL("TPTP::endTuple");

  unsigned arity = (unsigned)_ints.pop();
  ASS_GE(_termLists.size(), arity);

  DArray<TermList> elements(arity);
  DArray<unsigned> sorts(arity);

  for (int i = arity - 1; i >= 0; i--) {
    TermList ts = _termLists.pop();
    elements[i] = ts;
    sorts[i] = sortOf(ts);
  }

  Term* t = Term::createTuple(arity, sorts.begin(), elements.begin());
  _termLists.push(TermList(t));
} // endTuple

/**
 * Read a non-empty sequence of arguments, including the right parentheses
 * and save the resulting sequence of TermList and their number
 * @since 10/04/2011 Manchester
 */
void TPTP::args()
{
  CALL("TPTP::args");
  _states.push(State::END_ARGS);
  _states.push(State::TERM);
} // args

/**
 * Read a list of arguments after a term
 * @since 27/07/2011 Manchester
 */
void TPTP::endArgs()
{
  CALL("TPTP::endArgs");
 // check if there is any other term in the argument list
  Token tok = getTok(0);
  switch (tok.tag) {
  case Tag::T_COMMA:
    resetToks();
    _ints.push(_ints.pop()+1);
    _states.push(State::END_ARGS);
    _states.push(State::TERM);
    return;
  case Tag::T_RPAR:
    resetToks();
    return;
  case Tag::T_RBRA:
    resetToks();
    return;
  default:
    PARSE_ERROR(", ) or ] expected after an end of a term",tok);
  }
} // endArgs

/**
 * Bind a variable to a sort
 * @since 22/04/2011 Manchester
 */
void TPTP::bindVariable(int var,unsigned sortNumber)
{
  CALL("TPTP::bindVariable");

  SortList* definitions;
  if (_variableSorts.find(var,definitions)) {
    _variableSorts.replace(var,new SortList(sortNumber,definitions));
  }
  else {
    _variableSorts.insert(var,new SortList(sortNumber));
  }
} // bindVariable

/**
 * Read a non-empty sequence of variable and save the resulting
 * sequence of TermList and their number
 * @since 07/07/2011 Manchester
 * @since 16/04/2015 Gothenburg, do not parse the closing ']'
 */
void TPTP::varList()
{
  CALL("TPTP::varList");

  Stack<int> vars;
  for (;;) {
    Token& tok = getTok(0);

    if (tok.tag != Tag::T_VAR) {
      PARSE_ERROR("variable expected",tok);
    }
    int var = _vars.insert(tok.content);
    vars.push(var);
    resetToks();
    bool sortDeclared = false;
  afterVar:
    tok = getTok(0);
    switch (tok.tag) {
    case Tag::T_COLON: // v: type
      if (sortDeclared) {
	PARSE_ERROR("two declarations of variable sort",tok);
      }
      resetToks();
      bindVariable(var,readSort());
      sortDeclared = true;
      goto afterVar;

    case Tag::T_COMMA:
      if (!sortDeclared) {
	bindVariable(var,(unsigned)Sorts::DefaultSorts::SRT_DEFAULT);
      }
      resetToks();
      break;

    default:
      {
	if (!sortDeclared) {
	  bindVariable(var, (unsigned)Sorts::DefaultSorts::SRT_DEFAULT);
	}
	Formula::VarList* vs = Formula::VarList::empty();
        Formula::SortList* ss = Formula::SortList::empty();
	while (!vars.isEmpty()) {
          int v = vars.pop();
	  vs = new Formula::VarList(v,vs);
          ss = new Formula::SortList(sortOf(TermList(v,false)),ss);
	}
	_varLists.push(vs);
        _sortLists.push(ss);
	_bindLists.push(vs);
	return;
      }
    }
  }
} // varList

/**
 * Read a term and save the resulting TermList
 * @since 10/04/2011 Manchester
 * @since 13/04/2015 Gothenburg, major changes to support FOOL
 */
void TPTP::term()
{
  CALL("TPTP::term");
  Token tok = getTok(0);
  switch (tok.tag) {
    case Tag::T_NAME:
    case Tag::T_THEORY_FUNCTION:
    case Tag::T_VAR:
    case Tag::T_ITE:
    case Tag::T_LET:
    case Tag::T_LBRA:
      _states.push(State::TERM_INFIX);
      _states.push(State::FUN_APP);
      return;

    case Tag::T_STRING:
    case Tag::T_INT:
    case Tag::T_REAL:
    case Tag::T_RAT: {
      resetToks();
      unsigned number;
      switch (tok.tag) {
        case Tag::T_STRING:
          number = env.signature->addStringConstant(tok.content);
          break;
        case Tag::T_INT:
          number = addIntegerConstant(tok.content,_overflow,_isFof);
          break;
        case Tag::T_REAL:
          number = addRealConstant(tok.content,_overflow,_isFof);
          break;
        case Tag::T_RAT:
          number = addRationalConstant(tok.content,_overflow,_isFof);
          break;
        default:
          ASSERTION_VIOLATION;
      }
      Term *t = new(0) Term;
      t->makeSymbol(number, 0);
      t = env.sharing->insert(t);
      TermList constant(t);
      _termLists.push(constant);
      return;
    }

    default:
      _states.push(State::FORMULA_INSIDE_TERM);
  }
} // term

/**
 * Build a term assembled by term()
 * @since 09/07/2011 Manchester
 * @since 14/04/2015 Gothenburg, major changes to support FOOL
 */
void TPTP::endTerm()
{
  CALL("TPTP::endTerm");

  vstring name = _strings.pop();

  if (name == toString(Tag::T_ITE)) {
    _states.push(State::END_ITE);
    return;
  }

  if (name == toString(Tag::T_LET)) {
    _states.push(State::END_LET);
    return;
  }

  if (name == toString(Tag::T_TUPLE)) {
    _states.push(State::END_TUPLE);
    return;
  }

  TheoryFunction tf;
  if (findTheoryFunction(name, tf)) {
    _theoryFunctions.push(tf);
    _states.push(State::END_THEORY_FUNCTION);
    return;
  }

  int arity = _ints.pop();

  if (arity == -1) {
    // it was a variable
    unsigned var = (unsigned)_vars.insert(name);
    _termLists.push(TermList(var, false));
    return;
  }

  LetSymbolReference ref;
  if (env.signature->predicateExists(name, arity) ||
      (findLetSymbol(LetSymbolName(name, arity), ref) && IS_PREDICATE(ref)) ||
      findInterpretedPredicate(name, arity)) {
    // if the function symbol is actually a predicate,
    // we need to construct a formula and wrap it inside a term
    _formulas.push(createPredicateApplication(name, arity));
    _states.push(State::END_FORMULA_INSIDE_TERM);
    return;
  }

  _termLists.push(createFunctionApplication(name, arity));
} // endTerm

/**
 * Read after an end of atom or after lhs of an equality or inequality
 * @since 10/04/2011 Manchester
 * @since 13/04/2015 Gothenburg, major changes to support FOOL
 */
void TPTP::formulaInfix()
{
  CALL("TPTP::formulaInfix");

  Token tok = getTok(0);

  if (tok.tag == Tag::T_EQUAL || tok.tag == Tag::T_NEQ) {
    _states.push(State::END_EQ);
    _states.push(State::TERM);
    _states.push(State::MID_EQ);
    _states.push(State::END_TERM);
    return;
  }

  vstring name = _strings.pop();

  if (name == toString(Tag::T_ITE)) {
    _states.push(State::END_TERM_AS_FORMULA);
    _states.push(State::END_ITE);
    return;
  }

  TheoryFunction tf;
  if (findTheoryFunction(name, tf)) {
    switch (tf) {
    case TheoryFunction::TF_STORE:
        USER_ERROR("$store expression cannot be used as formula");
        break;
      case TheoryFunction::TF_SELECT:
        _theoryFunctions.push(tf);
        _states.push(State::END_TERM_AS_FORMULA);
        _states.push(State::END_THEORY_FUNCTION);
        break;
      default:
        ASSERTION_VIOLATION_REP(name);
    }
    return;
  }

  if (name == toString(Tag::T_LET)) {
    _states.push(State::END_TERM_AS_FORMULA);
    _states.push(State::END_LET);
    return;
  }

  int arity = _ints.pop();

  if (arity == -1) {
    // that was a variable
    unsigned var = (unsigned)_vars.insert(name);
    _termLists.push(TermList(var, false));
    _states.push(State::END_TERM_AS_FORMULA);
    return;
  }

  _formulas.push(createPredicateApplication(name, arity));
} // formulaInfix

/**
 * Read after an end of equality or inequality and save the (in)equality formula.
 * @since 09/07/2011 Manchester
 */
void TPTP::endEquality()
{
  CALL("TPTP::endEquality");

  _insideEqualityArgument--;

  TermList rhs = _termLists.pop();
  TermList lhs = _termLists.pop();

  if (sortOf(rhs) != sortOf(lhs)) {
    unsigned rsort = sortOf(rhs); 
    unsigned lsort = sortOf(lhs);
    USER_ERROR("Cannot create equality between terms of different types.\n"+
      rhs.toString()+" is "+env.sorts->sortName(rsort)+"\n"+
      lhs.toString()+" is "+env.sorts->sortName(lsort)
    );
  }

  Literal* l = createEquality(_bools.pop(),lhs,rhs);
   _formulas.push(new AtomicFormula(l));
} // endEquality

/**
 * Read
 * @since 09/07/2011 Manchester
 */
void TPTP::midEquality()
{
  CALL("TPTP::midEquality");

  _insideEqualityArgument++;

  Token tok = getTok(0);
  switch (tok.tag) {
  case Tag::T_EQUAL:
    _bools.push(true);
    break;
  case Tag::T_NEQ:
    _bools.push(false);
    break;
  default:
    PARSE_ERROR("either = or != expected",tok);
  }
  resetToks();
} // midEquality

/**
 * Creates an equality literal and takes care of its sort when it
 * is an equality between two variables.
 * @since 21/07/2011 Manchester
 * @since 03/05/2013 Train Manchester-London, bug fix
 */
Literal* TPTP::createEquality(bool polarity,TermList& lhs,TermList& rhs)
{
  TermList masterVar;
  unsigned sortNumber;
  if (!SortHelper::getResultSortOrMasterVariable(lhs, sortNumber, masterVar)) {
    // Master variable is a variable whose sort determines the sort of a term.
    // If term is a variable, the master variable is the variable itself. The
    // trickier case is when we have an if-then-else expression with variable
    // arguments.
    SortList* vs;
    if (_variableSorts.find(masterVar.var(),vs) && vs) {
      sortNumber = vs->head();
    }
    else { // this may happen when free variables appear in the formula (or clause)
      sortNumber = (unsigned)Sorts::DefaultSorts::SRT_DEFAULT;
    }
  }

  return Literal::createEquality(polarity,lhs,rhs,sortNumber);
} // TPTP::createEquality

/**
 * Creates a formula that is a predicate application literal from
 * provided predicate symbol name and arity. If arity is greater than zero,
 * the arguments are assumed to be on the _termLists stack.
 * @since 27/03/1015 Manchester
 */
Formula* TPTP::createPredicateApplication(vstring name, unsigned arity)
{
  CALL("TPTP::createPredicateApplication");
  ASS_GE(_termLists.size(), arity);

  int pred;
  LetSymbolReference ref;
  if (findLetSymbol(LetSymbolName(name, arity), ref) && IS_PREDICATE(ref)) {
    pred = (int)SYMBOL(ref);
  } else {
    if (arity > 0) {
      bool dummy;
      pred = addPredicate(name, arity, dummy, _termLists.top());
    } else {
      pred = env.signature->addPredicate(name, 0);
    }
  }
  if (pred == -1) { // equality
    TermList rhs = _termLists.pop();
    TermList lhs = _termLists.pop();
    return new AtomicFormula(createEquality(true,lhs,rhs));
  }
  if (pred == -2){ // distinct
    // TODO check that we are top-level
    // If fewer than 5 things are distinct then we add the disequalities
    if(arity<5){
      static Stack<unsigned> distincts;
      distincts.reset();
      for(int i=arity-1;i >= 0; i--){
        TermList t = _termLists.pop();
        if(t.isVar() || t.term()->arity()!=0){ USER_ERROR("$distinct can only be used with constants");}
        distincts.push(t.term()->functor());
      }
      Formula* distinct_formula = DistinctGroupExpansion().expand(distincts);
      return distinct_formula;
    }else{
      // Otherwise record them as being in a distinct group
      unsigned grpIdx = env.signature->createDistinctGroup(0);
      for(int i = arity-1;i >=0; i--){
        TermList ts = _termLists.pop();
        if(!ts.isTerm() || ts.term()->arity()!=0){
          USER_ERROR("$distinct should only be used positively with constants");
        }
        env.signature->addToDistinctGroup(ts.term()->functor(),grpIdx);
      }
      return new Formula(true); // we ignore it, it evaluates to true as we have recorded it elsewhere
    }
  }
  // not equality or distinct
  Literal* lit = new(arity) Literal(pred,arity,true,false);
  OperatorType* type = env.signature->getPredicate(pred)->predType();
  bool safe = true;
  for (int i = arity-1;i >= 0;i--) {
    unsigned sort = type->arg(i);
    TermList ts = _termLists.pop();
    unsigned tsSort = sortOf(ts);
    if (sort != tsSort) {
      USER_ERROR("Argument " + Lib::Int::toString(i) +
                 " of predicate " + env.signature->predicateName(pred) +
                 " expected something of sort "+env.sorts->sortName(sort)+
                 " but got something of sort "+env.sorts->sortName(tsSort));
    }
    safe = safe && ts.isSafe();
    *(lit->nthArgument(i)) = ts;
  }
  if (safe) {
    lit = env.sharing->insert(lit);
  }
  return new AtomicFormula(lit);
} // createPredicateApplication

/**
 * Creates a term that is a function application from
 * provided function symbol name and arity. If arity is greater than zero,
 * the arguments are assumed to be on the _termLists stack.
 * @since 13/04/2015 Gothenburg, major changes to support FOOL
 */
TermList TPTP::createFunctionApplication(vstring name, unsigned arity)
{
  CALL("TPTP::createFunctionApplication");
  ASS_GE(_termLists.size(), arity);

  unsigned fun;
  LetSymbolReference ref;
  if (findLetSymbol(LetSymbolName(name, arity), ref) && !IS_PREDICATE(ref)) {
    fun = SYMBOL(ref);
  } else {
    bool dummy;
    if (arity > 0) {
      fun = addFunction(name, arity, dummy, _termLists.top());
    } else {
      fun = addUninterpretedConstant(name, _overflow, dummy);
    }
  }
  Term* t = new(arity) Term;
  t->makeSymbol(fun,arity);
  OperatorType* type = env.signature->getFunction(fun)->fnType();
  bool safe = true;
  for (int i = arity-1;i >= 0;i--) {
    unsigned sort = type->arg(i);
    TermList ss = _termLists.pop();
    unsigned ssSort = sortOf(ss);
    if (sort != ssSort) {
      USER_ERROR("The sort " + env.sorts->sortName(ssSort) + " of function argument " + ss.toString() + " "
                 "does not match the expected sort " + env.sorts->sortName(sort));
    }
    *(t->nthArgument(i)) = ss;
    safe = safe && ss.isSafe();
  }
  if (safe) {
    t = env.sharing->insert(t);
  }
  TermList ts(t);
  return ts;
}

/**
 * Build a formula from previousy built subformulas
 * @since 10/04/2011 Manchester
 */
void TPTP::endFormula()
{
  CALL("TPTP::endFormula");

  int con = _connectives.pop();
  Formula* f;
  bool conReverse;
  switch (con) {
  case (int)Connective::IMP:
  case (int)Connective::AND:
  case (int)Connective::OR:
    conReverse = _bools.pop();
    break;
  case (int)Connective::IFF:
  case (int)Connective::XOR:
  case -1:
    break;
  case (int)Connective::NOT:
    f = _formulas.pop();
    // This gets rid of the annoying step in proof output where ~(L) is flattend to (~L)
    if(f->connective()== Connective::LITERAL){
      Literal* oldLit = static_cast<AtomicFormula*>(f)->literal();
      Literal* newLit = Literal::create(oldLit,!oldLit->polarity());
      _formulas.push(new AtomicFormula(newLit));
    }
    else{
      _formulas.push(new NegatedFormula(f));
    }
    _states.push(State::END_FORMULA);
    return;
  case (int)Connective::FORALL:
  case (int)Connective::EXISTS:
    f = _formulas.pop();
    _formulas.push(new QuantifiedFormula((Connective)con,_varLists.pop(),_sortLists.pop(),f));
    _states.push(State::END_FORMULA);
    return;
  case (int)Connective::LITERAL:
  default:
    throw ::Exception((vstring)"tell me how to handle connective " + Int::toString(con));
  }

  Token& tok = getTok(0);
  Tag tag = tok.tag;
  Connective c;
  bool cReverse = false;
  switch (tag) {
  case Tag::T_AND:
    c = Connective::AND;
    break;
  case Tag::T_NOT_AND:
    cReverse = true;
    c = Connective::AND;
    break;
  case Tag::T_NOT_OR:
    cReverse = true;
    c = Connective::OR;
    break;
  case Tag::T_OR:
    c = Connective::OR;
    break;
  case Tag::T_XOR:
    c = Connective::XOR;
    break;
  case Tag::T_IFF:
    c = Connective::IFF;
    break;
  case Tag::T_IMPLY:
    c = Connective::IMP;
    break;
  case Tag::T_REVERSE_IMP:
    cReverse = true;
    c = Connective::IMP;
    break;
  case Tag::T_EQUAL:
  case Tag::T_NEQ: {
    // not connectives, but we allow formulas to be arguments to = and !=
    _states.push(State::END_EQ);
    _states.push(State::TERM);
    _states.push(State::MID_EQ);
    _states.push(State::END_FORMULA_INSIDE_TERM);
    return;
  }
  default:
    // the formula does not end at a binary connective, build the formula and terminate
    switch (con) {
    case (int)Connective::IMP:
      f = _formulas.pop();
      if (conReverse) {
	f = new BinaryFormula((Connective)con,f,_formulas.pop());
      }
      else {
	f = new BinaryFormula((Connective)con,_formulas.pop(),f);
      }
      _formulas.push(f);
      _states.push(State::END_FORMULA);
      return;

    case (int)Connective::IFF:
    case (int)Connective::XOR:
      f = _formulas.pop();
      f = new BinaryFormula((Connective)con,_formulas.pop(),f);
      _formulas.push(f);
      _states.push(State::END_FORMULA);
      return;

    case (int)Connective::AND:
    case (int)Connective::OR:
      f = _formulas.pop();
      f = makeJunction((Connective)con,_formulas.pop(),f);
      if (conReverse) {
	f = new NegatedFormula(f);
      }
      _formulas.push(f);
      _states.push(State::END_FORMULA);
      return;

    case -1:
      return;
#if VDEBUG
    default:
      ASSERTION_VIOLATION;
#endif
    }
  }

  // con and c are binary connectives
  if (higherPrecedence(con,(int)c)) {
    f = _formulas.pop();
    Formula* g = _formulas.pop();
    if (con == (int)Connective::AND || con == (int)Connective::OR) {
      f = makeJunction((Connective)con,g,f);
      if (conReverse) {
	f = new NegatedFormula(f);
      }
    }
    else if (con == (int)Connective::IMP && conReverse) {
      f = new BinaryFormula((Connective)con,f,g);
    }
    else {
      f = new BinaryFormula((Connective)con,g,f);
    }
    _formulas.push(f);
    _states.push(State::END_FORMULA);
    return;
  }

  // c is a binary connective
  _connectives.push(con);
  if (con == (int)Connective::IMP || con == (int)Connective::AND || con == (int)Connective::OR) {
    _bools.push(conReverse);
  }
  _connectives.push((int)c);
  if (c == Connective::IMP || c == Connective::AND || c == Connective::OR) {
    _bools.push(cReverse);
  }
  resetToks();
  _states.push(State::END_FORMULA);
  _states.push(State::SIMPLE_FORMULA);
} // endFormula

/**
 * Builds a term that really is a formula
 * @author Evgeny Kotelnikov
 * @since 27/03/2015 Manchester
 */
void TPTP::formulaInsideTerm()
{
  CALL("TPTP::formulaInsideTerm");
  _states.push(State::END_FORMULA_INSIDE_TERM);
  _states.push(State::FORMULA);
} // formulaInsideTerm

/**
 * Wraps a formula inside a term
 * @author Evgeny Kotelnikov
 * @since 27/03/2015 Manchester
 */
void TPTP::endFormulaInsideTerm()
{
  CALL("TPTP::endFormulaInsideTerm");
  Formula* f = _formulas.pop();
  TermList ts(Term::createFormula(f));
  _termLists.push(ts);
} // endFormulaInsideTerm

/**
 * Makes a boolean term a formula
 * @author Evgeny Kotelnikov
 * @since 27/03/2015 Manchester
 */
void TPTP::endTermAsFormula()
{
  CALL("TPTP::endTermAsFormula");
  TermList t = _termLists.pop();
  if (sortOf(t) != (unsigned)Sorts::DefaultSorts::SRT_BOOL) {
    vstring sortName = env.sorts->sortName(sortOf(t));
    USER_ERROR("Non-boolean term " + t.toString() + " of sort " + sortName + " is used in a formula context");
  }
  if (t.isTerm() && t.term()->isFormula()) {
    _formulas.push(t.term()->getSpecialData()->getFormula());
  } else {
    _formulas.push(new BoolTermFormula(t));
  }
} // endTermAsFormula

/**
 * Build a type from previousy built types
 * @since 14/07/2011 Manchester
 */
void TPTP::endType()
{
  CALL("TPTP::endType");

  TypeTag tt = _typeTags.pop();
  Type* t = _types.pop();
  switch (tt) {
  case TypeTag::TT_ATOMIC:
    break;
  case TypeTag::TT_PRODUCT:
    t = new ProductType(_types.pop(),t);
    tt = _typeTags.pop();
    break;
  case TypeTag::TT_ARROW:
    t = new ArrowType(_types.pop(),t);
    tt = _typeTags.pop();
    break;
  }
  ASS(tt == TypeTag::TT_ATOMIC);
  _types.push(t);

  Token tok = getTok(0);
  switch (tok.tag) {
  case Tag::T_STAR:
    _typeTags.push(tt);
    _typeTags.push(TypeTag::TT_PRODUCT);
    break;
  case Tag::T_ARROW:
    _typeTags.push(tt);
    _typeTags.push(TypeTag::TT_ARROW);
    break;
  default:
    return;
  }
  resetToks();
  _states.push(State::END_TYPE);
  _states.push(State::SIMPLE_TYPE);
} // endType

/**
 * Skip a tag.
 * @since 10/04/2011 Manchester
 */
void TPTP::tag()
{
  CALL("TPTP::tag");
  consumeToken(_tags.pop());
} // tag

/**
 * Process the end of the fof() definition and build the corresponding unit.
 * @since 10/04/2011 Manchester
 */
void TPTP::endFof()
{
  CALL("TPTP::endFof");

  TPTP::SourceRecord* source = 0;

  // are we interested in collecting sources?
  if (_unitSources) {
    source = getSource();
  }
#if DEBUG_SOURCE
  else{
    // create fake map
    _unitSources = new DHMap<Unit*,SourceRecord*>();
    source = getSource();
  }
#endif

  skipToRPAR();
  consumeToken(Tag::T_DOT);

  bool isFof = _bools.pop();
  Formula* f = _formulas.pop();
  vstring nm = _strings.pop(); // unit name
  if (_allowedNames && !_allowedNames->contains(nm)) {
    return;
  }

  Unit* unit;
  if (isFof) { // fof() or tff()
    env.statistics->inputFormulas++;
    unit = new FormulaUnit(f,FromInput(_lastInputType));
    unit->setInheritedColor(_currentColor);
  }
  else { // cnf()
    env.statistics->inputClauses++;
    // convert the input formula f to a clause
    Stack<Formula*> forms;
    Stack<Literal*> lits;
    Formula* g = nullptr;
    forms.push(f);
    while (! forms.isEmpty()) {
      g = forms.pop();
      switch (g->connective()) {
      case Connective::OR:
	{
	  FormulaList::Iterator fs(static_cast<JunctionFormula*>(g)->getArgs());
	  while (fs.hasNext()) {
	    forms.push(fs.next());
	  }
	}
	break;

      case Connective::LITERAL:
      case Connective::NOT:
	{
	  bool positive = true;
	  while (g->connective() == Connective::NOT) {
	    g = static_cast<NegatedFormula*>(g)->subformula();
	    positive = !positive;
	  }
	  if (g->connective() != Connective::LITERAL) {
	    USER_ERROR((vstring)"input formula not in CNF: " + f->toString());
	  }
	  Literal* l = static_cast<AtomicFormula*>(g)->literal();
	  lits.push(positive ? l : Literal::complementaryLiteral(l));
	}
	break;

      case Connective::_TRUE:
	return;
      case Connective::_FALSE:
	break;
      default:
	USER_ERROR((vstring)"input formula not in CNF: " + f->toString());
      }
    }
    unit = Clause::fromStack(lits,FromInput(_lastInputType));
    unit->setInheritedColor(_currentColor);
  }

  if(source){ 
    ASS(_unitSources);
    _unitSources->insert(unit,source);
  }

  if (env.options->outputAxiomNames()) {
    assignAxiomName(unit,nm);
  }
#if DEBUG_SHOW_UNITS
  cout << "Unit: " << unit->toString() << "\n";
#endif
  if (!_inputs.isEmpty()) {
    unit->inference().markIncluded();
  }

  switch (_lastInputType) {
  case UnitInputType::CONJECTURE:
    if(!isFof) USER_ERROR("conjecture is not allowed in cnf");
    if(_seenConjecture) USER_ERROR("Vampire only supports a single conjecture in a problem");
    _seenConjecture=true;
    if (_isQuestion && ((env.options->mode() == Options::Mode::CLAUSIFY) || (env.options->mode() == Options::Mode::TCLAUSIFY)) && f->connective() == Connective::EXISTS) {
      // create an answer predicate
      QuantifiedFormula* g = static_cast<QuantifiedFormula*>(f);
      unsigned arity = Formula::VarList::length(g->vars());
      unsigned pred = env.signature->addPredicate("$$answer",arity);
      env.signature->getPredicate(pred)->markAnswerPredicate();
      Literal* a = new(arity) Literal(pred,arity,true,false);
      Formula::VarList::Iterator vs(g->vars());
      int i = 0;
      while (vs.hasNext()) {
	a->nthArgument(i++)->makeVar(vs.next());
      }
      a = env.sharing->insert(a);
      f = new QuantifiedFormula(Connective::FORALL,
				g->vars(),
                                g->sorts(),
				new BinaryFormula(Connective::IMP,g->subformula(),new AtomicFormula(a)));
      unit = new FormulaUnit(f,
			     FormulaTransformation(InferenceRule::ANSWER_LITERAL,unit));
    }
    else {
      Formula::VarList* vs = f->freeVariables();
      if (Formula::VarList::isEmpty(vs)) {
	f = new NegatedFormula(f);
      }
      else {
        // TODO can we use sortOf to get the sorts of vs? 
	f = new NegatedFormula(new QuantifiedFormula(Connective::FORALL,vs,0,f));
      }
      unit = new FormulaUnit(f,
			     FormulaTransformation(InferenceRule::NEGATED_CONJECTURE,unit));
    }
    break;

  case UnitInputType::CLAIM:
    {
      bool added;
      unsigned pred = env.signature->addPredicate(nm,0,added);
      if (!added) {
	USER_ERROR("Names of claims must be unique: "+nm);
      }
      env.signature->getPredicate(pred)->markLabel();
      Literal* a = new(0) Literal(pred,0,true,false);
      a = env.sharing->insert(a);
      Formula* claim = new AtomicFormula(a);
      Formula::VarList* vs = f->freeVariables();
      if (Formula::VarList::isNonEmpty(vs)) {
        //TODO can we use sortOf to get sorts of vs?
	f = new QuantifiedFormula(Connective::FORALL,vs,0,f);
      }
      f = new BinaryFormula(Connective::IFF,claim,f);
      unit = new FormulaUnit(f,
          FormulaTransformation(InferenceRule::CLAIM_DEFINITION,unit));
    }
    break;

  default:
    break;
  }
  _units.push(unit);
} // tag

/**
 * Add a state just reading a tag and save the tag in _tags.
 * @since 28/07/2011 Manchester
 */
void TPTP::addTagState(Tag t)
{
  CALL("TPTP::addTagState");
  _states.push(State::TAG);
  _tags.push(t);
} // TPTP::addTagState

/**
 * Process the end of the tff() definition and build the corresponding unit.
 * @since 14/07/2011 Manchester
 */
void TPTP::endTff()
{
  CALL("TPTP::endTff");

  int rpars= _ints.pop();
  while (rpars--) {
    consumeToken(Tag::T_RPAR);
  }
  skipToRPAR();
  consumeToken(Tag::T_DOT);

  // build a TPTP out of the parse type
  ASS(_typeTags.isEmpty());
  Type* t = _types.pop();
  ASS(_types.isEmpty());

  OperatorType* ot = constructOperatorType(t);

  vstring name = _strings.pop();

  unsigned arity = ot->arity();
  bool isPredicate = ot->isPredicateType();

  bool added;
  Signature::Symbol* symbol;
  if (isPredicate) {
    unsigned pred = env.signature->addPredicate(name, arity, added);
    symbol = env.signature->getPredicate(pred);
    if (!added) {
      // GR: Multiple identical type declarations for a symbol are allowed
      if(symbol->predType() != ot){
        USER_ERROR("Predicate symbol type is declared after its use: " + name);
      }
    }
    else{
      if (arity != 0) {
        symbol->setType(ot);
      }
    }
  } else {
    unsigned fun = arity == 0
                   ? addUninterpretedConstant(name, _overflow, added)
                   : env.signature->addFunction(name, arity, added);
    symbol = env.signature->getFunction(fun);
    if (!added) {
      // GR: Multiple identical type declarations for a symbol are allowed
      if(symbol->fnType() != ot){
        USER_ERROR("Function symbol type is declared after its use: " + name);
      }
    }
    else{
      symbol->setType(ot);
    }
  }
} // endTff

OperatorType* TPTP::constructOperatorType(Type* t)
{
  CALL("TPTP::constructOperatorType");

  unsigned resultSort;
  Stack<unsigned> argumentSorts;

  switch (t->tag()) {
  case Parse::TPTP::TypeTag::TT_PRODUCT:
      USER_ERROR("product types are not supported");

    case Parse::TPTP::TypeTag::TT_ATOMIC: {
      // atomic types: 0-ary predicates (propositions) and constants (0-ary functions, eg. int constant, array1 constants)
      resultSort = static_cast<AtomicType*>(t)->sortNumber();
      break;
    }

    case Parse::TPTP::TypeTag::TT_ARROW: {
      // non-atomic types, i.e. with arrows
      ArrowType* at = static_cast<ArrowType*>(t);
      Type* rhs = at->returnType();
      if (rhs->tag() != Parse::TPTP::TypeTag::TT_ATOMIC) {
        USER_ERROR("complex return types are not supported");
      }

      resultSort = static_cast<AtomicType *>(rhs)->sortNumber();
      Stack<Type*> types;
      types.push(at->argumentType());
      while (!types.isEmpty()) {
        Type *tp = types.pop();
        switch (tp->tag()) {
          case Parse::TPTP::TypeTag::TT_ARROW:
            USER_ERROR("higher-order types are not supported");

          case Parse::TPTP::TypeTag::TT_ATOMIC: {
            unsigned sortNumber = static_cast<AtomicType*>(tp)->sortNumber();
            argumentSorts.push(sortNumber);
            break;
          }

          case Parse::TPTP::TypeTag::TT_PRODUCT: {
            ProductType* pt = static_cast<ProductType*>(tp);
            types.push(pt->rhs());
            types.push(pt->lhs());
            break;
          }

#if VDEBUG
          default:
            ASSERTION_VIOLATION;
#endif
        }
      }
      break;
    }

#if VDEBUG
    default:
      ASSERTION_VIOLATION;
#endif
  }

  bool isPredicate = resultSort == (unsigned)Sorts::DefaultSorts::SRT_BOOL;
  unsigned arity = (unsigned)argumentSorts.size();
  if (isPredicate) {
    return OperatorType::getPredicateType(arity, argumentSorts.begin());
  } else {
    return OperatorType::getFunctionType(arity, argumentSorts.begin(), resultSort);
  }
} // constructOperatorType

/**
 *
 * @author Giles
 */
TPTP::SourceRecord* TPTP::getSource()
{
  if (getTok(0).tag != Tag::T_COMMA) { // if comma is not there, source was not provided
    return 0;
  }

  consumeToken(Tag::T_COMMA);

  //Either source is a file or an inference, otherwise we don't care about it!
  //  therefore failing will return 0
 
  Token& source_kind = getTok(0);
  if(source_kind.tag != Tag::T_NAME) return 0;

  resetToks();
  if (getTok(0).tag != Tag::T_LPAR) {
    return 0;
  } else {
    resetToks();
  }
  
  //file
  if(source_kind.content == "file"){
    vstring fileName = getTok(0).content;
    resetToks();
    consumeToken(Tag::T_COMMA);
    resetToks();
    vstring nameInFile = getTok(0).content;
    resetToks();

    // cout << "Creating file source record for " << fileName << " and " << nameInFile << endl;

    consumeToken(Tag::T_RPAR);
    return new FileSourceRecord(fileName,nameInFile);
  }
  // inference
  else if(source_kind.content == "inference" || source_kind.content == "introduced"){
    bool introduced = (source_kind.content == "introduced");
    vstring name = getTok(0).content;
    resetToks();

    // cout << "Creating inference source record for " << name <<  endl;

    InferenceSourceRecord* r = new InferenceSourceRecord(name);

    if(introduced){
      // then we don't expect names and we don't care about middle info 
      resetToks();
      skipToRPAR();
      return r;
    }

    // now skip this middle information that is between [ and ]
    consumeToken(Tag::T_COMMA);
    consumeToken(Tag::T_LBRA);
    skipToRBRA();
    consumeToken(Tag::T_COMMA);
    consumeToken(Tag::T_LBRA);

    // read comma separated list of names
    Token tok;
    while((tok=getTok(0)).tag != Tag::T_RBRA){
      resetToks();
      if(tok.tag == Tag::T_COMMA) continue;
   
      if (tok.tag != Tag::T_NAME && tok.tag != Tag::T_INT) {
        cout << "read token " << tok.tag << " with content " << tok.content << endl;

        // TODO: parse errors are nice, but maybe we just want to ignore any info which we cannot understand?

        PARSE_ERROR("Source unit name expected",tok);
      }

      vstring premise = tok.content;

      tok = getTok(0);
      if (tok.tag != Tag::T_COMMA && tok.tag != Tag::T_RBRA) {
        // if the next thing is neither comma not RBRA, it is an ugly info piece we want to skip
        resetToks();
        skipToRPAR();
      } else {
        r->premises.push(premise);
        // cout << "pushed premise " << premise << endl;
      }
    }
    resetToks();

    consumeToken(Tag::T_RPAR);
    return r;
  } else {
    
    skipToRPAR();
  }

  return 0;
}


/**
 * Skip any sequence tokens, including matching pairs of left parentheses,
 * until an unmatched right parenthesis is found. Consume this right parenthesis
 * and terminate.
 * @since 15/07/2011 Manchester
 */
void TPTP::skipToRPAR()
{
  int balance = 0;
  for (;;) {
    Token tok = getTok(0);
    switch (tok.tag) {
    case Tag::T_EOF:
      PARSE_ERROR(") not found",tok);
    case Tag::T_LPAR:
      resetToks();
      balance++;
      break;
    case Tag::T_RPAR:
      resetToks();
      balance--;
      if (balance == -1) {
	return;
      }
      break;
    default:
      resetToks();
      break;
    }
  }
} // skipToRPAR

/**
 * A copy of skipToRPAR but for BRA
 */
void TPTP::skipToRBRA()
{
  int balance = 0;
  for (;;) {
    Token tok = getTok(0);
    switch (tok.tag) {
    case Tag::T_EOF:
      PARSE_ERROR(") not found",tok);
    case Tag::T_LBRA:
      resetToks();
      balance++;
      break;
    case Tag::T_RBRA:
      resetToks();
      balance--;
      if (balance == -1) {
        return;
      }
      break;
    default:
      resetToks();
      break;
    }
  }
} // skipToRBRA

/**
 * Read a simple formula (quantified formula, negation,
 * formula in parentheses, true or false).
 * @since 10/04/2011 Manchester
 */
void TPTP::simpleFormula()
{
  CALL("TPTP::simpleFormula");

  Token tok = getTok(0);

  switch (tok.tag) {
  case Tag::T_NOT:
    resetToks();
    _connectives.push((int)Connective::NOT);
    _states.push(State::SIMPLE_FORMULA);
    return;

  case Tag::T_FORALL:
  case Tag::T_EXISTS:
    resetToks();
    consumeToken(Tag::T_LBRA);
    _connectives.push((int)(tok.tag == Tag::T_FORALL ? Connective::FORALL : Connective::EXISTS));
    _states.push(State::UNBIND_VARIABLES);
    _states.push(State::SIMPLE_FORMULA);
    addTagState(Tag::T_COLON);
    addTagState(Tag::T_RBRA);
    _states.push(State::VAR_LIST);
    return;

  case Tag::T_LPAR:
    resetToks();
    addTagState(Tag::T_RPAR);
    _states.push(State::FORMULA);
    return;

  case Tag::T_STRING:
  case Tag::T_INT:
  case Tag::T_RAT:
  case Tag::T_REAL:
    _states.push(State::END_EQ);
    _states.push(State::TERM);
    _states.push(State::MID_EQ);
    _states.push(State::TERM);
    return;
  case Tag::T_TRUE:
    resetToks();
    _formulas.push(new Formula(true));
    return;
  case Tag::T_FALSE:
    resetToks();
    _formulas.push(new Formula(false));
    return;
  case Tag::T_NAME:
  case Tag::T_VAR:
  case Tag::T_ITE:
  case Tag::T_THEORY_FUNCTION:
  case Tag::T_LET:
  case Tag::T_LBRA:
    _states.push(State::FORMULA_INFIX);
    _states.push(State::FUN_APP);
    return;
  default:
    PARSE_ERROR("formula or term expected",tok);
  }
} // simpleFormula

/**
 * Unbind variable sort definition.
 * @since 14/07/2011 Manchester
 */
void TPTP::unbindVariables()
{
  CALL("TPTP::unbindVariables");

  Formula::VarList::Iterator vs(_bindLists.pop());
  while (vs.hasNext()) {
    int var = vs.next();
    SortList* sorts;
    ALWAYS(_variableSorts.find(var,sorts));
    _variableSorts.replace(var,sorts->tail());
    delete sorts; // this deletes just the "popped" cell
  }
} // unbindVariables

/**
 * Read a simple type: name or type in parentheses
 * @since 14/07/2011 Manchester
 */
void TPTP::simpleType()
{
  CALL("TPTP::simpleType");

  Token& tok = getTok(0);
  if (tok.tag == Tag::T_LPAR) {
    resetToks();
    addTagState(Tag::T_RPAR);
    _states.push(State::TYPE);
    return;
  }
  _types.push(new AtomicType(readSort()));
} // simpleType

/**
 * Read a sort and return its number. If a sort is not built-in, then raise an
 * exception if it has been declared and newSortExpected, or it has not been
 * declared and newSortExpected is false.
 * @since 14/07/2011 Manchester
 */
unsigned TPTP::readSort()
{
  CALL("TPTP::readSort");

  Token tok = getTok(0);
  resetToks();
  switch (tok.tag) {
  case Tag::T_NAME:
    {
      bool added;
      unsigned sortNumber = env.sorts->addSort(tok.content,added,false);
      if (added) {
      	PARSE_ERROR("undeclared sort",tok);
      }
      return sortNumber;
    }

  case Tag::T_DEFAULT_TYPE:
    return (unsigned)Sorts::DefaultSorts::SRT_DEFAULT;

  case Tag::T_BOOL_TYPE:
    return (unsigned)Sorts::DefaultSorts::SRT_BOOL;

  case Tag::T_INTEGER_TYPE:
    return (unsigned)Sorts::DefaultSorts::SRT_INTEGER;

  case Tag::T_RATIONAL_TYPE:
    return (unsigned)Sorts::DefaultSorts::SRT_RATIONAL;

  case Tag::T_REAL_TYPE:
    return (unsigned)Sorts::DefaultSorts::SRT_REAL;

  case Tag::T_LBRA:
  {
    Stack<unsigned> sorts;
    for (;;) {
      unsigned sort = readSort();
      sorts.push(sort);
      if (getTok(0).tag == Tag::T_COMMA) {
        resetToks();
      } else {
        consumeToken(Tag::T_RBRA);
        break;
      }
    }

    if (sorts.length() < 2) {
      USER_ERROR("Tuple sort with less than two arguments");
    }

    return env.sorts->addTupleSort((unsigned) sorts.length(), sorts.begin());
  }
  case Tag::T_THEORY_SORT: {
    unsigned sort;
    consumeToken(Tag::T_LPAR);
    switch (getTheorySort(tok)) {
      case Parse::TPTP::TheorySort::TS_ARRAY: {
        unsigned indexSort = readSort();
        consumeToken(Parse::TPTP::Tag::T_COMMA);
        unsigned innerSort = readSort();
        sort = env.sorts->addArraySort(indexSort, innerSort);
        break;
      }
      default:
        ASSERTION_VIOLATION;
    }
    consumeToken(Tag::T_RPAR);
    return sort;
  }
  default:
    PARSE_ERROR("sort expected",tok);
  }
} // readSort

/**
 * True if c1 has a strictly higher priority than c2.
 * @since 07/07/2011 Manchester
 */
bool TPTP::higherPrecedence(int c1,int c2)
{
  if (c1 == c2) return false;
  if (c1 == -1) return false;
  if (c2 == (int)Connective::IFF) return true;
  if (c1 == (int)Connective::IFF) return false;
  if (c2 == (int)Connective::XOR) return true;
  if (c1 == (int)Connective::XOR) return false;
  if (c2 == (int)Connective::IMP) return true;
  if (c1 == (int)Connective::IMP) return false;
  if (c2 == (int)Connective::OR) return true;
  if (c1 == (int)Connective::OR) return false;
  ASSERTION_VIOLATION;
} // higherPriority

bool TPTP::findInterpretedPredicate(vstring name, unsigned arity) {
  CALL("TPTP::findInterpretedPredicate");

  if (name == "$evaleq" || name == "$equal" || name == "$distinct") {
    return true;
  }

  if (name == "$is_int" || name == "$is_rat") {
    return arity == 1;
  }

  if (name == "$less" || name == "$lesseq" || name == "$greater" || name == "$greatereq" || name == "$divides") {
    return arity == 2;
  }

  return false;
}

/**
 * Create an and- or or-formula flattening its lhs and rhs if necessary.
 * @since 07/07/2011 Manchester
 */
Formula* TPTP::makeJunction (Connective c,Formula* lhs,Formula* rhs)
{
  if (lhs->connective() == c) {
    FormulaList* largs = lhs->args();

    if (rhs->connective() == c) {
      FormulaList::concat(largs,rhs->args());
      delete static_cast<JunctionFormula*>(rhs);
      return lhs;
    }
    // only lhs has c as the main connective
    FormulaList::concat(largs,new FormulaList(rhs));
    return lhs;
  }
  // lhs' connective is not c
  if (rhs->connective() == c) {
    static_cast<JunctionFormula*>(rhs)->setArgs(new FormulaList(lhs,
								rhs->args()));
    return rhs;
  }
  // both connectives are not c
  return new JunctionFormula(c,
			     new FormulaList(lhs,
					     new FormulaList(rhs)));
} // makeJunction

/** Add a function to the signature
 * @param name the function name
 * @param arity the function arity
 * @param added if the function is new, will be assigned true, otherwise false
 * @param arg some argument of the function, require to resolve its type for overloaded
 *        built-in functions
 */
unsigned TPTP::addFunction(vstring name,int arity,bool& added,TermList& arg)
{
  CALL("TPTP::addFunction");

  if (name == "$sum") {
    return addOverloadedFunction(name,arity,2,added,arg,
        Theory::Interpretation::INT_PLUS,
        Theory::Interpretation::RAT_PLUS,
        Theory::Interpretation::REAL_PLUS);
  }
  if (name == "$difference") {
    return addOverloadedFunction(name,arity,2,added,arg,
        Theory::Interpretation::INT_MINUS,
        Theory::Interpretation::RAT_MINUS,
        Theory::Interpretation::REAL_MINUS);
  }
  if (name == "$product") {
    return addOverloadedFunction(name,arity,2,added,arg,
				 Theory::Interpretation::INT_MULTIPLY,
        Theory::Interpretation::RAT_MULTIPLY,
        Theory::Interpretation::REAL_MULTIPLY);
  }
  // An odd leftover, maps to the 'most natural' kind of division
  if (name == "$divide") {
    return addOverloadedFunction(name,arity,2,added,arg,
        Theory::Interpretation::INT_QUOTIENT_E,
        Theory::Interpretation::RAT_QUOTIENT,
        Theory::Interpretation::REAL_QUOTIENT);
  }
  if (name == "$modulo"){
    if(sortOf(arg)!=(unsigned)Sorts::DefaultSorts::SRT_INTEGER){
      USER_ERROR("$modulo can only be used with integer type");
    }
    return addOverloadedFunction(name,arity,2,added,arg,
        Theory::Interpretation::INT_REMAINDER_E,  // $modulo is the always positive remainder, therefore INT_REMAINDER_E
        Theory::Interpretation::INT_REMAINDER_E,  // will not be used
        Theory::Interpretation::INT_REMAINDER_E); // will not be used
  }
  if (name == "$abs"){
    if(sortOf(arg)!=(unsigned)Sorts::DefaultSorts::SRT_INTEGER){
      USER_ERROR("$abs can only be used with integer type");
    }
    return addOverloadedFunction(name,arity,1,added,arg,
        Theory::Interpretation::INT_ABS,
        Theory::Interpretation::INT_ABS,  // will not be used
        Theory::Interpretation::INT_ABS); // will not be used
  }
  if (name == "$quotient") {
    if(sortOf(arg)== (unsigned)Sorts::DefaultSorts::SRT_INTEGER){
      USER_ERROR("$quotient cannot be used with integer type");
    }
    return addOverloadedFunction(name,arity,2,added,arg,
        Theory::Interpretation::INT_QUOTIENT_E,// this is a dummy
        Theory::Interpretation::RAT_QUOTIENT,
        Theory::Interpretation::REAL_QUOTIENT);
  }
  if (name == "$quotient_e") {
    return addOverloadedFunction(name,arity,2,added,arg,
        Theory::Interpretation::INT_QUOTIENT_E,
        Theory::Interpretation::RAT_QUOTIENT_E,
        Theory::Interpretation::REAL_QUOTIENT_E);
  }
  if (name == "$quotient_t") {
    return addOverloadedFunction(name,arity,2,added,arg,
                                 Theory::Interpretation::INT_QUOTIENT_T,
        Theory::Interpretation::RAT_QUOTIENT_T,
        Theory::Interpretation::REAL_QUOTIENT_T);
  }
  if (name == "$quotient_f") {
    return addOverloadedFunction(name,arity,2,added,arg,
        Theory::Interpretation::INT_QUOTIENT_F,
        Theory::Interpretation::RAT_QUOTIENT_F,
        Theory::Interpretation::REAL_QUOTIENT_F);
  }
  if (name == "$remainder_e") {
    return addOverloadedFunction(name,arity,2,added,arg,
        Theory::Interpretation::INT_REMAINDER_E,
        Theory::Interpretation::RAT_REMAINDER_E,
        Theory::Interpretation::REAL_REMAINDER_E);
  }
  if (name == "$remainder_t") {
    return addOverloadedFunction(name,arity,2,added,arg,
        Theory::Interpretation::INT_REMAINDER_T,
        Theory::Interpretation::RAT_REMAINDER_T,
        Theory::Interpretation::REAL_REMAINDER_T);
  }
  if (name == "$remainder_f") {
    return addOverloadedFunction(name,arity,2,added,arg,
        Theory::Interpretation::INT_REMAINDER_F,
        Theory::Interpretation::RAT_REMAINDER_F,
        Theory::Interpretation::REAL_REMAINDER_F);
  }
  if (name == "$uminus") {
    return addOverloadedFunction(name,arity,1,added,arg,
        Theory::Interpretation::INT_UNARY_MINUS,
        Theory::Interpretation::RAT_UNARY_MINUS,
        Theory::Interpretation::REAL_UNARY_MINUS);
  }
  if (name == "$successor"){
    if(sortOf(arg)!=(unsigned)Sorts::DefaultSorts::SRT_INTEGER){
      USER_ERROR("$succ can only be used with integer type");
    }
    return addOverloadedFunction(name,arity,1,added,arg,
        Theory::Interpretation::INT_SUCCESSOR,
        Theory::Interpretation::INT_SUCCESSOR,  // will not be used
        Theory::Interpretation::INT_SUCCESSOR); // will not be used
  }
  if (name == "$floor") {
    return addOverloadedFunction(name,arity,1,added,arg,
        Theory::Interpretation::INT_FLOOR,
        Theory::Interpretation::RAT_FLOOR,
        Theory::Interpretation::REAL_FLOOR);
  }
  if (name == "$ceiling") {
    return addOverloadedFunction(name,arity,1,added,arg,
        Theory::Interpretation::INT_CEILING,
        Theory::Interpretation::RAT_CEILING,
        Theory::Interpretation::REAL_CEILING);
  }
  if (name == "$truncate") {
    return addOverloadedFunction(name,arity,1,added,arg,
        Theory::Interpretation::INT_TRUNCATE,
        Theory::Interpretation::RAT_TRUNCATE,
        Theory::Interpretation::REAL_TRUNCATE);
  }
  if (name == "$round") {
    return addOverloadedFunction(name,arity,1,added,arg,
        Theory::Interpretation::INT_ROUND,
        Theory::Interpretation::RAT_ROUND,
        Theory::Interpretation::REAL_ROUND);
  }
  if (name == "$to_int") {
    return addOverloadedFunction(name,arity,1,added,arg,
        Theory::Interpretation::INT_TO_INT,
        Theory::Interpretation::RAT_TO_INT,
        Theory::Interpretation::REAL_TO_INT);
  }
  if (name == "$to_rat") {
    return addOverloadedFunction(name,arity,1,added,arg,
        Theory::Interpretation::INT_TO_RAT,
        Theory::Interpretation::RAT_TO_RAT,
        Theory::Interpretation::REAL_TO_RAT);
  }
  if (name == "$to_real") {
    return addOverloadedFunction(name,arity,1,added,arg,
        Theory::Interpretation::INT_TO_REAL,
        Theory::Interpretation::RAT_TO_REAL,
        Theory::Interpretation::REAL_TO_REAL);
  }

  if (arity > 0) {
    return env.signature->addFunction(name,arity,added);
  }
  return addUninterpretedConstant(name,_overflow,added);
} // addFunction

/** Add a predicate to the signature
 * @param name the predicate name
 * @param arity the predicate arity
 * @param added if the predicate is new, will be assigned true, otherwise false
 * @param arg some argument of the predicate, require to resolve its type for overloaded
 *        built-in predicates
 * @return the predicate number in the signature, or -1 if it is a different name for an equality
 *         predicate
 */
int TPTP::addPredicate(vstring name,int arity,bool& added,TermList& arg)
{
  CALL("TPTP::addPredicate");

  if (name == "$evaleq" || name == "$equal") {
    return -1;
  }
  if (name == "$less") {
    return addOverloadedPredicate(name,arity,2,added,arg,
        Theory::Interpretation::INT_LESS,
        Theory::Interpretation::RAT_LESS,
        Theory::Interpretation::REAL_LESS);
  }
  if (name == "$lesseq") {
    return addOverloadedPredicate(name,arity,2,added,arg,
        Theory::Interpretation::INT_LESS_EQUAL,
        Theory::Interpretation::RAT_LESS_EQUAL,
        Theory::Interpretation::REAL_LESS_EQUAL);
  }
  if (name == "$greater") {
    return addOverloadedPredicate(name,arity,2,added,arg,
        Theory::Interpretation::INT_GREATER,
        Theory::Interpretation::RAT_GREATER,
        Theory::Interpretation::REAL_GREATER);
  }
  if (name == "$greatereq") {
    return addOverloadedPredicate(name,arity,2,added,arg,
        Theory::Interpretation::INT_GREATER_EQUAL,
        Theory::Interpretation::RAT_GREATER_EQUAL,
        Theory::Interpretation::REAL_GREATER_EQUAL);
  }
  if (name == "$is_int") {
    return addOverloadedPredicate(name,arity,1,added,arg,
        Theory::Interpretation::INT_IS_INT,
        Theory::Interpretation::RAT_IS_INT,
        Theory::Interpretation::REAL_IS_INT);
  }
  if (name == "$divides"){
    if(sortOf(arg)!= (unsigned)Sorts::DefaultSorts::SRT_INTEGER){
      USER_ERROR("$divides can only be used with integer type");
    }
    return addOverloadedPredicate(name,arity,2,added,arg,
        Theory::Interpretation::INT_DIVIDES,
        Theory::Interpretation::INT_DIVIDES,  // will not be used
        Theory::Interpretation::INT_DIVIDES); // will not be used
  }
  if (name == "$is_rat") {
    return addOverloadedPredicate(name,arity,1,added,arg,
        Theory::Interpretation::INT_IS_RAT,
        Theory::Interpretation::RAT_IS_RAT,
        Theory::Interpretation::REAL_IS_RAT);
  }
  if(name == "$distinct"){
    // special case for distinct, dealt with in formulaInfix
    return -2;
  }
  return env.signature->addPredicate(name,arity,added);
} // addPredicate


unsigned TPTP::addOverloadedFunction(vstring name,int arity,int symbolArity,bool& added,TermList& arg,
				     Theory::Interpretation integer,Theory::Interpretation rational,
				     Theory::Interpretation real)
{
  CALL("TPTP::addOverloadedFunction");

  if (arity != symbolArity) {
    USER_ERROR(name + " is used with " + Int::toString(arity) + " argument(s)");
  }
  unsigned srt = sortOf(arg);
  TermList* n = arg.next();
  for(int i=1;i<arity;i++){
    if(sortOf(*n)!=srt) USER_ERROR((vstring)"The symbol " + name + " is not used with a single sort");
    n = n->next();
  }
  if (srt == (unsigned)Sorts::DefaultSorts::SRT_INTEGER) {
    return env.signature->addInterpretedFunction(integer,name);
  }
  if (srt == (unsigned)Sorts::DefaultSorts::SRT_RATIONAL) {
    return env.signature->addInterpretedFunction(rational,name);
  }
  if (srt == (unsigned)Sorts::DefaultSorts::SRT_REAL) {
    return env.signature->addInterpretedFunction(real,name);
  }
  USER_ERROR((vstring)"The symbol " + name + " is used with a non-numeric type");
} // addOverloadedFunction

unsigned TPTP::addOverloadedPredicate(vstring name,int arity,int symbolArity,bool& added,TermList& arg,
				     Theory::Interpretation integer,Theory::Interpretation rational,
				     Theory::Interpretation real)
{
  CALL("TPTP::addOverloadedPredicate");

  if (arity != symbolArity) {
    USER_ERROR(name + " is used with " + Int::toString(arity) + " argument(s)");
  }
  unsigned srt = sortOf(arg);
  TermList* n = arg.next();
  for(int i=1;i<arity;i++){
    if(sortOf(*n)!=srt) USER_ERROR((vstring)"The symbol " + name + " is not used with a single sort");
    n = n->next(); 
  }
  
  if (srt == (unsigned)Sorts::DefaultSorts::SRT_INTEGER) {
    return env.signature->addInterpretedPredicate(integer,name);
  }
  if (srt == (unsigned)Sorts::DefaultSorts::SRT_RATIONAL) {
    return env.signature->addInterpretedPredicate(rational,name);
  }
  if (srt == (unsigned)Sorts::DefaultSorts::SRT_REAL) {
    return env.signature->addInterpretedPredicate(real,name);
  }
  USER_ERROR((vstring)"The symbol " + name + " is used with a non-numeric type");
} // addOverloadedPredicate

/**
 * Return the sort of the term.
 * @since 29/07/2011 Manchester
 * @since 03/05/2013 train Manchester-London bug fix
 * @author Andrei Voronkov
 */
unsigned TPTP::sortOf(TermList t)
{
  CALL("TPTP::sortOf");

  for (;;) {
    if (t.isVar()) {
      SortList* sorts;
      if (_variableSorts.find(t.var(),sorts) && SortList::isNonEmpty(sorts)) {
	return sorts->head();
      }
      // there might be variables whose sort is undeclared,
      // in this case they have the default sort
      bindVariable(t.var(), (unsigned)Sorts::DefaultSorts::SRT_DEFAULT);
      return (unsigned)Sorts::DefaultSorts::SRT_DEFAULT;
    }
    unsigned sort;
    TermList mvar;
    if (SortHelper::getResultSortOrMasterVariable(t.term(), sort, mvar)) {
      return sort;
    } else {
      t = mvar;
    }
  }
} // sortOf

/**
 * Add an integer constant by reading it from the vstring name.
 * If it overflows, create an uninterpreted constant of the
 * integer type and the name 'name'. Check that the name of the constant
 * does not collide with user-introduced names of uninterpreted constants.
 * @since 22/07/2011 Manchester
 * @since 03/05/2013 train Manchester-London, bug fix: integers are treated
 *   as terms of the default sort when fof() or cnf() is used
 * @author Andrei Voronkov
 */
unsigned TPTP::addIntegerConstant(const vstring& name, Set<vstring>& overflow, bool defaultSort)
{
  CALL("TPTP::addIntegerConstant");

  try {
    return env.signature->addIntegerConstant(name,defaultSort);
  }
  catch (Kernel::ArithmeticException&) {
    bool added;
    unsigned fun = env.signature->addFunction(name,0,added,true /* overflown constant*/);
    if (added) {
      overflow.insert(name);
      Signature::Symbol* symbol = env.signature->getFunction(fun);
      symbol->setType(OperatorType::getConstantsType(defaultSort ? (unsigned)Sorts::DefaultSorts::SRT_DEFAULT : (unsigned)Sorts::DefaultSorts::SRT_INTEGER));
    }
    else if (!overflow.contains(name)) {
      USER_ERROR((vstring)"Cannot use name '" + name + "' as an atom name since it collides with an integer number");
    }
    return fun;
  }
} // TPTP::addIntegerConstant

/**
 * Add an rational constant by reading it from the vstring name.
 * If it overflows, create an uninterpreted constant of the
 * rational type and the name 'name'. Check that the name of the constant
 * does not collide with user-introduced names of uninterpreted constants.
 * @since 22/07/2011 Manchester
 * @since 03/05/2013 train Manchester-London, fix to handle difference
 *    between treating rationals using fof() and tff()
 * @author Andrei Voronkov
 */
unsigned TPTP::addRationalConstant(const vstring& name, Set<vstring>& overflow, bool defaultSort)
{
  CALL("TPTP::addRationalConstant");

  size_t i = name.find_first_of("/");
  ASS(i != vstring::npos);
  try {
    return env.signature->addRationalConstant(name.substr(0,i),
					      name.substr(i+1),
					      defaultSort);
  }
  catch(Kernel::ArithmeticException&) {
    bool added;
    unsigned fun = env.signature->addFunction(name,0,added,true /* overflown constant*/);
    if (added) {
      overflow.insert(name);
      Signature::Symbol* symbol = env.signature->getFunction(fun);
      symbol->setType(OperatorType::getConstantsType(defaultSort ? (unsigned)Sorts::DefaultSorts::SRT_DEFAULT : (unsigned)Sorts::DefaultSorts::SRT_RATIONAL));
    }
    else if (!overflow.contains(name)) {
      USER_ERROR((vstring)"Cannot use name '" + name + "' as an atom name since it collides with an rational number");
    }
    return fun;
  }
} // TPTP::addRationalConstant

/**
 * Add an real constant by reading it from the vstring name.
 * If it overflows, create an uninterpreted constant of the
 * real type and the name 'name'. Check that the name of the constant
 * does not collide with user-introduced names of uninterpreted constants.
 * @since 22/07/2011 Manchester
 * @since 03/05/2013 train Manchester-London, fix to handle difference
 *    between treating rationals using fof() and tff()
 * @author Andrei Voronkov
 */
unsigned TPTP::addRealConstant(const vstring& name, Set<vstring>& overflow, bool defaultSort)
{
  CALL("TPTP::addRealConstant");

  try {
    return env.signature->addRealConstant(name,defaultSort);
  }
  catch(Kernel::ArithmeticException&) {
    bool added;
    unsigned fun = env.signature->addFunction(name,0,added,true /* overflown constant*/);
    if (added) {
      overflow.insert(name);
      Signature::Symbol* symbol = env.signature->getFunction(fun);
      symbol->setType(OperatorType::getConstantsType(defaultSort ? (unsigned)Sorts::DefaultSorts::SRT_DEFAULT : (unsigned)Sorts::DefaultSorts::SRT_REAL));
    }
    else if (!overflow.contains(name)) {
      USER_ERROR((vstring)"Cannot use name '" + name + "' as an atom name since it collides with an real number");
    }
    return fun;
  }
} // TPTP::addRealConstant


/**
 * Add an uninterpreted constant by reading it from the vstring name.
 * Check that the name of the constant does not collide with uninterpreted constants
 * created by the parser from overflown input numbers.
 * @since 22/07/2011 Manchester
 */
unsigned TPTP::addUninterpretedConstant(const vstring& name, Set<vstring>& overflow, bool& added)
{
  CALL("TPTP::addUninterpretedConstant");

  if (overflow.contains(name)) {
    USER_ERROR((vstring)"Cannot use name '" + name + "' as an atom name since it collides with an integer number");
  }
  return env.signature->addFunction(name,0,added);
} // TPTP::addUninterpretedConstant

/**
 * Associate name @b name with unit @b unit
 * Each formula can have its name assigned at most once
 */
void TPTP::assignAxiomName(const Unit* unit, vstring& name)
{
  CALL("Parser::assignAxiomName");
  ALWAYS(_axiomNames.insert(unit->number(), name));
} // TPTP::assignAxiomName

/**
 * If @b unit has a name associated, assign it into @b result,
 * and return true; otherwise return false
 */
bool TPTP::findAxiomName(const Unit* unit, vstring& result)
{
  CALL("Parser::findAxiomName");
  return _axiomNames.find(unit->number(), result);
} // TPTP::findAxiomName

/**
 * Process vampire() declaration
 * @since 25/08/2009 Redmond
 */
void TPTP::vampire()
{
  CALL("TPTP::vampire");

  consumeToken(Tag::T_LPAR);
  vstring nm = name();

  if (nm == "option") { // vampire(option,age_weight_ratio,3)
    consumeToken(Tag::T_COMMA);
    vstring opt = name();
    consumeToken(Tag::T_COMMA);
    Token tok = getTok(0);
    switch (tok.tag) {
    case Tag::T_INT:
    case Tag::T_REAL:
    case Tag::T_NAME:
      env.options->set(opt,tok.content);
      resetToks();
      break;
    default:
      PARSE_ERROR("either atom or number expected as a value of a Vampire option",tok);
    }
  }
  // Allows us to insert LaTeX templates for predicate and function symbols
  else if(nm == "latex"){
    consumeToken(Tag::T_COMMA);
    vstring kind = name();
    bool pred;
    if (kind == "predicate") {
      pred = true;
    }
    else if (kind == "function") {
      pred = false;
    }
    else {
      PARSE_ERROR("either 'predicate' or 'function' expected",getTok(0));
    }
    consumeToken(Tag::T_COMMA);
    vstring symb = name();
    consumeToken(Tag::T_COMMA);
    Token tok = getTok(0);
    if (tok.tag != Tag::T_INT) {
      PARSE_ERROR("a non-negative integer (denoting arity) expected",tok);
    }
    unsigned arity;
    if (!Int::stringToUnsignedInt(tok.content,arity)) {
      PARSE_ERROR("a number denoting arity expected",tok);
    }
    resetToks();
    consumeToken(Tag::T_COMMA);
    tok = getTok(0);
    if(tok.tag != Tag::T_STRING){
      PARSE_ERROR("a template string expected",tok);
    }
    vstring temp = tok.content;
    resetToks();
    if(pred){
      consumeToken(Tag::T_COMMA);
      vstring pol= name();
      bool polarity;
      if(pol=="true"){polarity=true;}else if(pol=="false"){polarity=false;}
      else{ PARSE_ERROR("polarity expected (true/false)",getTok(0)); }
      unsigned f = env.signature->addPredicate(symb,arity);
      theory->registerLaTeXPredName(f,polarity,temp);
    }
    else{
      unsigned f = env.signature->addFunction(symb,arity);
      theory->registerLaTeXFuncName(f,temp);
    }
  }
  else if (nm == "symbol") {
    consumeToken(Tag::T_COMMA);
    vstring kind = name();
    bool pred;
    if (kind == "predicate") {
      pred = true;
    }
    else if (kind == "function") {
      pred = false;
    }
    else {
      PARSE_ERROR("either 'predicate' or 'function' expected",getTok(0));
    }
    consumeToken(Tag::T_COMMA);
    vstring symb = name();
    consumeToken(Tag::T_COMMA);
    Token tok = getTok(0);
    if (tok.tag != Tag::T_INT) {
      PARSE_ERROR("a non-negative integer (denoting arity) expected",tok);
    }
    unsigned arity;
    if (!Int::stringToUnsignedInt(tok.content,arity)) {
      PARSE_ERROR("a number denoting arity expected",tok);
    }
    resetToks();
    consumeToken(Tag::T_COMMA);
    Color color;
    bool skip = false;
    vstring lr = name();
    if (lr == "left") {
      color=COLOR_LEFT;
    }
    else if (lr == "right") {
      color=COLOR_RIGHT;
    }
    else if (lr == "skip") {
      skip = true;
    }
    else {
      PARSE_ERROR("'left', 'right' or 'skip' expected",getTok(0));
    }
    env.colorUsed = true;
    Signature::Symbol* sym = pred
                             ? env.signature->getPredicate(env.signature->addPredicate(symb,arity))
                             : env.signature->getFunction(env.signature->addFunction(symb,arity));
    if (skip) {
      sym->markSkip();
    }
    else {
      sym->addColor(color);
    }
  }
  else if (nm == "left_formula") { // e.g. vampire(left_formula)
    _currentColor = COLOR_LEFT;
  }
  else if (nm == "right_formula") { // e.g. vampire(left_formula)
    _currentColor = COLOR_RIGHT;
  }
  else if (nm == "end_formula") { // e.g. vampire(left_formula)
    _currentColor = COLOR_TRANSPARENT;
  }
  else if (nm == "model_check"){
    consumeToken(Tag::T_COMMA);
    vstring command = name();
    if(command == "formulas_start"){
      _modelDefinition = false;
    }
    else if(command == "formulas_end"){
      // do nothing
    }
    else if(command == "model_start"){
      _modelDefinition = true;
    }
    else if(command == "model_end"){
      _modelDefinition = false;
    }
    else USER_ERROR("Unknown model_check command");
  }
  else {
    USER_ERROR((vstring)"Unknown vampire directive: "+nm);
  }
  consumeToken(Tag::T_RPAR);
  consumeToken(Tag::T_DOT);
} // vampire

#if VDEBUG
const char* TPTP::toString(State s)
{
  switch (s) {
  case State::UNIT_LIST:
    return "UNIT_LIST";
  case State::CNF:
    return "CNF";
  case State::FOF:
    return "FOF";
  case State::VAMPIRE:
    return "VAMPIRE";
  case State::FORMULA:
    return "FORMULA";
  case State::END_FOF:
    return "END_FOF";
  case State::SIMPLE_FORMULA:
    return "SIMPLE_FORMULA";
  case State::END_FORMULA:
    return "END_FORMULA";
  case State::FORMULA_INSIDE_TERM:
    return "FORMULA_INSIDE_TERM";
  case State::END_FORMULA_INSIDE_TERM:
    return "END_FORMULA_INSIDE_TERM";
  case State::END_TERM_AS_FORMULA:
    return "END_TERM_AS_FORMULA";
  case State::VAR_LIST:
    return "VAR_LIST";
  case State::FUN_APP:
    return "FUN_APP";
  case State::FORMULA_INFIX:
    return "FORMULA_INFIX";
  case State::ARGS:
    return "ARGS";
  case State::TERM:
    return "TERM";
  case State::TERM_INFIX:
    return "TERM_INFIX";
  case State::END_TERM:
    return "END_TERM";
  case State::TAG:
    return "TAG";
  case State::INCLUDE:
    return "INCLUDE";
  case State::END_EQ:
    return "END_EQ";
  case State::TFF:
    return "TFF";
  case State::THF:
    return "THF";
  case State::TYPE:
    return "TYPE";
  case State::END_TFF:
    return "END_TFF";
  case State::END_TYPE:
    return "END_TYPE";
  case State::SIMPLE_TYPE:
    return "SIMPLE_TYPE";
  case State::END_THEORY_FUNCTION:
    return "END_THEORY_FUNCTION";
  case State::END_ARGS:
    return "END_ARGS";
  case State::MID_EQ:
    return "MID_EQ";
  case State::LET_TYPE:
    return "LET_TYPE";
  case State::END_LET_TYPES:
    return "END_LET_TYPES";
  case State::DEFINITION:
    return "DEFINITION";
  case State::MID_DEFINITION:
    return "MID_DEFINITION";
  case State::END_DEFINITION:
    return "END_DEFINITION";
  case State::SYMBOL_DEFINITION:
    return "SYMBOL_DEFINITION";
  case State::TUPLE_DEFINITION:
    return "TUPLE_DEFINITION";
  case State::END_LET:
    return "END_LET";
  case State::UNBIND_VARIABLES:
    return "UNBIND_VARIABLES";
  case State::END_ITE:
    return "END_ITE";
  case State::END_TUPLE:
    return "END_TUPLE";
  default:
    cout << (int)s << "\n";
    ASS(false);
    break;
  }
}
#endif

#ifdef DEBUG_SHOW_STATE
void TPTP::printStacks() {
  Stack<State>::Iterator stit(_states);
  cout << "States:";
  if   (!stit.hasNext()) cout << " <empty>";
  while (stit.hasNext()) cout << " " << toString(stit.next());
  cout << endl;

  Stack<Type*>::Iterator tyit(_types);
  cout << "Types:";
  if   (!tyit.hasNext()) cout << " <empty>";
  while (tyit.hasNext()) cout << " " << tyit.next()->tag();
  cout << endl;

  Stack<int>::Iterator cit(_connectives);
  cout << "Connectives:";
  if   (!cit.hasNext()) cout << " <empty>";
  while (cit.hasNext()) cout << " " << cit.next();
  cout << endl;

  Stack<vstring>::Iterator sit(_strings);
  cout << "Strings:";
  if   (!sit.hasNext()) cout << " <empty>";
  while (sit.hasNext()) cout << " " << sit.next();
  cout << endl;

  Stack<int>::Iterator iit(_ints);
  cout << "Ints:";
  if   (!iit.hasNext()) cout << " <empty>";
  while (iit.hasNext()) cout << " " << iit.next();
  cout << endl;

  Stack<bool>::Iterator bit(_bools);
  cout << "Bools:";
  if   (!bit.hasNext()) cout << " <empty>";
  while (bit.hasNext()) cout << " " << bit.next();
  cout << endl;

  Stack<TermList>::Iterator tit(_termLists);
  cout << "Terms:";
  if   (!tit.hasNext()) cout << " <empty>";
  while (tit.hasNext()) cout << " " << tit.next().toString();
  cout << endl;

  Stack<Formula*>::Iterator fit(_formulas);
  cout << "Formulas:";
  if   (!fit.hasNext()) cout << " <empty>";
  while (fit.hasNext()) cout << " " << fit.next()->toString();
  cout << endl;

  Stack<Formula::VarList*>::Iterator vlit(_varLists);
  cout << "Var lists:";
  if   (!vlit.hasNext()) cout << " <empty>";
  while (vlit.hasNext()) {
    Formula::VarList::Iterator vit(vlit.next());
    if (!vit.hasNext()) {
      cout << " <empty>";
    } else {
      cout << " [";
      while (vit.hasNext()) {
        cout << vit.next();
        if (vit.hasNext()) cout << " ";
      };
      cout << "]";
    }
  }
  cout << endl;

  Map<int, SortList*>::Iterator vsit(_variableSorts);
  cout << "Variables sorts:";
  if   (!vsit.hasNext()) cout << "<empty>";
  int vsitKey;
  SortList* vsitVal;
  while (vsit.hasNext()) {
    vsit.next(vsitKey, vsitVal);
    cout << " {" << vsitKey << " ->";
    SortList::Iterator slit(vsitVal);
    if   (!slit.hasNext()) cout << " <empty>";
    while (slit.hasNext()) cout << " " << env.sorts->sortName(slit.next());
    cout << "}";
  }
  cout << endl;

  Stack<SortList*>::Iterator slsit(_sortLists);
  cout << "Sort lists: ";
  if   (!slsit.hasNext()) cout << "<empty>";
  while (slsit.hasNext()) {
    SortList* sl = slsit.next();
    SortList::Iterator slit(sl);
    if   (!slit.hasNext()) cout << "<empty>";
    while (slit.hasNext()) cout << env.sorts->sortName(slit.next()) << " ";
    cout << ";";
  }
  cout << endl;

  Stack<TheoryFunction>::Iterator tfit(_theoryFunctions);
  cout << "Theory functions: ";
  if   (!tfit.hasNext()) cout << " <empty>";
  while (tfit.hasNext()) cout << " " << tfit.next();
  cout << endl;

  Stack<LetSymbols>::Iterator lfsit(_letSymbols);
  cout << "Let functions scopes: ";
  if (!lfsit.hasNext()) cout << "<empty>";
  while (lfsit.hasNext()) {
    LetSymbols lfs = lfsit.next();
    LetSymbols::Iterator sit(lfs);
    if (!sit.hasNext()) {
      cout << "<empty>";
    } else {
      unsigned i = lfs.length();
      while (sit.hasNext()) {
        LetSymbol f    = sit.next();
        vstring name     = f.first.first;
        unsigned arity   = f.first.second;
        unsigned symbol  = f.second.first;
        bool isPredicate = f.second.second;

        vstring symbolName = isPredicate ? env.signature->predicateName(symbol)
                                         : env.signature->functionName (symbol);

        cout << name << "/" << arity << " -> " << symbolName;
        if (--i > 0) {
          cout << ", ";
        }
      };
    }
  }
  cout << endl;

  Stack<LetSymbols>::Iterator clfsit(_letTypedSymbols);
  cout << "Current let functions scopes: ";
  if (!clfsit.hasNext()) cout << "<empty>";
  while (clfsit.hasNext()) {
    LetSymbols lfs = clfsit.next();
    LetSymbols::Iterator csit(lfs);
    if (!csit.hasNext()) {
      cout << "<empty>";
    } else {
      unsigned i = lfs.length();
      while (csit.hasNext()) {
        LetSymbol f    = csit.next();
        vstring name     = f.first.first;
        unsigned arity   = f.first.second;
        unsigned symbol  = f.second.first;
        bool isPredicate = f.second.second;

        vstring symbolName = isPredicate ? env.signature->predicateName(symbol)
                                         : env.signature->functionName (symbol);

        cout << name << "/" << arity << " -> " << symbolName;
        if (--i > 0) {
          cout << ", ";
        }
      };
    }
  }
  cout << endl;

  Stack<LetDefinitions>::Iterator lbsit(_letDefinitions);
  cout << "Let definitions: ";
  if (!lbsit.hasNext()) cout << "<empty>";
  while (lbsit.hasNext()) {
    LetDefinitions lbs = lbsit.next();
    LetDefinitions::Iterator lbit(lbs);
    if (!lbit.hasNext()) {
      cout << "<empty>";
    } else {
      cout << "[";
      unsigned i = (unsigned)lbs.length();
      while (lbit.hasNext()) {
        LetSymbolReference ref = lbit.next();
        unsigned symbol = SYMBOL(ref);
        bool isPredicate = IS_PREDICATE(ref);
        vstring symbolName = isPredicate ? env.signature->predicateName(symbol)
                                         : env.signature->functionName (symbol);
        cout << symbolName;
        if (--i > 0) {
          cout << ", ";
        }
      }
      cout << "]";
    }
  }
  cout << endl;
}
#endif
