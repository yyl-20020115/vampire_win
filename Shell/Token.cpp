
/*
 * File Token.cpp.
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
 * @file Token.cpp
 * Implements class Token
 *
 * @since 25/07/2004 Torrevieja
 */

#include "Debug/Assertion.hpp"
#include "Token.hpp"

using namespace std;

namespace Shell {

/**
 * Return a text representation of a token.
 * 
 * @since 25/07/2004 Torrevieja
 */
Lib::vstring Token::toString (TokenType tt)
{
  switch (tt) {
  case TokenType::TT_INTEGER:
    return "<integer>";
  case TokenType::TT_REAL:
    return "<real>";
  case TokenType::TT_ROW_VARIABLE:
    return "<row variable>";
  case TokenType::TT_STRING:
    return "<string>";
  case TokenType::TT_EOF:
    return "<end-of-file>";
  case TokenType::TT_LPAR:
    return "(";
  case TokenType:: TT_RPAR:
    return ")";
  case TokenType::TT_LBRA:
    return "[";
  case TokenType::TT_RBRA:
    return "]";
  case TokenType::TT_COMMA:
    return ",";
  case TokenType::TT_COLON:
    return ":";
  case TokenType::TT_DOT  :
    return ".";
  case TokenType::TT_AND:
    return "&";
  case TokenType::TT_NOT:
    return "~";
  case TokenType::TT_OR:
    return "|";
  case TokenType::TT_IFF:
    return "<=>";
  case TokenType::TT_IMP:
    return "=>";
  case TokenType::TT_XOR:
    return "<~>";
  case TokenType::TT_FORALL:
    return "!";
  case TokenType::TT_EXISTS:
    return "?";
  case TokenType::TT_PP:
    return "++";
  case TokenType::TT_MM:
    return "--";
  case TokenType::TT_EQUAL:
    return "=";
  case TokenType::TT_NAME:
    return "<name>";
  case TokenType::TT_VAR:
    return "<variable>";
  case TokenType::TT_INPUT_FORMULA: 
    return "input_formula";
  case TokenType::TT_INPUT_CLAUSE:
    return "input_clause";
  case TokenType::TT_INCLUDE:
    return "include";
  case TokenType::TT_GREATER_THAN:
    return ">";
  case TokenType::TT_LESS_THAN:
    return "<";
  case TokenType::TT_END_OF_EMPTY_TAG:
    return "/>";
  case TokenType::TT_TEXT:
    return "<text>";
  case TokenType::TT_CLOSING_TAG:
    return "</";
  case TokenType::TT_PLUS:
    return "plus";
  case TokenType::TT_MINUS:
    return "minus";
  case TokenType::TT_DISTINCT:
    return "distinct";
  case TokenType::TT_LBLPOS:
    return "LBLPOS";
  case TokenType::TT_LBLNEG:
    return "LBLNEG";
  case TokenType::TT_LEMMA:
    return "LEMMA";
  case TokenType::TT_PROOF:
    return "PROOF";
  case TokenType::TT_PUSH:
    return "PUSH";
  case TokenType::TT_POP:
    return "POP";
  case TokenType::TT_PATTERN:
    return "PATTERN";
  case TokenType::TT_DEFPRED:
    return "DEFPRED";
  case TokenType::TT_DEFPREDMAP:
    return "DEFPREDMAP";
  case TokenType::TT_PROMPTON:
    return "PROMPTON";
  case TokenType::TT_PROMPTOFF:
    return "PROMPTOFF";
  case TokenType::TT_ORDER:
    return "ORDER";
  case TokenType::TT_EXPLIES:
    return "EXPLIES";
  case TokenType::TT_ADD_CONSTANT:
    return "ADD_CONSTANT";
  case TokenType::TT_ADD_VARIABLE:
    return "ADD_VARIABLE";
  case TokenType::TT_ADD_DEF_VARIABLE:
    return "ADD_DEF_VARIABLE";
  case TokenType::TT_ADD_EQUAL:
    return "ADD_EQUAL";
  case TokenType::TT_ADD_BIT_NOT:
    return "ADD_BIT_NOT";
  case TokenType::TT_ADD_BIT_AND:
    return "ADD_BIT_AND";
  case TokenType::TT_ADD_BIT_OR:
    return "ADD_BIT_OR";
  case TokenType::TT_ADD_BIT_XOR:
    return "ADD_BIT_XOR";
  case TokenType::TT_ADD_LOGICAL_NOT:
    return "ADD_LOGICAL_NOT";
  case TokenType::TT_ADD_LOGICAL_AND:
    return "ADD_LOGICAL_AND";
  case TokenType::TT_ADD_LOGICAL_OR:
    return "ADD_LOGICAL_OR";
  case TokenType::TT_ADD_LOGICAL_IMPLIES:
    return "ADD_LOGICAL_IMPLIES";
  case TokenType::TT_ADD_LESS_THAN:
    return "ADD_LESS_THAN";
  case TokenType::TT_ADD_LESS_EQUAL:
    return "ADD_LESS_EQUAL";
  case TokenType::TT_ADD_GREATER_THAN:
    return "ADD_GREATER_THAN";
  case TokenType::TT_ADD_GREATER_EQUAL:
    return "ADD_GREATER_EQUAL";
  case TokenType::TT_ADD_SUB:
    return "ADD_SUB";
  case TokenType::TT_ADD_SUM:
    return "ADD_SUM";
  case TokenType::TT_ADD_MUL:
    return "ADD_MUL";
  case TokenType::TT_ADD_DIV:
    return "ADD_DIV";
  case TokenType::TT_ADD_MOD:
    return "ADD_MOD";
  case TokenType::TT_ADD_LSHIFT:
    return "ADD_LSHIFT";
  case TokenType::TT_ADD_RSHIFT:
    return "ADD_RSHIFT";
  case TokenType::TT_ADD_LSHIFT1:
    return "ADD_LSHIFT1";
  case TokenType::TT_ADD_RSHIFT1:
    return "ADD_RSHIFT1";
  case TokenType::TT_ADD_ASSIGNMENT:
    return "ADD_ASSIGNMENT";
  case TokenType::TT_ADD_CONCAT_OP:
    return "ADD_CONCAT_OP";
  case TokenType::TT_ADD_CONDITION:
    return "ADD_CONDITION";
  case TokenType::TT_ADD_ZERO_EXTENSION:
    return "ADD_ZERO_EXTENSION";
  case TokenType::TT_ADD_SIGN_EXTENSION:
    return "ADD_SIGN_EXTENSION";
  case TokenType::TT_ADD_DEF_UF:
    return "ADD_DEF_UF";
  case TokenType::TT_ADD_UF_ARG:
    return "ADD_UF_ARG";
  case TokenType::TT_ADD_UF_TERM_ARG:
    return "ADD_UF_TERM_ARG";
  case TokenType::TT_ADD_LATCH:
    return "ADD_LATCH";
  case TokenType::TT_ADD_UF_TERM:
    return "ADD_UF_TERM";
  case TokenType::TT_ADD_ASSUMPTION:
    return "ADD_ASSUMPTION";
  case TokenType::TT_TRUE:
    return "TRUE";
  case TokenType::TT_FALSE:
    return "FALSE";
  case TokenType::TT_NEQ:
    return "!=";
  case TokenType::TT_CNF:
    return "cnf";
  case TokenType::TT_QUOTED_STRING:
    return "QUOTED_STRING";
  case TokenType::TT_GEQ:
    return ">=";
  case TokenType::TT_LEQ:
    return "<=";
  case TokenType::TT_ATTRIBUTE:
    return "<attribute>";
  case TokenType::TT_ARITH:
    return "<arith>";
  case TokenType::TT_USER:
    return "<user value>";
    
#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }
} // Token::toString

}
