
/*
 * File LispLexer.cpp.
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
 * @file LispLexer.cpp
 * Implements class LispLexer
 *
 * @since 14/07/2004 Turku
 */

#include <cstring>

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"

#include "Lib/Exception.hpp"

#include "LispLexer.hpp"

using namespace Shell;

/**
 * Initialise a lexer.
 * @since 25/08/2009 Redmond
 */
LispLexer::LispLexer (istream& in)
  : Lexer (in)
{
} // LispLexer::LispLexer


/**
 * Skip all whitespaces and comments. After this operation either
 * _lastCharacter will be not whitespace or _eof will be set to true.
 * @since 25/08/2009 Redmond
 */
void LispLexer::skipWhiteSpacesAndComments ()
{
  CALL("LispLexer::skipWhiteSpacesAndComments");

  bool comment = false;
  while (! _eof) {
    switch (_lastCharacter) {
    case ' ':
    case '\t':
    case '\r':
    case '\f':
      readNextChar();
      break;

    case '\n': // end-of-line comment (if any) finished
      comment = false;
      readNextChar();
      break;

    case ';': // Lisp comment sign
      comment = true;
      readNextChar();
      break;

    default:
      if (comment) {
	readNextChar();
	break;
      }
      return;
    }
  }
} // LispLexer::skipWhiteSpacesAndComments

/**
 * Read the next token.
 * @since 26/08/2009 Redmond
 */
void LispLexer::readToken (Token& token)
{
  CALL("LispLexer::readToken");

  skipWhiteSpacesAndComments();
  _charCursor = 0;

  if (_eof) {
    token.tag = TokenType::TT_EOF;
    token.text = "";
    return;
  }
  token.line = _lineNumber;

  switch (_lastCharacter) {
  case '(':
    token.tag = TokenType::TT_LPAR;
    saveLastChar();
    saveTokenText(token);
    readNextChar();
    break;
  case ')':
    token.tag = TokenType::TT_RPAR;
    saveLastChar();
    saveTokenText(token);
    readNextChar();
    break;
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
    readNumber(token);
    return;
  case '"':
    readQuotedString(token, '"', '"','"');
    return;
  case '|':
    readQuotedString(token, '|', '|','\\');
    return;
  case '{':
    readQuotedString(token, '{', '}','\\');
    return;
  default:
    readName(token);
    token.tag = TokenType::TT_NAME;
    return;
  }
} // LispLexer::readToken

/**
 * Read a name. No check is made about the current character
 * @since 26/08/2009 Redmond
 */
void LispLexer::readName (Token& token)
{
  CALL("LispLexer::readName");

  saveLastChar();

  while (readNextChar()) {
    switch(_lastCharacter) {
    case ' ':
    case '\t':
    case '\r':
    case '\f':
    case '\n':
    case ';':
    case ')':
    case '(':
    case '{':
    case '}':
      // token parsed
      saveTokenText(token);
      return;
    default:
      saveLastChar();
      break;
    }
  }

  // no more characters, token parsed
  saveTokenText(token);
} // LispLexer::readName

/**
 * Read a quoted string.
 * @since 26/08/2009 Redmond
 *
 * Added escapeChar to support smtlib string literals that use " to escape " 
 * @since May 2020 @author Giles
 */
void LispLexer::readQuotedString(Token& token, char opening, char closing, char escapeChar)
{
  CALL("LispLexer::readQuotedString");

  bool escape=false;
  saveLastChar();

  while (readNextChar()) {
    if (_lastCharacter == escapeChar && !escape && closing != escapeChar) {
      escape=true;
    }
    else if (_lastCharacter == closing && !escape) {
      if(closing == escapeChar && lookAhead() == closing){
        readNextChar();
      }
      else{
        saveLastChar();
        saveTokenText(token);
        readNextChar();
        token.tag = TokenType::TT_NAME;
        return;
      }
    }
    else {
      if (escape && _lastCharacter!=closing && _lastCharacter!=escapeChar) {
	throw LexerException((vstring)"invalid escape sequence in quoted string ", *this);
      }
      escape=false;
      saveLastChar();
    }
  }
  throw LexerException((vstring)"file ended while reading quoted string ", *this);
} // LispLexer::readQuotedString



