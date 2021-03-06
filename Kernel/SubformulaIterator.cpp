
/*
 * File SubformulaIterator.cpp.
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
 * @file SubformulaIterator.cpp
 * Implements a class SubformulaIterator that iterates
 * over subformulas in formula lists, and formulas.
 *
 * @since 06/01/2004 Manchester
 * @since 02/06/2007 Manchester changed to new datastructures
 * @since 06/05/2015 Gothenburg in order to support FOOL, we need to search for formulas inside terms as well
 */

#include "Debug/Tracer.hpp"

#include "SubformulaIterator.hpp"

namespace Kernel {

/**
 * Elements strong information, used internally in subformula iterators.
 */
class SubformulaIterator::Element {
public:
  Element (FormulaList* list, int polarity, Element* rest)
    : _tag(Tag::FORMULA_LIST),
      _formulaList(list),
      _polarity(polarity),
      _rest(rest)
  {}
  Element (Formula* f, int polarity, Element* rest)
    : _tag(Tag::FORMULA),
      _formula(f),
      _polarity(polarity),
      _rest(rest)
  {}
  Element (TermList* ts, int polarity, Element* rest)
    : _tag(Tag::TERM_LIST),
      _termList(ts),
      _polarity(polarity),
      _rest(rest)
  {}
  Element (Term* t, int polarity, Element* rest)
    : _tag(Tag::TERM),
      _term(t),
      _polarity(polarity),
      _rest(rest)
  {}
  enum class Tag {
    FORMULA_LIST,
    FORMULA,
    TERM_LIST,
    TERM
  };
  Tag _tag;
  union{
    FormulaList* _formulaList;
    Formula* _formula;
    TermList* _termList;
    Term* _term;
  };
  int _polarity;
  Element* _rest;

  CLASS_NAME(SubformulaIterator::Element);
  USE_ALLOCATOR(SubformulaIterator::Element);
};


/**
 * Build an iterator over t.
 * @since 06/01/2004 Manchester
 */
SubformulaIterator::SubformulaIterator (Formula* f)
  : _current(f),
    _currentPolarity(1),
    _reserve(0)
{
} // SubformulaIterator::SubformulaIterator


/**
 * Build an iterator over of ts.
 * @since 06/01/2004 Manchester
 */
SubformulaIterator::SubformulaIterator (FormulaList* ts)
  : _current(0),
    _reserve(new Element(ts,1,0))
{
} // SubformulaIterator::SubformulaIterator


/**
 * True if there the next subformula.
 * @since 06/01/2004 Manchester
 * @since 22/08/2004 Torrevieja, a bug fixed causing reserve formulas
 *                   to be ignored
 * @since 06/05/2015 Gothenburg look inside terms in search for formulas, used by FOOL
 */
bool SubformulaIterator::hasNext ()
{
  CALL("SubformulaIterator::hasNext");

  if (_current) {
    return true;
  }

  // try to set _current
  while (_reserve) {
    switch (_reserve->_tag) {
      case Element::Tag::FORMULA_LIST: {
        FormulaList *first = _reserve->_formulaList;
        if (FormulaList::isEmpty(first)) {
          Element *rest = _reserve->_rest;
          delete _reserve;
          _reserve = rest;
          break;
        } else { // first is non-empty
          _current = first->head();
          _currentPolarity = _reserve->_polarity;
          _reserve->_formulaList = first->tail();
          return true;
        }
      }

      case Element::Tag::FORMULA: {
        _current = _reserve->_formula;
        _currentPolarity = _reserve->_polarity;
        Element *rest = _reserve->_rest;
        delete _reserve;
        _reserve = rest;
        return true;
      }

      case Element::Tag::TERM_LIST: {
        TermList* first = _reserve->_termList;
        if (!first->isTerm()) {
          Element *rest = _reserve->_rest;
          delete _reserve;
          _reserve = rest;
        } else { // first is non-empty
          _reserve->_termList = first->next();
          _reserve = new Element(first->term(), _reserve->_polarity, _reserve);
        }
        break;
      }

      case Element::Tag::TERM: {
        Term* term = _reserve->_term;
        int polarity = _reserve->_polarity;
        Element* rest = new Element(term->args(), polarity, _reserve->_rest);
        if (!term->isSpecial()) {
          delete _reserve;
          _reserve = rest;
          break;
        }

        switch (term->functor()) {
          case Term::SF_ITE: {
            _current = term->getSpecialData()->getCondition();
            _currentPolarity = polarity;
            delete _reserve;
            _reserve = rest;
            return true;
          }
          case Term::SF_LET: {
            delete _reserve;
            TermList binding = term->getSpecialData()->getBinding();
            if (!binding.isTerm()) {
              _reserve = rest;
            } else {
              // TODO: should be 1 instead of polarity?
              _reserve = new Element(binding.term(), polarity, rest);
            }
            break;
          }
          case Term::SF_LET_TUPLE: {
            delete _reserve;
            TermList binding = term->getSpecialData()->getBinding();
            if (!binding.isTerm()) {
              _reserve = rest;
            } else {
              // TODO: should be 1 instead of polarity?
              _reserve = new Element(binding.term(), polarity, rest);
            }
            break;
          }
          case Term::SF_FORMULA: {
            _current = term->getSpecialData()->getFormula();
            _currentPolarity = polarity;
            delete _reserve;
            _reserve = rest;
            return true;
          }
          case Term::SF_TUPLE: {
            delete _reserve;
            Term* tupleTerm = term->getSpecialData()->getTupleTerm();
            // TODO: should be 1 instead of polarity?
            _reserve = new Element(tupleTerm, polarity, rest);
            break;
          }
#if VDEBUG
          default:
            ASSERTION_VIOLATION;
#endif
        }
        break;
      }

#if VDEBUG
      default:
        ASSERTION_VIOLATION;
#endif
    }
  }
  // _reserve is empty
  return false;
} // SubformulaIterator::hasNext


/**
 * Return the next subformula.
 */
Formula* SubformulaIterator::next ()
{
  CALL("SubformulaIterator::next/0");

  int dummy;
  return next(dummy);
}

/**
 * Return the next subformula, into @c resultPolarity assign the polarity
 * of the returned subformula in the iterated formula.
 *
 * @since 06/01/2004 Manchester
 * @since 11/12/2004 Manchester, true and false added
 * @since 06/05/2015 Gothenburg look inside terms in search for formulas, used by FOOL
 */
Formula* SubformulaIterator::next (int& resultPolarity)
{
  CALL("SubformulaIterator::next/1");

  Formula* result = _current;
  resultPolarity = _currentPolarity;

  switch (result->connective()) {
  case Connective::LITERAL:
    _reserve = new Element(result->literal()->args(), resultPolarity, _reserve);
    _current = 0;
    break;

  case Connective::_TRUE:
  case Connective::_FALSE:
  case Connective::NAME:
    _current = 0;
    break;

  case Connective::AND:
  case Connective::OR:
    _reserve = new Element(result->args(), resultPolarity, _reserve);
    _current = 0;
    break;

  case Connective::IMP:
    _current = result->left();
    _currentPolarity = -resultPolarity;
    _reserve = new Element(result->right(), resultPolarity, _reserve);
    break;

  case Connective::IFF:
  case Connective::XOR:
    _current = result->left();
    _currentPolarity = 0;
    _reserve = new Element(result->right(), 0, _reserve);
    break;

  case Connective::NOT:
    _current = result->uarg();
    _currentPolarity = -resultPolarity;
    break;

  case Connective::FORALL:
  case Connective::EXISTS:
    _current = result->qarg();
    _currentPolarity = resultPolarity;
    break;

  case Connective::BOOL_TERM: {
    _current = 0;
    TermList ts = result->getBooleanTerm();
    if (!ts.isVar()) {
      // here we rely on the fact that TermList can only be either a variable, a $ite or a $let
      _reserve = new Element(ts.term(), resultPolarity, _reserve);
    }
    break;
  }

#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }

  return result;
} // SubformulaIterator::next


/**
 * Destroy the iterator.
 */
SubformulaIterator::~SubformulaIterator ()
{
  while (_reserve) {
    Element* next = _reserve->_rest;
    delete _reserve;
    _reserve = next;
  }
} // SubformulaIterator::~SubformulaIterator

}
