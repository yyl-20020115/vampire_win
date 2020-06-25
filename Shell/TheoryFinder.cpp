
/*
 * File TheoryFinder.cpp.
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
 * @file TheoryFinder.cpp
 * Implements class TheoryFinder for finding theories in the input problems.
 *
 * @since 09/06/2004 Manchester
 * @since 09/07/2008 Linz, changed to new datastructures
 * @since 28/07/2008 flight Linz airport and train Manchester-London, reimplemented completely
 *                   and simplified
 */

// #include "CodeGenerator.hpp"

#include "Debug/Tracer.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Term.hpp"

#include "Property.hpp"
#include "TheoryFinder.hpp"

// Set this to 1 to make Vampire output all matching steps
#define TRACE_FINDER 0
// Set this to 1 to make Vampire output found matches
#define SHOW_FOUND 0

using namespace Lib;
using namespace Shell;
using namespace Kernel;

/**
 * Build a new theory finder.
 * @since 09/06/2004 Manchester
 */
TheoryFinder::TheoryFinder (const UnitList* units,Property* property)
  : _units(units),
    _property(property)
{
  CALL("TheoryFinder::TheoryFinder");
} // TheoryFinder::TheoryFinder

/**
 * @since 09/06/2004 Manchester
 */
TheoryFinder::~TheoryFinder ()
{
  CALL("TheoryFinder::~TheoryFinder");
} // TheoryFinder::TheoryFinder

/**
 * @since 09/06/2004 Manchester
 * @since 18/06/2004 Manchester, added proof-search for theories
 */
int TheoryFinder::search()
{
  CALL("TheoryFinder::search");

  int found = 0;
  UnitList::Iterator uit(_units);
  while (uit.hasNext()) {
    if (matchAll(uit.next())) {
      found++;
    }
  }

  return found;
} // TheoryFinder::search


/**
 * Match against all known axioms.
 *
 * @since 09/06/2004 Manchester
 * @since 27/07/2008 Linz Airport, changed to new datastructures
 */
bool TheoryFinder::matchAll(const Unit* unit)
{
  CALL("TheoryFinder::matchAll(const Unit*)");

  // do not remove this, we need a pointer to an existing unit
  if (unit->isClause()) {
    return matchAll(static_cast<const Clause*>(unit));
  }

  return matchAll(static_cast<const FormulaUnit*>(unit)->formula());
} // TheoryFinder::matchAll

/**
 * Match clause against all known axioms.
 *
 * @since 09/06/2004 Manchester
 * @since 27/07/2008 Linz Airport, changed to new datastructures
 */
bool TheoryFinder::matchAll(const Clause* clause)
{
  CALL("TheoryFinder::matchAll(const Clause*)");

  switch (clause->length()) {
  case 1:
    return matchAll((*clause)[0]);
  case 2:
    return matchSubset(clause);
    return false;
  case 3:
     return matchFLD2(clause) ||
            matchCondensedDetachment1(clause) ||
            matchCondensedDetachment2(clause) ||
            matchExtensionality(clause);
  case 4:
    return matchFLD1(clause);
  default:
    return false;
  }
} // TheoryFinder::matchAll(const Clause* clause)

/**
 * Match formula against all known axioms.
 *
 * @since 09/06/2004 Manchester
 * @since 27/07/2008 Linz Airport, changed to new datastructures
 */
bool TheoryFinder::matchAll(const Formula* formula)
{
  CALL("TheoryFinder::matchAll (const Formula*...)");

  while (formula->connective() == Connective::FORALL) {
    formula = formula->qarg();
  }

  if (formula->connective() == Connective::LITERAL) {
    return matchAll(formula->literal());
  }

  return matchExtensionality(formula) ||
         matchSubset(formula) ||
         matchListConstructors(formula);
} // TheoryFinder::matchAll(const Formula*)

/**
 * Class for representing information stored about backtrack points
 * @since 31/07/2008 Manchester
 */
class TheoryFinder::Backtrack
{
public:
  /** code pointer */
  unsigned cp;
  /** object on which the instruction should be executed */
  const void* obj;
  /** position in the object stack */
  unsigned objPos;
}; // TheoryFinder::Backtrack

bool TheoryFinder::matchCode(const void* obj,
			     const unsigned char* code,
			     uint64_t prop)
{
  CALL("TheoryFinder::matchCode/3");
  
  bool found = matchCode(obj, code);
  if (found && prop) {
    _property->addProp(prop);
  }
  return found;
}

/**
 * Match the code against an object (a Formula,FormulaList,Literal,TermList or Term).
 *
 * @return true if succeeds
 * @since 24/06/2004 Dresden
 * @since 28/07/2008 train Manchester-London
 * @Since 30/01/2014 Refactored pure matching code to be static and public.
 *                   Previous method updating the Property field calls this method.
 */
bool TheoryFinder::matchCode(const void* obj,
			     const unsigned char* code)
{
  CALL("TheoryFinder::matchCode/2");

  Backtrack backtrack[20];
  unsigned backtrackPos = 0;

  // stack of objects to be inspected later
  const void* objects[100];
  int objectPos = 1;
  objects[0] = obj;

  // variable numbers
  unsigned vars[10];
  // function symbol numbers
  unsigned funs[10];
  // predicate symbol numbers
  unsigned preds[10];
  unsigned cp = 0; // code pointer

  // the clause, if any
  const Clause* clause;
  // the length of this clause
  int clength;
  // literal numbers to be matched by LIT i commands
  int literals[4];

 match:
  switch (code[cp]) {
  case (unsigned char)Code::END:
#if TRACE_FINDER
    cout << "Matched\n";
#endif
    return true;

  case (unsigned char)Code::NEWVAR: {
    ASS(objectPos > 0);
    obj = objects[--objectPos];
    const TermList* ts = reinterpret_cast<const TermList*>(obj);
#if TRACE_FINDER
    cout << "M: NEWVAR " << (int)code[cp+1] << ": " << ts->toString() << "\n";
#endif
    if (! ts->isVar()) {
      goto backtrack;
    }
    vars[code[cp+1]] = ts->var();
    if (! ts->next()->isEmpty()) {
      objects[objectPos++] = ts->next();
    }
    cp += 2;
    goto match;
  }

  case (unsigned)Code::NEWFUN:
  case (unsigned)Code::NEWFUN1: {
    ASS(objectPos > 0);
    obj = objects[--objectPos];
    const TermList* ts = reinterpret_cast<const TermList*>(obj);
    int funNumber = code[cp+1];
#if TRACE_FINDER
    cout << "M: NEWFUN" << (code[cp] == NEWFUN1 ? "1" : "") << ' ' << funNumber
	 << '/' << (int)code[cp+2] << ": " << ts->toString() << "\n";
#endif
    if (ts->isVar()) {
      goto backtrack;
    }
    const Term* t = ts->term();
    if (t->arity() != code[cp+2]) {
      goto backtrack;
    }
    // check that the function is new
    for (int k = funNumber - 1; k >= 0; k--) {
      if (funs[k] == t->functor()) {
	goto backtrack;
      }
    }
    funs[funNumber] = t->functor();
    if (code[cp] == (unsigned)Code::NEWFUN && ! ts->next()->isEmpty()) {
      objects[objectPos++] = ts->next();
    }
    ts = t->args();
    if (! ts->isEmpty()) {
      objects[objectPos++] = ts;
    }
    cp += 3;
    goto match;
  }

  case (unsigned)Code::NEWPRED: {
    ASS(objectPos > 0);
    obj = objects[--objectPos];
    const Literal* lit = reinterpret_cast<const Literal*>(obj);
    int predNumber = code[cp+1];
#if TRACE_FINDER
    cout << "M: NEWPRED " << predNumber << '/' << (int)code[cp+2] << ": " << lit->toString() << "\n";
#endif
    if (lit->arity() != code[cp+2]) {
      goto backtrack;
    }
    // check that the predicate is new
    for (int k = predNumber - 1; k >= 0; k--) {
      if (preds[k] == lit->functor()) {
	goto backtrack;
      }
    }
    preds[predNumber] = lit->functor();
    const TermList* ts = lit->args();
    if (! ts->isEmpty()) {
      objects[objectPos++] = ts;
    }
    cp += 3;
    goto match;
  }

  case (unsigned)Code::OLDFUN:
  case (unsigned)Code::OLDFUN1: {
    ASS(objectPos > 0);
    obj = objects[--objectPos];
    const TermList* ts = reinterpret_cast<const TermList*>(obj);
#if TRACE_FINDER
    cout << "M: OLDFUN" << (code[cp] == OLDFUN1 ? "1" : "") << " " << (int)code[cp+1]
	 << '/' << (int)code[cp+2] << ": " << ts->toString() << "\n";
#endif
    if (ts->isVar()) {
      goto backtrack;
    }
    const Term* t = ts->term();
    if (funs[code[cp+1]] != t->functor()) {
      goto backtrack;
    }
    if (code[cp] == (unsigned)Code::OLDFUN && ! ts->next()->isEmpty()) {
      objects[objectPos++] = ts->next();
    }
    ts = t->args();
    if (! ts->isEmpty()) {
      objects[objectPos++] = ts;
    }
    cp += 2;
    goto match;
  }

  case (unsigned)Code::OLDPRED: {
#if TRACE_FINDER
    cout << "M: OLDPRED " << (int)code[cp+1] << "\n";
#endif
    ASS(objectPos > 0);
    obj = objects[--objectPos];
    const Literal* lit = reinterpret_cast<const Literal*>(obj);

    if (preds[code[cp+1]] != lit->functor()) {
      goto backtrack;
    }
    const TermList* ts = lit->args();
    if (! ts->isEmpty()) {
      objects[objectPos++] = ts;
    }
    cp += 2;
    goto match;
  }

  case (unsigned)Code::OLDVAR:
  case (unsigned)Code::OLDVAR1: {
    ASS(objectPos > 0);
    obj = objects[--objectPos];
    const TermList* ts = reinterpret_cast<const TermList*>(obj);
#if TRACE_FINDER
    cout << "M: OLDVAR" << (code[cp] == OLDVAR1 ? "1" : "")
	 << ' ' << (int)code[cp+1] << ": " << ts->toString() << "\n";
#endif
    if (! ts->isVar()) {
      goto backtrack;
    }
    if (vars[code[cp+1]] != ts->var()) {
      goto backtrack;
    }
    if (code[cp] == (unsigned)Code::OLDVAR && ! ts->next()->isEmpty()) {
      objects[objectPos++] = ts->next();
    }
    cp += 2;
    goto match;
  }

  case (unsigned)Code::EQL: {
    ASS(objectPos > 0);
    obj = objects[--objectPos];
    const Literal* lit = reinterpret_cast<const Literal*>(obj);
#if TRACE_FINDER
    cout << "M: EQL: " << lit->toString() << "\n";
#endif
    if (! lit->isEquality()) {
      goto backtrack;
    }

    Backtrack& back = backtrack[backtrackPos++];
    back.cp = cp;
    back.obj = obj;
    back.objPos = objectPos;

    const TermList* ts = lit->args();
    objects[objectPos++] = ts->next();
    objects[objectPos++] = ts;

    cp++;
    goto match;
  }

  case (unsigned)Code::CLS: {
    ASS(objectPos > 0);
    obj = objects[--objectPos];
    clause = reinterpret_cast<const Clause*>(obj);
#if TRACE_FINDER
    cout << "M: CLS: " << clause->toString() << endl;
#endif
    clength = clause->length();
    cp++;
    goto match;
  }

  case (unsigned)Code::PLIT:
  case (unsigned)Code::NLIT: {
#if TRACE_FINDER
    cout << "M: LIT " << (int)code[cp+1] << "\n";
#endif
    unsigned l = code[cp+1];
    // bit field of choices for this literal
    unsigned choice = (1u << clength) - 1;
    for (int i = l-1;i >= 0;i--) {
      // remove from the choice literals already used
      choice -= 1u << literals[i];
    }
    int c = 0;
    // find the next available literal whose polarity matches
    while (c < clength) {
      // remove from the choice literals already used
      if (choice & (1 << c)) {
	if ((*clause)[c]->isPositive()) {
	  if (code[cp] == (unsigned)Code::PLIT) {
	    break;
	  }
	}
	else if (code[cp] == (unsigned)Code::NLIT) {
	  break;
	}
      }
      c++;
    }

    if (c == clength) { // no candidate found
      goto backtrack;
    }

    // create a backtrack point
    Backtrack& back = backtrack[backtrackPos++];
    back.cp = cp;
    back.objPos = objectPos;

    literals[l] = c;
    objects[objectPos++] = (*clause)[c];

    cp += 2;
    goto match;
  }

  case (unsigned)Code::CIFF:
  case (unsigned)Code::NBCIFF: {
    ASS(objectPos > 0);
    obj = objects[--objectPos];
    const Formula* f = reinterpret_cast<const Formula*>(obj);
#if TRACE_FINDER
    cout << "M: IFF: " << f->toString() << "\n";
#endif
    if (f->connective() != Connective::IFF) {
      goto backtrack;
    }

    if (code[cp] == (unsigned)Code::CIFF) {
      Backtrack& back = backtrack[backtrackPos++];
      back.cp = cp;
      back.obj = obj;
      back.objPos = objectPos;
    }

    objects[objectPos++] = f->right();
    objects[objectPos++] = f->left();

    cp++;
    goto match;
  }

    // FUTURE WORK: COR is not commutative, currently we add code for both permutations
    // it should be changed
  case (unsigned)Code::COR: {
    ASS(objectPos > 0);
    obj = objects[--objectPos];
    const Formula* f = reinterpret_cast<const Formula*>(obj);
#if TRACE_FINDER
    cout << "M: OR " << (int)code[cp+1] << ": " << f->toString() << "\n";
#endif
    if (f->connective() != Connective::OR) {
      goto backtrack;
    }
    
    // TEMPORARY, we can only handle disjunctions of length 2
    ASS(code[cp+1] == 2);

    const FormulaList* args = f->args();
    if (FormulaList::length(args) != code[cp+1]) {
      goto backtrack;
    }

    // Backtrack& back = backtrack[backtrackPos++];
    // back.cp = cp;
    // back.obj = obj;
    // back.objPos = objectPos;

    FormulaList::Iterator as(args);
    while (as.hasNext()) {
      objects[objectPos++] = as.next();
    }

    cp += 2;
    goto match;
  }

  case (unsigned)Code::CIMP: {
    ASS(objectPos > 0);
    obj = objects[--objectPos];
    const Formula* f = reinterpret_cast<const Formula*>(obj);
#if TRACE_FINDER
    cout << "M: IMP: " << f->toString() << "\n";
#endif
    if (f->connective() !=Connective::IMP) {
      goto backtrack;
    }

    objects[objectPos++] = f->right();
    objects[objectPos++] = f->left();

    cp++;
    goto match;
  }

  case (unsigned)Code::CFORALL: {
    ASS(objectPos > 0);
    obj = objects[--objectPos];
    const Formula* f = reinterpret_cast<const Formula*>(obj);
#if TRACE_FINDER
    cout << "M: FORALL " << (int)code[cp+1] << ": " << f->toString() << "\n";
#endif
    if (f->connective() != Connective::FORALL) {
      goto backtrack;
    }
    if (Formula::VarList::length(f->vars()) != code[cp+1]) {
      goto backtrack;
    }
    cp += 2;
    List<int>::Iterator vs(f->vars());
    while (vs.hasNext()) {
      vars[code[cp++]] = vs.next();
    }
    objects[objectPos++] = f->qarg();

    goto match;
  }

  case (unsigned)Code::POS: {
    ASS(objectPos > 0);

    obj = objects[--objectPos];
    const Formula* f = reinterpret_cast<const Formula*>(obj);
#if TRACE_FINDER
    cout << "M: POS: " << f->toString() << "\n";
#endif
    if (f->connective() != Kernel::Connective::LITERAL) {
      goto backtrack;
    }
    const Literal* lit = f->literal();
    if (! lit->isPositive()) {
      goto backtrack;
    }
    objects[objectPos++] = lit;

    cp++;
    goto match;
  }

#if VDEBUG
  case (unsigned)Code::CAND:
  case (unsigned)Code::CNOT:
  case (unsigned)Code::CXOR:
  case (unsigned)Code::CEXISTS:
  case (unsigned)Code::NEG:
  case (unsigned)Code::TERM:
  case (unsigned)Code::FORM:
  default:
    ASSERTION_VIOLATION;
#endif
  }

 backtrack:
  if (backtrackPos == 0) {
#if TRACE_FINDER
    cout << "M: fail\n";
#endif
    return false;
  }
  // retrieving information for backtracking
  Backtrack& back = backtrack[--backtrackPos];
  cp = back.cp;
  obj = back.obj;

  ASS_GE(objectPos,(int)back.objPos); // if we already went below the stored objPos, if the restored code succeeds, we will continue into undefined territory
  // Actually, this might still be to weak; we should insist the whole objects stack up back.objPos is identical to the one when Backtrack back was created.
  // Example of the problem: Matching
  /* {CIFF,                           // <=>
   *  CFORALL,1,0,CIFF,              // (Ax0)<=>
   *  POS,NEWPRED,0,2,OLDVAR,0,NEWVAR,1, //  member(x0,x1)
   *  POS,OLDPRED,0,OLDVAR,0,NEWVAR,2,   //  member(x0,x2)
   *  POS,EQL,OLDVAR1,1,OLDVAR1,2,END};         // x1=x2
   * against
   * set_equal(X,Y) <=> ! [Z] : ( element(Z,X) <=> element(Z,Y) ).
   *
   * After
   * ! [Z] : ( element(Z,X) <=> element(Z,Y) )
   * succeeds
   * set_equal(X,Y)
   * fails (because set_equal is not "=").
   *
   * Backtracking to the other polarity of ( element(Z,X) <=> element(Z,Y) )
   * is at this point evil, since the objects stack no longer contains
   * set_equal(X,Y) as a LITARAL formula at objectPos==0
   *
   * In this case fixed by using non-backtrackable CIFF for the inner <=>
   **/

  objectPos = back.objPos;

  switch (code[cp]) {
  case (unsigned)Code::EQL: {
    const Literal* lit = reinterpret_cast<const Literal*>(obj);
#if TRACE_FINDER
    cout << "B: EQL: " << lit->toString() << "\n";
#endif
    const TermList* ts = lit->args();
    objects[objectPos++] = ts;
    objects[objectPos++] = ts->next();

    cp++;
    goto match;
  }

  case (unsigned)Code::CIFF: {
    const Formula* f = reinterpret_cast<const Formula*>(obj);
#if TRACE_FINDER
    cout << "B: IFF: " << f->toString() << "\n";
#endif
    objects[objectPos++] = f->left();
    objects[objectPos++] = f->right();

    cp++;
    goto match;
  }

  case (unsigned)Code::PLIT:
  case (unsigned)Code::NLIT: {
#if TRACE_FINDER
    cout << "B: LIT\n";
#endif
    unsigned l = code[cp+1];
    // bit field of choices for this literal
    unsigned choice = (1u << clength) - 1;
    for (int i = l-1;i >= 0;i--) {
      // remove from the choice literals already used
      choice -= 1u << literals[i];
    }
    int c = literals[l]+1;
    // find the next available literal whose polarity matches
    while (c < clength) {
      // remove from the choice literals already used
      if (choice & (1 << c)) {
	if ((*clause)[c]->isPositive()) {
	  if (code[cp] == (unsigned)Shell::TheoryFinder::Code::PLIT) {
	    break;
	  }
	}
	else if (code[cp] == (unsigned)Shell::TheoryFinder::Code::NLIT) {
	  break;
	}
      }
      c++;
    }

    if (c == clength) { // no candidate found
      goto backtrack;
    }

    // create a backtrack point
    Backtrack& back = backtrack[backtrackPos++];
    back.cp = cp;
    back.objPos = objectPos;

    literals[l] = c;
    objects[objectPos++] = (*clause)[c];

    cp += 2;
    goto match;
  }

#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }
} // TheoryFinder::MatcherState::match

/**
 * Match atom against commutativity x+y=y+x.
 *
 * @since 10/06/2004 Manchester
 */
bool TheoryFinder::matchC(const Literal* lit)
{
  CALL("TheoryFinder::matchC");

#if TRACE_FINDER
  cout << lit->toString() << "\n";
#endif
  static const unsigned char code[] =
  {(unsigned char)Code::EQL, //                                   // =
    (unsigned char)Code::NEWFUN1,0,2,(unsigned char)Code::NEWVAR,0,(unsigned char)Code::NEWVAR,1,  // +(x0,x1)
    (unsigned char)Code::OLDFUN1,0,(unsigned char)Code::OLDVAR,1,(unsigned char)Code::OLDVAR,0,
    (unsigned char)Code::END};   // +(x1,x0)

  if (matchCode(lit,code,0)) {
#if SHOW_FOUND
    cout << "C: " << lit->toString() << "\n";
#endif
    return true;
  }
  return false;
} // TheoryFinder::matchC(const Literal* lit)


/**
 * Match atom against associativity (x+y)+z=x+(y+z).
 *
 * @since 16/06/2005 Manchester
 */
bool TheoryFinder::matchA(const Literal* lit)
{
  CALL("TheoryFinder::matchA");
  static const unsigned char code[] =
  {(unsigned char)Code::EQL, //                                   // =
    (unsigned char)Code::NEWFUN1,0,2,(unsigned char)Code::OLDFUN,0,
    (unsigned char)Code::NEWVAR,0,(unsigned char)Code::NEWVAR,1,(unsigned char)Code::NEWVAR,2,  // +(+(x0,x1),x2)
    (unsigned char)Code::OLDFUN1,0,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::OLDFUN,0,
    (unsigned char)Code::OLDVAR,1,(unsigned char)Code::OLDVAR,2,   // +(x0,+(x1,x2))
    (unsigned char)Code::END};

  if (matchCode(lit,code,0)) {
#if SHOW_FOUND
    cout << "A: " << lit->toString() << "\n";
#endif
    return true;
  }
  return false;
} // TheoryFinder::matchA(const Literal* lit)

/**
 * Match clause against part of extensionality axiom
 * member(f(X,Y),X) \/ member(f(X,Y),Y) \/ X=Y
 *
 * @since 25/06/2004 Dresden
 */
bool TheoryFinder::matchExtensionality (const Clause* c)
{
  CALL("TheoryFinder::matchExtensionality (const Clause&...)");

  static const unsigned char code[] =
    { (unsigned char)Code::CLS,
     (unsigned char)Code::NLIT,0,
      (unsigned char)Code::NEWPRED,0,2,                            // ~member(f(X,Y),X),
      (unsigned char)Code::NEWFUN,0,2,(unsigned char)Code::NEWVAR,0,(unsigned char)Code::NEWVAR,1,(unsigned char)Code::OLDVAR,0,
     (unsigned char)Code::NLIT,1,
      (unsigned char)Code::OLDPRED,0,                              // ~member(f(X,Y),Y),
      (unsigned char)Code::OLDFUN,0,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::OLDVAR,1,(unsigned char)Code::OLDVAR,1,
     (unsigned char)Code::PLIT,2,
      (unsigned char)Code::EQL,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::OLDVAR,1,(unsigned char)Code::END}; // X=Y

  if (matchCode(c,code,Property::PR_HAS_EXTENSIONALITY)) {
#if SHOW_FOUND
    cout << "Extensionality: " << c->toString() << "\n";
#endif
    return true;
  }
  return false;
} // TheoryFinder::matchExtensionality

/**
 * Match clause against the condensed detachment axiom
 * ~theorem(X) \/ ~theorem(imply(X,Y)) \/ theorem(Y).
 *
 * @since 21/06/2005 Manchester
 */
bool TheoryFinder::matchCondensedDetachment1(const Clause* c)
{
  CALL("TheoryFinder::CondensedDetachment1(const LiteralList&...)");

  static const unsigned char code[] =
  { (unsigned char)Code::CLS,
   (unsigned char)Code::PLIT,0,
    (unsigned char)Code::NEWPRED,0,1,(unsigned char)Code::NEWVAR,0,                         // theorem(x0)
   (unsigned char)Code::NLIT,1,
    (unsigned char)Code::OLDPRED,0,(unsigned char)Code::NEWVAR,1,                      // ~theorem(x1)
   (unsigned char)Code::NLIT,2,
    (unsigned char)Code::OLDPRED,0,(unsigned char)Code::NEWFUN,0,2,(unsigned char)Code::OLDVAR,1,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::END}; // ~theorem(imply(x1,x0))

  if (matchCode(c,code,Property::PR_HAS_CONDENSED_DETACHMENT1)) {
#if SHOW_FOUND
    cout << "Condensed detachment 1: " << c->toString() << "\n";
#endif
    return true;
  }
  return false;
} // TheoryFinder::matchCondensedDetachment1

/**
 * Match clause against the condensed detachment axiom
 * ~theorem(X) \/ ~theorem(or(not(X),Y)) \/ theorem(Y).
 *
 * @since 21/06/2005 Manchester
 */
bool TheoryFinder::matchCondensedDetachment2(const Clause* c)
{
  CALL("TheoryFinder::CondensedDetachment2(const Clause&...)");

  static const unsigned char code[] =
  {(unsigned char)Code::CLS,
   (unsigned char)Code::PLIT,0,
    (unsigned char)Code::NEWPRED,0,1,(unsigned char)Code::NEWVAR,0,                                    // theorem(x0)
   (unsigned char)Code::NLIT,1,
    (unsigned char)Code::OLDPRED,0,(unsigned char)Code::NEWVAR,1,                                 // ~theorem(x1)
   (unsigned char)Code::NLIT,2,
    (unsigned char)Code::OLDPRED,0,(unsigned char)Code::NEWFUN,0,2,(unsigned char)Code::NEWFUN,1,1,(unsigned char)Code::OLDVAR,1,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::END}; // ~theorem(or(not(x1),x0))

  if (matchCode(c,code,Property::PR_HAS_CONDENSED_DETACHMENT2)) {
#if SHOW_FOUND
    cout << "Condensed detachment 2: " << c->toString() << "\n";
#endif
    return true;
  }
  return false;
} // TheoryFinder::matchmatchCondensedDetachment2

/**
 * Match clause against the axiom
 * equalish(add(multiply(X,Z),multiply(Y,Z)),multiply(add(X,Y),Z)) \/
 * ~defined(X) \/ ~defined(Y) \/ ~defined(Z).
 *
 * @since 21/06/2005 Manchester
 */
bool TheoryFinder::matchFLD1(const Clause* c)
{
  CALL("TheoryFinder::matchFLD1(const Clause&...)");

  static const unsigned char code[] =
    { (unsigned char)Code::CLS,
     (unsigned char)Code::PLIT,0,
      (unsigned char)Code::NEWPRED,0,2,(unsigned char)Code::NEWFUN,0,2,(unsigned char)Code::NEWFUN,1,2,(unsigned char)Code::NEWVAR,0,(unsigned char)Code::NEWVAR,1,     // equalish(add(multiply(x0,x1),
       (unsigned char)Code::OLDFUN,1,(unsigned char)Code::NEWVAR,2,(unsigned char)Code::OLDVAR,1,                             //  multiply(x2,x1)),
       (unsigned char)Code::OLDFUN,1,(unsigned char)Code::OLDFUN,0,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::OLDVAR,2,(unsigned char)Code::OLDVAR,1,           //  multiply(add(x0,x2),x1))
     (unsigned char)Code::NLIT,1,
      (unsigned char)Code::NEWPRED,1,1,(unsigned char)Code::OLDVAR,0,                               // ~defined(x0)
     (unsigned char)Code::NLIT,2,
      (unsigned char)Code::OLDPRED,1,(unsigned char)Code::OLDVAR,2,                                 // ~defined(x2)
     (unsigned char)Code::NLIT,3,
      (unsigned char)Code::OLDPRED,1,(unsigned char)Code::OLDVAR,1,(unsigned char)Code::END};                             // ~defined(x1)

  if (matchCode(c,code,Property::PR_HAS_FLD1)) {
#if SHOW_FOUND
    cout << "FLD1: " << c->toString() << "\n";
#endif
    return true;
  }
  return false;
} // TheoryFinder::matchFLD1

/**
 * Match clause against the axiom
 * product(multiplicative_inverse(X),X,multiplicative_identity) \/
 * sum(additive_identity,X,additive_identity) \/
 * ~defined(X).
 *
 * @since 21/06/2005 Manchester
 */
bool TheoryFinder::matchFLD2(const Clause* c)
{
  CALL("TheoryFinder::matchFLD2(const Clause&...)");

  static const unsigned char code[] =
  { (unsigned char)Code::CLS,
   (unsigned char)Code::PLIT,0,
    (unsigned char)Code::NEWPRED,0,3,(unsigned char)Code::NEWFUN,0,1,(unsigned char)Code::NEWVAR,0,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::NEWFUN,0,0,     // product(inv(x0),x0,1)
   (unsigned char)Code::PLIT,1,
   (unsigned char)Code::NEWPRED,1,3,(unsigned char)Code::NEWFUN,2,0,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::OLDFUN,2,                // sum(0,x0,0)
   (unsigned char)Code::NLIT,2,
    (unsigned char)Code::NEWPRED,2,1,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::END};                               // ~defined(x0)

  if (matchCode(c,code,Property::PR_HAS_FLD2)) {
#if SHOW_FOUND
    cout << "FLD2: " << c->toString() << "\n";
#endif
    return true;
  }
  return false;
} // TheoryFinder::matchFLD2

/**
 * Match clause against part of the subset axiom
 * member(f(X,Y),X) \/ subset(X,Y), where f is disregarded.
 *
 * @since 24/06/2004 Dresden
 * @since 19/06/2005 Manchester, simplified using matchCode(...)
 */
bool TheoryFinder::matchSubset (const Clause* c)
{
  CALL("TheoryFinder::matchSubset(const Clause* c)");

  static const unsigned char code[] =
  { (unsigned char)Code::CLS,
   (unsigned char)Code::PLIT,0,
    (unsigned char)Code::NEWPRED,0,2,                 // member(f(X,Y),X),
     (unsigned char)Code::NEWFUN,0,2,(unsigned char)Code::NEWVAR,0,(unsigned char)Code::NEWVAR,1,(unsigned char)Code::OLDVAR,0,
   (unsigned char)Code::PLIT,1,
    (unsigned char)Code::NEWPRED,1,2,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::OLDVAR,1,(unsigned char)Code::END}; // subset(X,Y)

  if (matchCode(c,code,Property::PR_HAS_SUBSET)) {
#if SHOW_FOUND
    cout << "Subset: " << c->toString() << "\n";
#endif
    return true;
  }
  return false;
} // TheoryFinder::matchSubset

/**
 * Match formula against part the subset axiom
 * subset(x,y) &lt;=&gt; (Az)(member(z,x) =&gt; member(z,y)).
 *
 * @since 25/06/2004 Dresden
 * @since 19/06/2005 Manchester, simplified using matchCode(...)
 */
bool TheoryFinder::matchSubset (const Formula* f)
{
  CALL("TheoryFinder::matchSubset(const Formula* f)");

  static const unsigned char code[] =
    { (unsigned char)Code::CIFF,                          // <=>
      (unsigned char)Code::POS,(unsigned char)Code::NEWPRED,0,2,(unsigned char)Code::NEWVAR,0,(unsigned char)Code::NEWVAR,1, //  subset(x,y)
      (unsigned char)Code::CFORALL,1,2,(unsigned char)Code::CIMP,             //  (Az) =>
       (unsigned char)Code::POS,(unsigned char)Code::NEWPRED,1,2,(unsigned char)Code::OLDVAR,2,(unsigned char)Code::OLDVAR,0,//   member(z,x)
       (unsigned char)Code::POS,(unsigned char)Code::OLDPRED,1,(unsigned char)Code::OLDVAR,2,(unsigned char)Code::OLDVAR,1,(unsigned char)Code::END}; //   member(z,y)

  if (matchCode(f,code,Property::PR_HAS_SUBSET)) {
#if SHOW_FOUND
    cout << "Subset: " << f->toString() << "\n";
#endif
    return true;
  }
  return false;
} // TheoryFinder::matchSubset

// tff(l1,axiom,(! [K: $int,L: list] : head(cons(K,L)) = K )).
// tff(l2,axiom,(! [K: $int,L: list] : tail(cons(K,L)) = L )).
// %----Constructors
// tff(l3,axiom,(
//     ! [L: list] :
//       ( L = nil
//       | L = cons(head(L),tail(L)) ) )).
// tff(l4,axiom,(
//     ! [K: $int,L: list] : cons(K,L) != nil )).

/**
 * Match formula against part the list constructors axiom
 * L = nil v L = cons(head(L),tail(L))
 * @since 16/06/2015 Manchester
 * @author Andrei Voronkov
 */
bool TheoryFinder::matchListConstructors (const Formula* f)
{
  CALL("TheoryFinder::matchListConstructors");
#if TRACE_FINDER
  cout << "M: [match list constructors axiom]\n";
#endif

  static const unsigned char code1[] =
     { (unsigned char)Code::COR,2,                        // \/
       (unsigned char)Code::POS,(unsigned char)Code::EQL,(unsigned char)Code::NEWVAR,0,            // =(L,
               (unsigned char)Code::NEWFUN1,0,2,          // cons
                (unsigned char)Code::NEWFUN,1,1,(unsigned char)Code::OLDVAR,0, // head(L)
                (unsigned char)Code::NEWFUN,2,1,(unsigned char)Code::OLDVAR,0, // tail(L)
       (unsigned char)Code::POS,(unsigned char)Code::EQL,(unsigned char)Code::OLDVAR1,0,(unsigned char)Code::NEWFUN1,3,0,(unsigned char)Code::END}; // =(L,nil)
  static const unsigned char code2[] =
     { (unsigned char)Code::COR,2,                         // \/
       (unsigned char)Code::POS,(unsigned char)Code::EQL,(unsigned char)Code::NEWVAR,0,(unsigned char)Code::NEWFUN1,0,0, // =(L,nil)
       (unsigned char)Code::POS,(unsigned char)Code::EQL,(unsigned char)Code::OLDVAR1,0,             // =(L,
               (unsigned char)Code::NEWFUN1,1,2,          // cons
                (unsigned char)Code::NEWFUN,2,1,(unsigned char)Code::OLDVAR,0, // head(L)
                (unsigned char)Code::NEWFUN,3,1,(unsigned char)Code::OLDVAR,0, // tail(L)
      (unsigned char)Code::END};
  if (matchCode(f,code1,Property::PR_LIST_AXIOMS) ||
      matchCode(f,code2,Property::PR_LIST_AXIOMS)) {
#if SHOW_FOUND
    cout << "List constructors: " << f->toString() << "\n";
#endif
    return true;
  }
  return false;
} // TheoryFinder::matchListConstructors

/**
 * Match formula against the extensionality axiom
 * (Az)(member(z,x) &lt;=&gt; member(z,y)) =&gt; x=y,
 * or the same but with &lt;=&gt; instead of =&gt;.
 *
 * @since 25/06/2004 Dresden
 * @since 19/06/2005 Manchester, simplified using matchCode(...)
 */
bool TheoryFinder::matchExtensionality (const Formula* f)
{
  CALL("TheoryFinder::matchExtensionality (const Formula&...)");

  static const unsigned char code1[] =
    { (unsigned char)Code::CIFF,                           // <=>
      (unsigned char)Code::CFORALL,1,0,(unsigned char)Code::NBCIFF,              // (Ax0)<=>
       (unsigned char)Code::POS,(unsigned char)Code::NEWPRED,0,2,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::NEWVAR,1, //  member(x0,x1)
       (unsigned char)Code::POS,(unsigned char)Code::OLDPRED,0,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::NEWVAR,2,   //  member(x0,x2)
       (unsigned char)Code::POS,(unsigned char)Code::EQL,(unsigned char)Code::OLDVAR1,1,(unsigned char)Code::OLDVAR1,2,(unsigned char)Code::END};         // x1=x2
  static const unsigned char code2[] =
    { (unsigned char)Code::CIMP,                           // =>
      (unsigned char)Code::CFORALL,1,0,(unsigned char)Code::NBCIFF,              // (Ax0)<=>
       (unsigned char)Code::POS,(unsigned char)Code::NEWPRED,0,2,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::NEWVAR,1, //  member(x0,x1)
       (unsigned char)Code::POS,(unsigned char)Code::OLDPRED,0,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::NEWVAR,2,   //  member(x0,x2)
       (unsigned char)Code::POS,(unsigned char)Code::EQL,(unsigned char)Code::OLDVAR1,1,(unsigned char)Code::OLDVAR1,2,(unsigned char)Code::END};         // x1=x2

  // NBCIFF explained: As the LHS and the RHS of the inner <=> are variants, it does not make sense to backtrack over them; EQL is commutative to check the two versions!

  if (matchCode(f,code1,Property::PR_HAS_EXTENSIONALITY) ||
      matchCode(f,code2,Property::PR_HAS_EXTENSIONALITY)) {
#if SHOW_FOUND
    cout << "Extensionality: " << f->toString() << "\n";
#endif
    return true;
  }
  return false;
} // TheoryFinder::matchExtensionality


/**
 * Match atom against the left inverse axiom i(x)*x=1
 *
 * @since 16/06/2005 Manchester
 */
bool TheoryFinder::matchLeftInverse(const Literal* lit)
{
  CALL("TheoryFinder::matchLeftInverse");

  static const unsigned char code[] =
   { (unsigned char)Code::EQL, //                                                // =
    (unsigned char)Code::NEWFUN1,0,2,(unsigned char)Code::NEWFUN,1,1,(unsigned char)Code::NEWVAR,0,(unsigned char)Code::OLDVAR,0, // *(i(x0),x0)
    (unsigned char)Code::NEWFUN1,2,0,                              // 1
    (unsigned char)Code::END};

  if (matchCode(lit,code,0)) {
#if SHOW_FOUND
    cout << "Left inverse: " << lit->toString() << "\n";
#endif
    return true;
  }
  return false;
} // TheoryFinder::matchLeftInverse(const Literal* lit)

/**
 * Match atom against the right inverse axiom x*i(x)=1
 *
 * @since 16/06/2005 Manchester
 */
bool TheoryFinder::matchRightInverse(const Literal* lit)
{
  CALL("TheoryFinder::matchRightInverse");

  static const unsigned char code[] =
   { (unsigned char)Code::EQL, //                                                // =
    (unsigned char)Code::NEWFUN1,0,2,(unsigned char)Code::NEWVAR,0,(unsigned char)Code::NEWFUN,1,1,(unsigned char)Code::OLDVAR,0,// *(x0,i(x0))
    (unsigned char)Code::NEWFUN1,2,0,                                           // 1
    (unsigned char)Code::END};

  if (matchCode(lit,code,0)) {
#if SHOW_FOUND
    cout << "Right inverse: " << lit->toString() << "\n";
#endif
    return true;
  }
  return false;
} // TheoryFinder::matchRightInverse(const Literal* lit)

/**
 * Match atom against the left identity axiom 1*x=x
 *
 * @since 16/06/2005 Manchester
 */
bool TheoryFinder::matchLeftIdentity(const Literal* lit)
{
  CALL("TheoryFinder::matchLeftIdentity");

  static const unsigned char code[] =
   { (unsigned char)Code::EQL, //                           // =
    (unsigned char)Code::NEWFUN1,0,2,(unsigned char)Code::NEWFUN,1,0,(unsigned char)Code::NEWVAR,0,  // *(1,x)
    (unsigned char)Code::OLDVAR1,0,                        // x
    (unsigned char)Code::END};

  if (matchCode(lit,code,0)) {
#if SHOW_FOUND
    cout << "Left identity: " << lit->toString() << "\n";
#endif
    return true;
  }
  return false;
} // TheoryFinder::matchLeftIdentity(const Literal* lit)

/**
 * Match atom against the idempotence axiom x*x=x
 *
 * @since 16/06/2005 Manchester
 */
bool TheoryFinder::matchIdempotence(const Literal* lit)
{
  CALL("TheoryFinder::matchIdempotence");

  static const unsigned char code[] =
    { (unsigned char)Code::EQL,(unsigned char)Code::NEWFUN1,0,2,(unsigned char)Code::NEWVAR,0,(unsigned char)Code::OLDVAR,0,
     (unsigned char)Code::OLDVAR1,0,(unsigned char)Code::END}; // =(*(x0,x0),x0)

  if (matchCode(lit,code,0)) {
#if SHOW_FOUND
    cout << "Idempotence: " << lit->toString() << "\n";
#endif
    return true;
  }
  return false;
} // TheoryFinder::matchIdempotence(const Literal* lit)

/**
 * Match atom against the right identity axiom x*1=x
 *
 * @since 16/06/2005 Manchester
 */
bool TheoryFinder::matchRightIdentity(const Literal* lit)
{
  CALL("TheoryFinder::matchRightIdentity");

  static const unsigned char code[] =
   { (unsigned char)Code::EQL, //                          // =
    (unsigned char)Code::NEWFUN1,0,2,(unsigned char)Code::NEWVAR,0,(unsigned char)Code::NEWFUN,1,0, // *(x,1)
    (unsigned char)Code::OLDVAR1,0,(unsigned char)Code::END};                  // x

  if (matchCode(lit,code,0)) {
#if SHOW_FOUND
    cout << "Right identity: " << lit->toString() << "\n";
#endif
    return true;
  }
  return false;
} // TheoryFinder::matchRightIdentity(const Literal* lit)

/**
 * Match atom against the associator axiom
 * A(x,y,z) = A(x,y,z) = +(*(*(x,y),z),-(*(x,*(y,z)))).
 *
 * @since 17/06/2005 Manchester
 */
bool TheoryFinder::matchAssociator(const Literal* lit)
{
  CALL("TheoryFinder::matchAssociator");

  static const unsigned char code[] =
   { (unsigned char)Code::EQL, //                                                    // =
    (unsigned char)Code::NEWFUN1,0,3,(unsigned char)Code::NEWVAR,0,(unsigned char)Code::NEWVAR,1,(unsigned char)Code::NEWVAR,2,                     // A(x0,x1,x2)
    (unsigned char)Code::NEWFUN1,1,2,(unsigned char)Code::NEWFUN,2,2,(unsigned char)Code::OLDFUN,2,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::OLDVAR,1,(unsigned char)Code::OLDVAR,2, // +(*(*(x0,x1),x2),
    (unsigned char)Code::NEWFUN,3,1,(unsigned char)Code::OLDFUN,2,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::OLDFUN,2,(unsigned char)Code::OLDVAR,1,(unsigned char)Code::OLDVAR,2,  // -(*(x0,*(x1,x2))))
    (unsigned char)Code::END};

  if (matchCode(lit,code,0)) {
#if SHOW_FOUND
    cout << "Associator: " << lit->toString() << "\n";
#endif
    return true;
  }
  return false;
} // TheoryFinder::matchAssociator

/**
 * Match atom against the commutator axiom C(x,y) = +(*(y,x),-(*(x,y))).
 *
 * @since 17/06/2005 Manchester
 */
bool TheoryFinder::matchCommutator(const Literal* lit)
{
  CALL("TheoryFinder::matchCommutator");

  static const unsigned char code[] =
   { (unsigned char)Code::EQL,                                      // =
    (unsigned char)Code::NEWFUN1,0,3,(unsigned char)Code::NEWVAR,0,(unsigned char)Code::NEWVAR,1,            // C(x0,x1)
    (unsigned char)Code::NEWFUN1,1,2,(unsigned char)Code::NEWFUN,2,2,(unsigned char)Code::OLDVAR,1,(unsigned char)Code::OLDVAR,0, // +(*(x1,x0),
    (unsigned char)Code::NEWFUN,3,1,(unsigned char)Code::OLDFUN,2,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::OLDVAR,1,    // -(*(x0,x1)))
    (unsigned char)Code::END};

  if (matchCode(lit,code,0)) {
#if SHOW_FOUND
    cout << "Commutator: " << lit->toString() << "\n";
#endif
    return true;
  }
  return false;
} // TheoryFinder::matchCommutator

/**
 * Match atom against the left distributivity axiom.
 *
 * @since 17/06/2005 Manchester
 */
bool TheoryFinder::matchLeftDistributivity(const Literal* lit)
{
  CALL("TheoryFinder::matchLeftDistributivity");

  static const unsigned char code[] =
   { (unsigned char)Code::EQL, //                                                // =
    (unsigned char)Code::NEWFUN1,0,2,(unsigned char)Code::NEWFUN,1,2,(unsigned char)Code::NEWVAR,0,
    (unsigned char)Code::NEWVAR,1,(unsigned char)Code::NEWVAR,2,                                // *(+(x0,x1),x2)
    (unsigned char)Code::OLDFUN1,1,(unsigned char)Code::OLDFUN,0,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::OLDVAR,2,
    (unsigned char)Code::OLDFUN,0,(unsigned char)Code::OLDVAR,1,(unsigned char)Code::OLDVAR,2,(unsigned char)Code::END};                 // +(*(x0,x2),*(x1,x2))

  if (matchCode(lit,code,0)) {
#if SHOW_FOUND
    cout << "Left distributivity: " << lit->toString() << "\n";
#endif
    return true;
  }
  return false;
} // TheoryFinder::matchLeftDistributivity(const Literal* lit)

/**
 * Match atom against the right distributivity axiom.
 *
 * @since 17/06/2005 Manchester
 */
bool TheoryFinder::matchRightDistributivity (const Literal* lit)
{
  CALL("TheoryFinder::matchRightDistributivity");

  static const unsigned char code[] =
   { (unsigned char)Code::EQL, //                                // =
    (unsigned char)Code::NEWFUN1,0,2,(unsigned char)Code::NEWVAR,0,(unsigned char)Code::NEWFUN,1,2,
    (unsigned char)Code::NEWVAR,1,(unsigned char)Code::NEWVAR,2,                     // *(x0,+(x1,x2))
    (unsigned char)Code::OLDFUN1,1,(unsigned char)Code::OLDFUN,0,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::OLDVAR,1,
    (unsigned char)Code::OLDFUN,0,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::OLDVAR,2,(unsigned char)Code::END};       // +(*(x0,x1),*(x0,x2))

  if (matchCode(lit,code,0)) {
#if SHOW_FOUND
    cout << "Right distributivity: " << lit->toString() << "\n";
#endif
    return true;
  }
  return false;
} // TheoryFinder::matchRightDistributivity(const Literal* lit)

/**
 * Match atom against any of the four versions of the Robbins Algebra axiom.
 *
 * @since 17/06/2005 Manchester
 */
bool TheoryFinder::matchRobbins(const Literal* lit)
{
  CALL("TheoryFinder::matchRobbins");

  static const unsigned char code1[] =
   { (unsigned char)Code::EQL, //                                                     // =
     (unsigned char)Code::NEWFUN1,0,1,(unsigned char)Code::NEWFUN,1,2,(unsigned char)Code::OLDFUN,0,(unsigned char)Code::OLDFUN,1,(unsigned char)Code::NEWVAR,0,(unsigned char)Code::NEWVAR,1,//  n(+(n(+(x0,x1)),
      (unsigned char)Code::OLDFUN,0,(unsigned char)Code::OLDFUN,1,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::OLDFUN,0,(unsigned char)Code::OLDVAR,1,             //  n(+(x0,n(x1)))))
    (unsigned char)Code::OLDVAR1,0,(unsigned char)Code::END};                                             //  x0
  static const unsigned char code2[] =
   { (unsigned char)Code::EQL, //                                                     // =
     (unsigned char)Code::NEWFUN1,0,1,(unsigned char)Code::NEWFUN,1,2,(unsigned char)Code::OLDFUN,0,(unsigned char)Code::OLDFUN,1,(unsigned char)Code::NEWVAR,0,(unsigned char)Code::NEWVAR,1,//  n(+(n(+(x0,x1)),
      (unsigned char)Code::OLDFUN,0,(unsigned char)Code::OLDFUN,1,(unsigned char)Code::OLDFUN,0,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::OLDVAR,1,             //  n(+(n(x0),x1))))
    (unsigned char)Code::OLDVAR1,1,(unsigned char)Code::END};                                             //  x1
  static const unsigned char code3[] =
   { (unsigned char)Code::EQL, //                                                             // =
     (unsigned char)Code::NEWFUN1,0,1,(unsigned char)Code::NEWFUN,1,2,(unsigned char)Code::OLDFUN,0,(unsigned char)Code::OLDFUN,1,(unsigned char)Code::NEWVAR,0,(unsigned char)Code::OLDFUN,0,(unsigned char)Code::NEWVAR,1,//  n(+(n(+(x0,n(x1))),
      (unsigned char)Code::OLDFUN,0,(unsigned char)Code::OLDFUN,1,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::OLDVAR,1,                              //  n(+(x0,x1))))
    (unsigned char)Code::OLDVAR1,0,(unsigned char)Code::END};                                                     //  x0
  static const unsigned char code4[] =
   { (unsigned char)Code::EQL, //                                                             // =
     (unsigned char)Code::NEWFUN,0,1,(unsigned char)Code::NEWFUN,1,2,(unsigned char)Code::OLDFUN,0,(unsigned char)Code::OLDFUN,1,(unsigned char)Code::OLDFUN,0,(unsigned char)Code::NEWVAR,0,(unsigned char)Code::NEWVAR,1,//  n(+(n(+(n(x0),x1)),
      (unsigned char)Code::OLDFUN,0,(unsigned char)Code::OLDFUN,1,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::OLDVAR,1,                              //  n(+(x0,x1))))
    (unsigned char)Code::OLDVAR,1,(unsigned char)Code::END};                                                      //  x1

  if (matchCode(lit,code1,0) ||
      matchCode(lit,code2,0) ||
      matchCode(lit,code3,0) ||
      matchCode(lit,code4,0)) {
#if SHOW_FOUND
    cout << "Robbins: " << lit->toString() << "\n";
#endif
    return true;
  }
  return false;
} // TheoryFinder::matchRobbins(const Literal* lit)

/**
 * Match atom against any of the two versions of the alternative
 * associativity axiom: *(*(x,x),y) = *(x,*(x,y)) or
 * *(*(x,y),y) = *(x,*(y,y)).
 *
 * @since 17/06/2005 Manchester
 */
bool TheoryFinder::matchAlternative(const Literal* lit)
{
  CALL("TheoryFinder::matchAlternative");

  static const unsigned char code1[] =
   { (unsigned char)Code::EQL, //                                          // =
     (unsigned char)Code::NEWFUN1,0,2,(unsigned char)Code::OLDFUN,0,(unsigned char)Code::NEWVAR,0,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::NEWVAR,1, // *(*(x0,x0),x1)
    (unsigned char)Code::OLDFUN1,0,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::OLDFUN,0,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::OLDVAR,1,(unsigned char)Code::END};  // *(x0,*(x0,x1))
  static const unsigned char code2[] =
   { (unsigned char)Code::EQL, //                                          // =
     (unsigned char)Code::NEWFUN1,0,2,(unsigned char)Code::OLDFUN,0,(unsigned char)Code::NEWVAR,0,(unsigned char)Code::NEWVAR,1,(unsigned char)Code::OLDVAR,1, // *(*(x0,x1),x1)
    (unsigned char)Code::OLDFUN1,0,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::OLDFUN,0,(unsigned char)Code::OLDVAR,1,(unsigned char)Code::OLDVAR,1,(unsigned char)Code::END};  // *(x0,*(x1,x1))

  if (matchCode(lit,code1,0) ||
      matchCode(lit,code2,0)) {
#if SHOW_FOUND
    cout << "Alternative: " << lit->toString() << "\n";
#endif
    return true;
  }
  return false;
} // TheoryFinder::matchAlternative(const Literal* lit)

/**
 * Match atom against the right absorption axiom *(x,+(x,y)) = x.
 *
 * @since 17/06/2005 Manchester
 */
bool TheoryFinder::matchAbsorption(const Literal* lit)
{
  CALL("TheoryFinder::matchAbsorption");

  static const unsigned char code[] =
   { (unsigned char)Code::EQL,                                              // =
    (unsigned char)Code::NEWFUN1,0,2,(unsigned char)Code::NEWVAR,0,(unsigned char)Code::NEWFUN,1,2,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::NEWVAR,1, // *(x0,+(x0,x1))
    (unsigned char)Code::OLDVAR1,0,(unsigned char)Code::END};             // x0
  
  if (matchCode(lit,code,0)) {
#if SHOW_FOUND
    cout << "Absorption: " << lit->toString() << "\n";
#endif
    return true;
  }
  return false;
} // TheoryFinder::matchAbsorption(const Literal* lit)

/**
 * Match atom against the S-combinator axiom
 * _(_(_(S,x),y),z) = _(_(x,z),_(y,z)).
 *
 * @since 18/06/2005 Manchester
 */
bool TheoryFinder::matchCombinatorS(const Literal* lit)
{
  CALL("TheoryFinder::matchCombinatorS");

  static const unsigned char code[] =
   { (unsigned char)Code::EQL,                                     // =
    (unsigned char)Code::NEWFUN1,0,2,(unsigned char)Code::OLDFUN,0,(unsigned char)Code::OLDFUN,0,(unsigned char)Code::NEWFUN,1,0,
     (unsigned char)Code::NEWVAR,0,(unsigned char)Code::NEWVAR,1,(unsigned char)Code::NEWVAR,2,             // _(_(_(S,x0),x1),x2)
    (unsigned char)Code::OLDFUN1,0,(unsigned char)Code::OLDFUN,0,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::OLDVAR,2,
    (unsigned char)Code::OLDFUN,0,(unsigned char)Code::OLDVAR,1,(unsigned char)Code::OLDVAR,2,(unsigned char)Code::END};            // _(_(x0,x2),_(x1,x2))

  if (matchCode(lit,code,Property::PR_COMBINATOR)) {
#if SHOW_FOUND
    cout << "S: " << lit->toString() << "\n";
#endif
    return true;
  }
  return false;
} // TheoryFinder::matchCombinatorS

/**
 * Match atom against the B-combinator axiom
 * ._(_(_(B,x),y),z) = _(x,_(y,z)).
 *
 * @since 18/06/2005 Manchester
 */
bool TheoryFinder::matchCombinatorB(const Literal* lit)
{
  CALL("TheoryFinder::matchCombinatorB");

  static const unsigned char code[] =
   { (unsigned char)Code::EQL,                                           // =
    (unsigned char)Code::NEWFUN1,0,2,(unsigned char)Code::OLDFUN,0,(unsigned char)Code::OLDFUN,0,(unsigned char)Code::NEWFUN,1,0,
     (unsigned char)Code::NEWVAR,0,(unsigned char)Code::NEWVAR,1,(unsigned char)Code::NEWVAR,2,                   // _(_(_(B,x0),x1),x2)
    (unsigned char)Code::OLDFUN1,0,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::OLDFUN,0,(unsigned char)Code::OLDVAR,1,(unsigned char)Code::OLDVAR,2,(unsigned char)Code::END}; // _(x0,_(x1,x2))

  if (matchCode(lit,code,Property::PR_COMBINATOR_B)) {
#if SHOW_FOUND
    cout << "B: " << lit->toString() << "\n";
#endif
    return true;
  }
  return false;
} // TheoryFinder::matchCombinatorB

/**
 * Match atom against the T-combinator axiom
 * _(_(T,x),y) = _(y,x).
 *
 * @since 18/06/2005 Manchester
 */
bool TheoryFinder::matchCombinatorT(const Literal* lit)
{
  CALL("TheoryFinder::matchCombinatorT");

  static const unsigned char code[] =
   { (unsigned char)Code::EQL,                                              // =
    (unsigned char)Code::NEWFUN1,0,2,(unsigned char)Code::OLDFUN,0,(unsigned char)Code::NEWFUN,1,0,(unsigned char)Code::NEWVAR,0,(unsigned char)Code::NEWVAR,1, // _(_(T,x0),x1)
    (unsigned char)Code::OLDFUN1,0,(unsigned char)Code::OLDVAR,1,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::END};                      // _(x1,x0)

  if (matchCode(lit,code,Property::PR_COMBINATOR)) {
#if SHOW_FOUND
    cout << "T: " << lit->toString() << "\n";
#endif
    return true;
  }
  return false;
} // TheoryFinder::matchCombinatorT

/**
 * Match atom against the O-combinator axiom
 * _(_(O,x),y) = _(y,_(x,y)).
 *
 * @since 18/06/2005 Manchester
 */
bool TheoryFinder::matchCombinatorO(const Literal* lit)
{
  CALL("TheoryFinder::matchCombinatorO");

  static const unsigned char code[] =
   { (unsigned char)Code::EQL,                                              // =
    (unsigned char)Code::NEWFUN1,0,2,(unsigned char)Code::OLDFUN,0,(unsigned char)Code::NEWFUN,1,0,(unsigned char)Code::NEWVAR,0,(unsigned char)Code::NEWVAR,1, // _(_(O,x0),x1)
    (unsigned char)Code::OLDFUN1,0,(unsigned char)Code::OLDVAR,1,(unsigned char)Code::OLDFUN,0,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::OLDVAR,1,(unsigned char)Code::END};    // _(x1,_(x0,x1))

  if (matchCode(lit,code,Property::PR_COMBINATOR)) {
#if SHOW_FOUND
    cout << "O: " << lit->toString() << "\n";
#endif
    return true;
  }
  return false;
} // TheoryFinder::matchCombinatorO

/**
 * Match atom against the Q-combinator axiom
 * _(_(_(Q,x),y),z) = _(y,_(x,z)).
 *
 * @since 18/06/2005 Manchester
 */
bool TheoryFinder::matchCombinatorQ(const Literal* lit)
{
  CALL("TheoryFinder::matchCombinatorQ");

  static const unsigned char code[] =
   { (unsigned char)Code::EQL,                                           // =
    (unsigned char)Code::NEWFUN1,0,2,(unsigned char)Code::OLDFUN,0,(unsigned char)Code::OLDFUN,0,(unsigned char)Code::NEWFUN,1,0,
     (unsigned char)Code::NEWVAR,0,(unsigned char)Code::NEWVAR,1,(unsigned char)Code::NEWVAR,2,                   // _(_(_(Q,x0),x1),x2)
    (unsigned char)Code::OLDFUN1,0,(unsigned char)Code::OLDVAR,1,(unsigned char)Code::OLDFUN,0,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::OLDVAR,2,(unsigned char)Code::END}; // _(x1,_(x0,x2))

  if (matchCode(lit,code,Property::PR_COMBINATOR)) {
#if SHOW_FOUND
    cout << "Q: " << lit->toString() << "\n";
#endif
    return true;
  }
  return false;
} // TheoryFinder::matchCombinatorQ

/**
 * Match atom against all known unit axioms.
 *
 * @since 17/06/2005 Manchester
 */
bool TheoryFinder::matchAll (const Literal* lit)
{
  CALL("TheoryFinder::matchAll(const Literal*)");

  if (! lit->isPositive()) {
    return false;
  }

  return matchC(lit) ||
         matchA(lit) ||
         matchIdempotence(lit) ||
         matchLeftInverse(lit) ||
         matchLeftIdentity(lit) ||
         matchRightInverse(lit) ||
         matchRightIdentity(lit) ||
         matchLeftDistributivity(lit) ||
         matchRightDistributivity(lit) ||
         matchAssociator(lit) ||
         matchCommutator(lit) ||
         matchAlternative(lit) ||
         matchAbsorption(lit) ||
         matchRobbins(lit) ||
         matchCombinatorS(lit) ||
         matchCombinatorB(lit) ||
         matchCombinatorT(lit) ||
         matchCombinatorO(lit) ||
         matchCombinatorQ(lit);
} // TheoryFinder::matchAll(const Literal*)

// /**
//  * Analyse the clause obtained by refuting _metaTheory.
//  * @since 18/06/2005 Manchester
//  */
// void TheoryFinder::analyse (const Clause& clause)
// {
//   CALL("TheoryFinder::analyse");

//   const Term& answer = clause.literals().head().atom().args().head();
//   const vstring theory(answer.functor().name());
//   if (theory == "group") {
//     _property->addProp(Property::PR_GROUP);
//   }
//   else if (theory == "ring") {
//     _property->addProp(Property::PR_RING);
//   }
//   else if (theory == "robbins_algebra") {
//     _property->addProp(Property::PR_ROBBINS_ALGEBRA);
//   }
//   else if (theory == "non_associative_ring") {
//     _property->addProp(Property::PR_NA_RING);
//   }
//   else if (theory == "boolean_algebra") {
//     _property->addProp(Property::PR_BOOLEAN_ALGEBRA);
//   }
//   else if (theory == "lattice") {
//     _property->addProp(Property::PR_LATTICE);
//   }
//   else if (theory == "lattice_ordered_group") {
//     _property->addProp(Property::PR_LO_GROUP);
//   }
// #if DEBUG_THEORY_FINDER
//   cout << "THEORY FOUND: " << theory << "\n";
// #endif
// } // TheoryFinder::analyse

/**
 * Returns true iff @c c matches the pattern of a known extensionality clause.
 * At the moment this includes the standard and subset-based formulations of the
 * set extensionality axiom, as well as the array extensionality axiom.
 *
 * All patterns must have exactly one equality among variables.
 *
 * f(X,Y) ∉ X v f(X,Y) ∉ Y v X=Y
 * X ⊊ Y v Y ⊊ X v X=Y
 * X[sk(X,Y)] ≠ Y[sk(X,Y)] v X=Y
 */
bool TheoryFinder::matchKnownExtensionality(const Clause* c) {
  static const unsigned char setCode[] =
    { (unsigned char)Code::CLS,
     (unsigned char)Code::NLIT,0,
      (unsigned char)Code::NEWPRED,0,2,                            // ~member(f(X,Y),X),
      (unsigned char)Code::NEWFUN,0,2,(unsigned char)Code::NEWVAR,0,(unsigned char)Code::NEWVAR,1,(unsigned char)Code::OLDVAR,0,
     (unsigned char)Code::NLIT,1,
      (unsigned char)Code::OLDPRED,0,                              // ~member(f(X,Y),Y),
      (unsigned char)Code::OLDFUN,0,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::OLDVAR,1,(unsigned char)Code::OLDVAR,1,
     (unsigned char)Code::PLIT,2,
      (unsigned char)Code::EQL,(unsigned char)Code::OLDVAR1,0,(unsigned char)Code::OLDVAR1,1,(unsigned char)Code::END}; // X=Y
  static const unsigned char arrayCode[] =
    { (unsigned char)Code::CLS,
     (unsigned char)Code::NLIT,0,
      (unsigned char)Code::EQL,
      (unsigned char)Code::NEWFUN1,0,2,(unsigned char)Code::NEWVAR,0,(unsigned char)Code::NEWFUN,1,2,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::NEWVAR,1,  // sel(X,sk(X,Y) != sel(Y,sk(X,Y)),
      (unsigned char)Code::OLDFUN1,0  ,(unsigned char)Code::OLDVAR,1,(unsigned char)Code::OLDFUN,1  ,(unsigned char)Code::OLDVAR,0,(unsigned char)Code::OLDVAR,1,
     (unsigned char)Code::PLIT,1,
      (unsigned char)Code::EQL,(unsigned char)Code::OLDVAR1,0,(unsigned char)Code::OLDVAR1,1,(unsigned char)Code::END}; // X=Y
  static const unsigned char subsetCode[] =
    { (unsigned char)Code::CLS,
     (unsigned char)Code::NLIT,0,
      (unsigned char)Code::NEWPRED,0,2,(unsigned char)Code::NEWVAR,0,(unsigned char)Code::NEWVAR,1,           // ~subseteq(X,Y),
     (unsigned char)Code::NLIT,1,
      (unsigned char)Code::OLDPRED,0,  (unsigned char)Code::OLDVAR,1,(unsigned char)Code::OLDVAR,0,           // ~subseteq(Y,X),
     (unsigned char)Code::PLIT,2,
      (unsigned char)Code::EQL,(unsigned char)Code::OLDVAR1,0,(unsigned char)Code::OLDVAR1,1,(unsigned char)Code::END}; // X=Y

  switch (c->length()) {
  case 2:
    return matchCode(c, arrayCode);
  case 3:
     return (matchCode(c, setCode) || matchCode(c, subsetCode));
  default:
    return false;
  }
} // matchKnownExtensionality

