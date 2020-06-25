
/*
 * File InterpretedLiteralEvaluator.cpp.
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
 * @file InterpretedLiteralEvaluator.cpp
 * Implements class InterpretedLiteralEvaluator.
 */

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"

#include "Signature.hpp"
#include "Sorts.hpp"
#include "TermIterators.hpp"
#include "Term.hpp"
#include "Theory.hpp"

#include "InterpretedLiteralEvaluator.hpp"

#define IDEBUG 0

namespace Kernel
{
using namespace Lib;

/**
 * We use descendants of this class to evaluate various functions.
 *
 * One function can be evaluated only by one Evaluator object.
 */
class InterpretedLiteralEvaluator::Evaluator
{
public:
  CLASS_NAME(InterpretedLiteralEvaluator::Evaluator);
  USE_ALLOCATOR(InterpretedLiteralEvaluator::Evaluator);
  
  virtual ~Evaluator() {}

  virtual bool canEvaluateFunc(unsigned func) { return false; }
  virtual bool canEvaluatePred(unsigned pred) { return false; }

  virtual bool tryEvaluateFunc(Term* trm, TermList& res) { return false; }
  virtual bool tryEvaluatePred(Literal* trm, bool& res)  { return false; }
};

/**
 * We want to evaluate terms up to AC e.g. (1+a)+1 -> a+2 ... the standard evaluation
 * will not do this. The idea here is to collapse the term tree into a list of terms
 * and, combine together the numbers, and then rebuild a term
 *
 * @author Giles
 * @since 06/12/18
 */
template<class T>
class InterpretedLiteralEvaluator::ACFunEvaluator
   : public Evaluator
{
public:
  CLASS_NAME(InterpretedLiteralEvaluator::ACFunEvaluator<T>);
  USE_ALLOCATOR(InterpretedLiteralEvaluator::ACFunEvaluator<T>);

  ACFunEvaluator(unsigned f, Evaluator* e, Term* id) : _fun(f),_eval(e),_identity(id) {
    T check;
    ASS(theory->tryInterpretConstant(_identity,check));
  }
  unsigned _fun;
  Evaluator* _eval;
  Term* _identity;

  virtual bool canEvaluatePred(unsigned pred) { return false; }
  virtual bool tryEvaluatePred(Literal* trm, bool& res)  { return false; }

  virtual bool canEvaluateFunc(unsigned func) { return func == _fun; }

  virtual bool tryEvaluateFunc(Term* trm, TermList& res) {
#if IDEBUG
     cout << "ACFunEvaluator::tryEvaluateFunc " << trm->toString() << endl;
#endif
    ASS_EQ(trm->functor(),_fun);
    ASS_EQ(trm->arity(),2);

    Stack<TermList*> todo;
    Stack<TermList*> done;
    todo.push(trm->nthArgument(0));
    todo.push(trm->nthArgument(1));

    while(!todo.isEmpty()){
      TermList* t = todo.pop();
      if(t->isTerm() && t->term()->functor() == _fun){
        todo.push(t->term()->nthArgument(0));
        todo.push(t->term()->nthArgument(1));
      }
      else{
       done.push(t);
      }
    }
    ASS(done.length()>1);

    Stack<TermList*>::Iterator it(done);
    Stack<TermList*> keep;
    Term* acc = _identity;
    int acc_cnt = 0;
    while(it.hasNext()){ 
      TermList* t = it.next();
#if IDEBUG
	cout << "considering " << t->toString() << endl;
#endif
      T thing;
      if(t->isTerm() && theory->tryInterpretConstant(t->term(),thing)){
        TermList tmp;
        Term* evalThis = Term::create2(_fun,TermList(acc),*t);
        bool evaluated = _eval->tryEvaluateFunc(evalThis,tmp);
        // if it is not evaluated then there was no change, so copy the term 
        if (!evaluated) {
#if IDEBUG
          cout << "evaluated is false with " << evalThis->toString() << endl;
#endif
          return false;
        }
        else{
#if IDEBUG
	cout << "evaluated to " << tmp.term()->toString() << endl;
#endif
          ASS(tmp.isTerm());
          acc = tmp.term();
          acc_cnt++;
        }
      }
      else{ keep.push(t); }
    } 
    if(keep.length() == done.length() || 
       (keep.length() == done.length()-1 && acc_cnt==1)){ 
#if IDEBUG
	cout << "nothing was reduced" << endl;
#endif
      return false; 
    }
 
    // a bit of a hack, we might need a pointer to this below, to have uniform treatment of all the TermLists
    TermList accT(acc);
 
    // Now build a new term from kept and acc (if not identity)
    // We keep acc if it is identity and if there's no other terms
    if(_identity!=acc || keep.length()==0) {
      keep.push(&accT); // Safe because we just use this pointer locally
    }
    ASS(keep.length()>0);
    Stack<TermList*>::BottomFirstIterator kit(keep);
    res = *kit.next();
    while(kit.hasNext()){
      TermList* t = kit.next(); 
      res = TermList(Term::create2(_fun,res,*t));
    }
    return true;
  }
};


/**
 * Interpreted equality has to be treated specially. We do not have separate
 * predicate symbols for different kinds of equality so the sorts must be 
 * detected and the correct intepretation of constants carried out.
 *
 * Equality is only decided between constant terms.
 *
 * @author Giles
 * @since 10/11/14
 */
class InterpretedLiteralEvaluator::EqualityEvaluator
  : public Evaluator
{
  bool canEvaluatePred(unsigned pred) override {
    return Signature::isEqualityPredicate(pred);
  }

  template<typename T>
  bool checkEquality(Literal* lit, bool& res)
  {
    CALL("InterpretedLiteralEvaluator::EqualityEvaluator::checkEquality");
    T arg1;
    if(!theory->tryInterpretConstant(lit->nthArgument(0)->term(),arg1)){ 
      return false; 
    }
    T arg2;
    if(!theory->tryInterpretConstant(lit->nthArgument(1)->term(),arg2)){ 
      return false;
    }

    res = (arg1 == arg2);

    return true;
  }

  bool tryEvaluatePred(Literal* lit, bool& res) override
  {
    CALL("InterpretedLiteralEvaluator::EqualityEvaluator::tryEvaluatePred");

    try{
      ASS(lit->isEquality());
    
      // We try and interpret the equality as a number of different sorts
      // If it is not an equality between two constants of the same sort the
      // checkEquality function will return false, otherwise res will contain
      // the result of the equality check
      bool okay = checkEquality<IntegerConstantType>(lit,res)  ||
                  checkEquality<RationalConstantType>(lit,res) ||
                  checkEquality<RealConstantType>(lit,res);

     // Also check if the two terms are already equivalent, although that should be captured elsewhere
     // This allows us to return true even if we couldn't interpret lit due to arithmetic exception
     if(lit->nthArgument(0)->term() == lit->nthArgument(1)->term()){
       okay = true;
       res = true;
     } 
#if IDEBUG
      cout << "HERE with " << lit->nthArgument(0)->term() << " and " << lit->nthArgument(1)->term() << endl;
      cout << "HERE with " << lit->nthArgument(0)->term()->toString() << " and " << lit->nthArgument(1)->term()->toString() << endl;
      cout << "okay is " << okay << endl;
#endif
      if(!okay) return false;

      if(lit->isNegative()){ res = !res; }

      return true;

    }
    catch(ArithmeticException&)
    {
      return false;
    }

  }
};

/**
 * An evaluator for dealing with conversions between sorts
 *
 */
class InterpretedLiteralEvaluator::ConversionEvaluator
  : public Evaluator
{
public:
  bool canEvaluateFunc(unsigned func) override
  {
    CALL("InterpretedLiteralEvaluator::ConversionEvaluator::canEvaluateFunc");

    if (!theory->isInterpretedFunction(func)) {
      return false;
    }
    return theory->isConversionOperation(theory->interpretFunction(func));
  }

  virtual bool tryEvaluateFunc(Term* trm, TermList& res) override
  {
    CALL("InterpretedLiteralEvaluator::ConversionEvaluator::tryEvaluateFunc");
    ASS(theory->isInterpretedFunction(trm));

    try {
      Interpretation itp = theory->interpretFunction(trm);
      ASS(theory->isFunction(itp));
      ASS(theory->isConversionOperation(itp));
      ASS_EQ(theory->getArity(itp), 1);

      TermList argTrm = *trm->nthArgument(0);
      switch(itp) {
      case Theory::Interpretation::INT_TO_RAT:
	{
	  IntegerConstantType arg;
	  if (!theory->tryInterpretConstant(argTrm, arg)) { 
	    return false;
	  }
	  RationalConstantType resNum(arg,1);
	  res = TermList(theory->representConstant(resNum));
	  return true;
	}
      case Theory::Interpretation::INT_TO_REAL:
	{
	  IntegerConstantType arg;
	  if (!theory->tryInterpretConstant(argTrm, arg)) {
	    return false;
	  }
	  RealConstantType resNum(RationalConstantType(arg,1));
	  res = TermList(theory->representConstant(resNum));
	  return true;
	}
      case Theory::Interpretation::RAT_TO_INT:
	{
	  RationalConstantType arg;
	  if (!theory->tryInterpretConstant(argTrm, arg)) {
	    return false;
	  }
	  IntegerConstantType resNum = IntegerConstantType::floor(arg);
	  res = TermList(theory->representConstant(resNum));
	  return true;
	}
      case Theory::Interpretation::RAT_TO_REAL:
	{
	  RationalConstantType arg;
	  if (!theory->tryInterpretConstant(argTrm, arg)) {
	    return false;
	  }
	  RealConstantType resNum(arg);
	  res = TermList(theory->representConstant(resNum));
	  return true;
	}
      case Theory::Interpretation::REAL_TO_INT:
	{
	  RealConstantType arg;
	  if (!theory->tryInterpretConstant(argTrm, arg)) {
	    return false;
	  }
	  IntegerConstantType resNum = IntegerConstantType::floor(RationalConstantType(arg));
	  res = TermList(theory->representConstant(resNum));
	  return true;
	}
      case Theory::Interpretation::REAL_TO_RAT:
	{
	  //this is correct only as long as we only represent rational real numbers
	  RealConstantType arg;
	  if (!theory->tryInterpretConstant(argTrm, arg)) {
	    return false;
	  }
	  RationalConstantType resNum(arg);
	  res = TermList(theory->representConstant(resNum));
	return true;
      }

      default:
	ASSERTION_VIOLATION;
      }
    }
    catch(ArithmeticException&)
    {
      return false;
    }
  }
};

/**
 * Evaluates constant theory expressions
 *
 * Evaluators for each sort implement tryEvaluate(Unary/Binary)(Func/Pred) 
 * 
 */
template<class T>
class InterpretedLiteralEvaluator::TypedEvaluator : public Evaluator
{
public:
  typedef T Value;

  TypedEvaluator() {}

  virtual bool isZero(T arg) = 0;
  virtual TermList getZero() = 0;
  virtual bool isOne(T arg) = 0;
  virtual bool isMinusOne(T arg) = 0;

  virtual TermList invert(TermList t) = 0;

  virtual bool isAddition(Interpretation interp) = 0;
  virtual bool isProduct(Interpretation interp) = 0;
  virtual bool isDivision(Interpretation interp) = 0;

  virtual bool canEvaluate(Interpretation interp)
  {
    CALL("InterpretedLiteralEvaluator::TypedEvaluator::canEvaluate");
    
    // This is why we cannot evaluate Equality here... we cannot determine its sort
    if (!theory->hasSingleSort(interp)) { return false; } //To skip conversions and EQUAL

    if (theory->isPolymorphic(interp)) { return false; } // typed evaulator not for polymorphic stuff

    unsigned opSort = theory->getOperationSort(interp);
    return opSort==T::getSort();
  }

  virtual bool tryEvaluateFunc(Term* trm, TermList& res) override
  {
    CALL("InterpretedLiteralEvaluator::tryEvaluateFunc");
    ASS(theory->isInterpretedFunction(trm));

#if IDEBUG
    cout << "try evaluate " << trm->toString() << endl;
#endif

    try {
      Interpretation itp = theory->interpretFunction(trm);
      ASS(theory->isFunction(itp));
      unsigned arity = theory->getArity(itp);

      if (arity!=1 && arity!=2) {
	INVALID_OPERATION("unsupported arity of interpreted operation: "+Int::toString(arity));
      }
      T resNum;
      TermList arg1Trm = *trm->nthArgument(0);
      T arg1;
      if (arity==1) {
        if (theory->tryInterpretConstant(arg1Trm, arg1)){
          if (!tryEvaluateUnaryFunc(itp, arg1, resNum)) { return false;}
        }
        else{ return false;}
      }
      else if(arity==2){
        // If one argument is not a constant and the other is zero, one or minus one then
        // we might have some special cases

        T arg2;
        TermList arg2Trm = *trm->nthArgument(1);

        bool specialCase = true;
        T conArg;
        TermList nonConTerm;
        if (theory->tryInterpretConstant(arg1Trm, arg1) && (isZero(arg1) || isOne(arg1) || isMinusOne(arg1)) && 
            !theory->tryInterpretConstant(arg2Trm, arg2)) {
         conArg = arg1;
         nonConTerm = arg2Trm;
        }
        else if(theory->tryInterpretConstant(arg2Trm, arg2) && (isZero(arg2) || isOne(arg2) || isMinusOne(arg2)) && 
            !theory->tryInterpretConstant(arg1Trm, arg1)) {
         conArg = arg2;
         nonConTerm = arg1Trm;
        }
        else{
          specialCase = false;
        }
        if(specialCase){
#if IDEBUG
	cout << "special case" << endl;

#endif
 
          //Special case where itp is division and arg2 is '1'
          //   Important... this is a non-symmetric case!
          if(theory->tryInterpretConstant(arg2Trm, arg2) && isOne(arg2) && isDivision(itp)){
            res = arg1Trm;
            return true;
          }
          //Special case where itp is addition and conArg is '0'
          if(isZero(conArg) && isAddition(itp)){
            res = nonConTerm;
            return true;
          }
          //Special case where itp is multiplication and conArg  is '1'
          if(isOne(conArg) && isProduct(itp)){
            res = nonConTerm;
            return true;
          }
          //Special case where itp is multiplication and conArg  is '-1'
          if(isMinusOne(conArg) && isProduct(itp)){
            res = invert(nonConTerm); 
            return true;
          }
          //Special case where itp is multiplication and conArg is '0'
          if(isZero(conArg) && isProduct(itp)){
            res = getZero();
            return true;
          }
        }
        if(theory->tryInterpretConstant(arg1Trm, arg1) && theory->tryInterpretConstant(arg2Trm, arg2)){
	  if (!tryEvaluateBinaryFunc(itp, arg1, arg2, resNum)) { return false;}
        }
        else{ return false;}
      }
      res = TermList(theory->representConstant(resNum));
      return true;
    }
    catch(ArithmeticException)
    {
#if IDEBUG
       cout << "ArithmeticException" << endl;
#endif
      return false;
    }
  }

  virtual bool tryEvaluatePred(Literal* lit, bool& res) override
  {
    CALL("InterpretedLiteralEvaluator::tryEvaluatePred");
    ASS(theory->isInterpretedPredicate(lit));

    try {
      Interpretation itp = theory->interpretPredicate(lit);
      ASS(!theory->isFunction(itp));
      unsigned arity = theory->getArity(itp);

      if (arity!=1 && arity!=2) {
	INVALID_OPERATION("unsupported arity of interpreted operation: "+Int::toString(arity));
      }
      TermList arg1Trm = *lit->nthArgument(0);
      T arg1;
      if (!theory->tryInterpretConstant(arg1Trm, arg1)) { return false; }
      if (arity==1) {
	if (!tryEvaluateUnaryPred(itp, arg1, res)) { return false;}
      }
      else {
	TermList arg2Trm = *lit->nthArgument(1);
	T arg2;
	if (!theory->tryInterpretConstant(arg2Trm, arg2)) { return false; }
	if (!tryEvaluateBinaryPred(itp, arg1, arg2, res)) { return false;}
      }
      if (lit->isNegative()) {
	res = !res;
      }
      return true;
    }
    catch(ArithmeticException&)
    {
      return false;
    }

  }

  bool canEvaluateFunc(unsigned func) override
  {
    CALL("InterpretedLiteralEvaluator::TypedEvaluator::canEvaluateFunc");

    if (!theory->isInterpretedFunction(func)) {
      return false;
    }
    Interpretation interp = theory->interpretFunction(func);
    return canEvaluate(interp);
  }

  bool canEvaluatePred(unsigned pred) override
  {
    CALL("InterpretedLiteralEvaluator::TypedEvaluator::canEvaluatePred");

    if (!theory->isInterpretedPredicate(pred)) {
      return false;
    }
    Interpretation interp = theory->interpretPredicate(pred);
    return canEvaluate(interp);
  }

protected:
  virtual bool tryEvaluateUnaryFunc(Interpretation op, const T& arg, T& res)
  { return false; }
  virtual bool tryEvaluateBinaryFunc(Interpretation op, const T& arg1, const T& arg2, T& res)
  { return false; }

  virtual bool tryEvaluateUnaryPred(Interpretation op, const T& arg1, bool& res)
  { return false; }
  virtual bool tryEvaluateBinaryPred(Interpretation op, const T& arg1, const T& arg2, bool& res)
  { return false; }
};

/**
 * Evaluates integer functions
 */
class InterpretedLiteralEvaluator::IntEvaluator : public TypedEvaluator<IntegerConstantType>
{
protected:

  virtual bool isZero(IntegerConstantType arg){ return arg.toInner()==0;}
  virtual TermList getZero(){ return TermList(theory->representConstant(IntegerConstantType(0))); }
  virtual bool isOne(IntegerConstantType arg){ return arg.toInner()==1;}
  virtual bool isMinusOne(IntegerConstantType arg){ return arg.toInner()==-1;}

  virtual TermList invert(TermList t){ 
    unsigned um = env.signature->getInterpretingSymbol(Theory::Interpretation::INT_UNARY_MINUS);
    return TermList(Term::create1(um,t)); 
  }

  virtual bool isAddition(Interpretation interp){ return interp==Theory::Interpretation::INT_PLUS; }
  virtual bool isProduct(Interpretation interp){ return interp==Theory::Interpretation::INT_MULTIPLY;}
  virtual bool isDivision(Interpretation interp){ 
    return interp==Theory::Interpretation::INT_QUOTIENT_E || interp==Theory::Interpretation::INT_QUOTIENT_T || 
           interp==Theory::Interpretation::INT_QUOTIENT_F; 
  }

  virtual bool tryEvaluateUnaryFunc(Interpretation op, const Value& arg, Value& res)
  {
    CALL("InterpretedLiteralEvaluator::IntEvaluator::tryEvaluateUnaryFunc");

    switch(op) {
    case Theory::Interpretation::INT_UNARY_MINUS:
      res = -arg;
      return true;
    case Theory::Interpretation::INT_ABS:
      if (arg < 0) {
        res = -arg;
      } else {
        res = arg;
      }
      return true;
    case Theory::Interpretation::INT_SUCCESSOR:
      res = arg+1;
      return true;
    case Theory::Interpretation::INT_FLOOR:
    case Theory::Interpretation::INT_CEILING:
    case Theory::Interpretation::INT_TRUNCATE:
    case Theory::Interpretation::INT_ROUND:
       // For integers these do nothing
      res = arg;
      return true;
    default:
      return false;
    }
  }

  virtual bool tryEvaluateBinaryFunc(Interpretation op, const Value& arg1,
      const Value& arg2, Value& res)
  {
    CALL("InterpretedLiteralEvaluator::IntEvaluator::tryEvaluateBinaryFunc");

    switch(op) {
    case Theory::Interpretation::INT_PLUS:
      res = arg1+arg2;
      return true;
    case Theory::Interpretation::INT_MINUS:
      res = arg1-arg2;
      return true;
    case Theory::Interpretation::INT_MULTIPLY:
      res = arg1*arg2;
      return true;
    case Theory::Interpretation::INT_QUOTIENT_E:
      res = arg1.quotientE(arg2); // should be equivalent to arg1/arg2
      return true;
    case Theory::Interpretation::INT_QUOTIENT_T:
      res = arg1.quotientT(arg2);
      return true;
    case Theory::Interpretation::INT_QUOTIENT_F:
      res = arg1.quotientF(arg2);
      return true;
    // The remainder is left - (quotient * right)
    case Theory::Interpretation::INT_REMAINDER_E:
      res = arg1 - (arg1.quotientE(arg2)*arg2);
      return true;
    case Theory::Interpretation::INT_REMAINDER_T:
      res = arg1 - (arg1.quotientT(arg2)*arg2);
      return true;
    case Theory::Interpretation::INT_REMAINDER_F:
      res = arg1 - (arg1.quotientF(arg2)*arg2);
      return true;
    default:
      return false;
    }
  }

  virtual bool tryEvaluateBinaryPred(Interpretation op, const Value& arg1,
      const Value& arg2, bool& res)
  {
    CALL("InterpretedLiteralEvaluator::IntEvaluator::tryEvaluateBinaryPred");

    switch(op) {
    case Theory::Interpretation::INT_GREATER:
      res = arg1>arg2;
      return true;
    case Theory::Interpretation::INT_GREATER_EQUAL:
      res = arg1>=arg2;
      return true;
    case Theory::Interpretation::INT_LESS:
      res = arg1<arg2;
      return true;
    case Theory::Interpretation::INT_LESS_EQUAL:
      res = arg1<=arg2;
      return true;
    case Theory::Interpretation::INT_DIVIDES:
      res = (arg2%arg1)==0;
      return true;
    default:
      return false;
    }
  }
};

/**
 * Evaluations rational functions
 */
class InterpretedLiteralEvaluator::RatEvaluator : public TypedEvaluator<RationalConstantType>
{
protected:
  virtual bool isZero(RationalConstantType arg){ return arg.isZero();}
  virtual TermList getZero(){ return TermList(theory->representConstant(RationalConstantType(0,1))); }
  virtual bool isOne(RationalConstantType arg) { return arg.numerator()==arg.denominator();}
  virtual bool isMinusOne(RationalConstantType arg) { return arg.numerator() == -arg.denominator();}

  virtual TermList invert(TermList t){ 
    unsigned um = env.signature->getInterpretingSymbol(Theory::Interpretation::RAT_UNARY_MINUS);
    return TermList(Term::create1(um,t));                      
  }

  virtual bool isAddition(Interpretation interp){ return interp==Theory::Interpretation::RAT_PLUS; }
  virtual bool isProduct(Interpretation interp){ return interp==Theory::Interpretation::RAT_MULTIPLY;}
  virtual bool isDivision(Interpretation interp){ 
    return interp==Theory::Interpretation::RAT_QUOTIENT || interp==Theory::Interpretation::RAT_QUOTIENT_E || 
           interp==Theory::Interpretation::RAT_QUOTIENT_T || interp==Theory::Interpretation::RAT_QUOTIENT_F;
  }

  virtual bool tryEvaluateUnaryFunc(Interpretation op, const Value& arg, Value& res)
  {
    CALL("InterpretedLiteralEvaluator::RatEvaluator::tryEvaluateUnaryFunc");

    switch(op) {
    case Theory::Interpretation::RAT_UNARY_MINUS:
      res = -arg;
      return true;
    case Theory::Interpretation::RAT_FLOOR:
      res = arg.floor();
      return true;
    case Theory::Interpretation::RAT_CEILING:
      res = arg.ceiling();
      return true;
    case Theory::Interpretation::RAT_TRUNCATE:
      res = arg.truncate();
      return true;
    default:
      return false;
    }
  }

  virtual bool tryEvaluateBinaryFunc(Interpretation op, const Value& arg1,
      const Value& arg2, Value& res)
  {
    CALL("InterpretedLiteralEvaluator::RatEvaluator::tryEvaluateBinaryFunc");

    switch(op) {
    case Theory::Interpretation::RAT_PLUS:
      res = arg1+arg2;
      return true;
    case Theory::Interpretation::RAT_MINUS:
      res = arg1-arg2;
      return true;
    case Theory::Interpretation::RAT_MULTIPLY:
      res = arg1*arg2;
      return true;
    case Theory::Interpretation::RAT_QUOTIENT:
      res = arg1/arg2;
      return true;
    case Theory::Interpretation::RAT_QUOTIENT_E:
      res = arg1.quotientE(arg2);
      return true;
    case Theory::Interpretation::RAT_QUOTIENT_T:
      res = arg1.quotientT(arg2);
      return true;
    case Theory::Interpretation::RAT_QUOTIENT_F:
      res = arg1.quotientF(arg2);
      return true;
    // The remainder is left - (quotient * right)
    case Theory::Interpretation::RAT_REMAINDER_E:
      res = arg1 - (arg1.quotientE(arg2)*arg2);
      return true;
    case Theory::Interpretation::RAT_REMAINDER_T:
      res = arg1 - (arg1.quotientT(arg2)*arg2);
      return true;
    case Theory::Interpretation::RAT_REMAINDER_F:
      res = arg1 - (arg1.quotientF(arg2)*arg2);
      return true;
    default:
      return false;
    }
  }

  virtual bool tryEvaluateBinaryPred(Interpretation op, const Value& arg1,
      const Value& arg2, bool& res)
  {
    CALL("InterpretedLiteralEvaluator::RatEvaluator::tryEvaluateBinaryPred");

    switch(op) {
    case Theory::Interpretation::RAT_GREATER:
      res = arg1>arg2;
      return true;
    case Theory::Interpretation::RAT_GREATER_EQUAL:
      res = arg1>=arg2;
      return true;
    case Theory::Interpretation::RAT_LESS:
      res = arg1<arg2;
      return true;
    case Theory::Interpretation::RAT_LESS_EQUAL:
      res = arg1<=arg2;
      return true;
    default:
      return false;
    }
  }

  virtual bool tryEvaluateUnaryPred(Interpretation op, const Value& arg1,
      bool& res)
  {
    CALL("InterpretedLiteralEvaluator::RatEvaluator::tryEvaluateBinaryPred");

    switch(op) {
    case Theory::Interpretation::RAT_IS_INT:
      res = arg1.isInt();
      return true;
    default:
      return false;
    }
  }
};

/**
 * Evaluates real functions. 
 * As reals are represented as rationals the operations are for reals.
 * See Kernel/Theory.hpp for how these operations are defined
 */
class InterpretedLiteralEvaluator::RealEvaluator : public TypedEvaluator<RealConstantType>
{
protected:
  virtual bool isZero(RealConstantType arg){ return arg.isZero();}
  virtual TermList getZero(){ return TermList(theory->representConstant(RealConstantType(RationalConstantType(0, 1)))); }
  virtual bool isOne(RealConstantType arg) { return arg.numerator()==arg.denominator();}
  virtual bool isMinusOne(RealConstantType arg) { return arg.numerator() == -arg.denominator();}

  virtual TermList invert(TermList t){ 
    unsigned um = env.signature->getInterpretingSymbol(Theory::Interpretation::REAL_UNARY_MINUS);
    return TermList(Term::create1(um,t));                      
  }

  virtual bool isAddition(Interpretation interp){ return interp==Theory::Interpretation::REAL_PLUS; }
  virtual bool isProduct(Interpretation interp){ return interp==Theory::Interpretation::REAL_MULTIPLY;}
  virtual bool isDivision(Interpretation interp){ 
    return interp==Theory::Interpretation::REAL_QUOTIENT || interp==Theory::Interpretation::REAL_QUOTIENT_E ||
           interp==Theory::Interpretation::REAL_QUOTIENT_T || interp==Theory::Interpretation::REAL_QUOTIENT_F;
  }

  virtual bool tryEvaluateUnaryFunc(Interpretation op, const Value& arg, Value& res)
  {
    CALL("InterpretedLiteralEvaluator::RealEvaluator::tryEvaluateUnaryFunc");

    switch(op) {
    case Theory::Interpretation::REAL_UNARY_MINUS:
      res = -arg;
      return true;
    case Theory::Interpretation::REAL_FLOOR:
      res = arg.floor();
      return true;
    case Theory::Interpretation::REAL_CEILING:
      res = arg.ceiling();
      return true;
    case Theory::Interpretation::REAL_TRUNCATE:
      res = arg.truncate();
      return true;
    default:
      return false;
    }
  }

  virtual bool tryEvaluateBinaryFunc(Interpretation op, const Value& arg1,
      const Value& arg2, Value& res)
  {
    CALL("InterpretedLiteralEvaluator::RealEvaluator::tryEvaluateBinaryFunc");

    switch(op) {
    case Theory::Interpretation::REAL_PLUS:
      res = arg1+arg2;
      return true;
    case Theory::Interpretation::REAL_MINUS:
      res = arg1-arg2;
      return true;
    case Theory::Interpretation::REAL_MULTIPLY:
      res = arg1*arg2;
      return true;
    case Theory::Interpretation::REAL_QUOTIENT:
      res = arg1/arg2;
      return true;
    case Theory::Interpretation::REAL_QUOTIENT_E:
      res = arg1.quotientE(arg2);
      return true;
    case Theory::Interpretation::REAL_QUOTIENT_T:
      res = arg1.quotientT(arg2);
      return true;
    case Theory::Interpretation::REAL_QUOTIENT_F:
      res = arg1.quotientF(arg2);
      return true;
    // The remainder is left - (quotient * right)
    case Theory::Interpretation::REAL_REMAINDER_E:
      res = arg1 - (arg1.quotientE(arg2)*arg2);
      return true;
    case Theory::Interpretation::REAL_REMAINDER_T:
      res = arg1 - (arg1.quotientT(arg2)*arg2);
      return true;
    case Theory::Interpretation::REAL_REMAINDER_F:
      res = arg1 - (arg1.quotientF(arg2)*arg2);
      return true;
    default:
      return false;
    }
  }

  virtual bool tryEvaluateBinaryPred(Interpretation op, const Value& arg1,
      const Value& arg2, bool& res)
  {
    CALL("InterpretedLiteralEvaluator::RealEvaluator::tryEvaluateBinaryPred");

    switch(op) {
    case Theory::Interpretation::REAL_GREATER:
      res = arg1>arg2;
      return true;
    case Theory::Interpretation::REAL_GREATER_EQUAL:
      res = arg1>=arg2;
      return true;
    case Theory::Interpretation::REAL_LESS:
      res = arg1<arg2;
      return true;
    case Theory::Interpretation::REAL_LESS_EQUAL:
      res = arg1<=arg2;
      return true;
    default:
      return false;
    }
  }

  virtual bool tryEvaluateUnaryPred(Interpretation op, const Value& arg1,
      bool& res)
  {
    CALL("InterpretedLiteralEvaluator::RealEvaluator::tryEvaluateBinaryPred");

    switch(op) {
    case Theory::Interpretation::REAL_IS_INT:
      res = arg1.isInt();
      return true;
    case Theory::Interpretation::REAL_IS_RAT:
      //this is true as long as we can evaluate only rational reals.
      res = true;
      return true;
    default:
      return false;
    }
  }

};

////////////////////////////////
// InterpretedLiteralEvaluator
//
// This is where the evaluators defined above are used.

InterpretedLiteralEvaluator::InterpretedLiteralEvaluator()
{
  CALL("InterpretedLiteralEvaluator::InterpretedLiteralEvaluator");

  // For an evaluator to be used it must be pushed onto _evals
  // We search this list, calling canEvaluate on each evaluator
  // An invariant we want to maintain is that for any literal only one
  //  Evaluator will return true for canEvaluate
  _evals.push(new IntEvaluator());
  _evals.push(new RatEvaluator());
  _evals.push(new RealEvaluator());
  _evals.push(new ConversionEvaluator());
  _evals.push(new EqualityEvaluator());

  if(env.options->useACeval()){

  // Special AC evaluators are added to be tried first for Plus and Multiply
  _evals.push(new ACFunEvaluator<IntegerConstantType>(
		env.signature->getInterpretingSymbol(Theory::Interpretation::INT_PLUS),
		new IntEvaluator(),
		theory->representConstant(IntegerConstantType(0)))); 
  _evals.push(new ACFunEvaluator<IntegerConstantType>(
                env.signature->getInterpretingSymbol(Theory::Interpretation::INT_MULTIPLY),
                new IntEvaluator(),
                theory->representConstant(IntegerConstantType(1))));

  _evals.push(new ACFunEvaluator<RationalConstantType>(
                env.signature->getInterpretingSymbol(Theory::Interpretation::RAT_PLUS),
                new RatEvaluator(),
                theory->representConstant(RationalConstantType(0))));
  _evals.push(new ACFunEvaluator<RationalConstantType>(
                env.signature->getInterpretingSymbol(Theory::Interpretation::RAT_MULTIPLY),
                new RatEvaluator(),
                theory->representConstant(RationalConstantType(1))));

  _evals.push(new ACFunEvaluator<RealConstantType>(
                env.signature->getInterpretingSymbol(Theory::Interpretation::REAL_PLUS),
                new RealEvaluator(),
                theory->representConstant(RealConstantType(RationalConstantType(0)))));
  _evals.push(new ACFunEvaluator<RealConstantType>(
                env.signature->getInterpretingSymbol(Theory::Interpretation::REAL_MULTIPLY),
                new RealEvaluator(),
                theory->representConstant(RealConstantType(RationalConstantType(1)))));

  }

  _funEvaluators.ensure(0);
  _predEvaluators.ensure(0);

}

InterpretedLiteralEvaluator::~InterpretedLiteralEvaluator()
{
  CALL("InterpretedEvaluation::LiteralSimplifier::~LiteralSimplifier");

  while (_evals.isNonEmpty()) {
    delete _evals.pop();
  }
}

/**
 * This checks if a literal is 'balancable' i.e. can be put into the form term=constant or term=var
 * 
 * This is still an experimental process and will be expanded/reworked later
 *
 * @author Giles
 * @since 11/11/14
 */
bool InterpretedLiteralEvaluator::balancable(Literal* lit)
{
  CALL("InterpretedLiteralEvaluator::balancable");
  // Check that lit is compatible with this balancing operation
  // One thing that we cannot check, but assume is that it has already been simplified once
  // balance applies further checks

  // lit must be an interpretted predicate
  if(!theory->isInterpretedPredicate(lit->functor())) return false;

  // the perdicate must be binary
  Interpretation ip = theory->interpretPredicate(lit->functor());
  if(theory->getArity(ip)!=2) return false;

  // one side must be a constant and the other interpretted
  // the other side can contain at most one variable or uninterpreted subterm 
  // but we do not check this second condition here, instead we detect it in balance
  TermList t1 = *lit->nthArgument(0);
  TermList t2 = *lit->nthArgument(1);

  bool t1Number = theory->isInterpretedNumber(t1);
  bool t2Number = theory->isInterpretedNumber(t2);

  if(!t1Number && !t2Number){ return false; } // cannot balance
  if(t1Number && t2Number){ return true; } // already balanced

  // so here exactly one of t1Number and t2Number is true

  if(t1Number){
    if(t2.isVar()){ return false;} // already balanced
    if(!theory->isInterpretedFunction(t2)){ return false;} // cannot balance
  }
  if(t2Number){
    if(t1.isVar()){ return false;} // already balanced
    if(!theory->isInterpretedFunction(t1)){ return false;} // cannot balance
  }

  return true;
}

/**
 * This attempts to 'balance' a literal i.e. put it into the form term=constant
 *
 * The current implementation is only applicable to a restricted set of cases.
 *
 * This is still an experimental process and will be expanded/reworked later
 *
 * @author Giles
 * @since 11/11/14
 */
bool InterpretedLiteralEvaluator::balance(Literal* lit,Literal*& resLit,Stack<Literal*>& sideConditions)
{
  CALL("InterpretedLiteralEvaluator::balance");
  ASS(balancable(lit));

#if IDEBUG
  cout << "try balance " << lit->toString() << endl;
#endif

  ASS(theory->isInterpretedPredicate(lit->functor()));

  // at the end this tells us if the predicate needs to be swapped, only applies if non-equality
  bool swap = false; 

  // only want lesseq and equality
  if(lit->arity()!=2) return false;

  TermList t1;
  TermList t2;
  // ensure that t1 is the constant
  if(theory->isInterpretedNumber(*lit->nthArgument(0))){
    t1 = *lit->nthArgument(0); t2 = *lit->nthArgument(1);
  }else{
    t1 = *lit->nthArgument(1); t2 = *lit->nthArgument(0);
    swap=true;
  }
  // so we have t1 a constant and t2 something that has an interpreted function at the top

  Signature::Symbol* conSym = env.signature->getFunction(t1.term()->functor());
  unsigned srt = 0;
  if(conSym->integerConstant()) srt = (unsigned)Sorts::DefaultSorts::SRT_INTEGER;
  else if(conSym->rationalConstant()) srt = (unsigned)Sorts::DefaultSorts::SRT_RATIONAL;
  else if(conSym->realConstant()) srt = (unsigned)Sorts::DefaultSorts::SRT_REAL;
  else{
     ASSERTION_VIOLATION_REP(t1);
    return false;// can't work out the sort, that's odd!
  }

  // unwrap t2, applying the wrappings to t1 until we get to something we can't unwrap
  // this updates t1 and t2 as we go

  // This relies on the fact that a simplified literal with a single non-constant
  // subterm will look like f(c,f(c,f(c,t)))=c
  // If we cannot invert an interpreted function f then we fail

  bool modified = false;

  while(theory->isInterpretedFunction(t2)){
    TermList* args = t2.term()->args();
    
    // find which arg of t2 is the non_constant bit, this is what we are unwrapping 
    TermList* to_unwrap=0;
    while(args->isNonEmpty()){
      if(!theory->isInterpretedNumber(*args)){
        if(to_unwrap){
          return false; // If there is more than one non-constant term this will not work
        }
        to_unwrap=args;
      } 
      args= args->next();
    }
    //Should not happen if balancable passed and it was simplified
    if(!to_unwrap){ return false;} 
    
    // Now we do a case on the functor of t2
    Term* t2term = t2.term();
    Interpretation t2interp = theory->interpretFunction(t2term->functor());
    TermList result;
    bool okay=true;
    switch(t2interp){
      case Theory::Interpretation::INT_PLUS:
        okay=balancePlus(Theory::Interpretation::INT_PLUS,Theory::Interpretation::INT_UNARY_MINUS,t2term,to_unwrap,t1,result);
        break;
      case Theory::Interpretation::RAT_PLUS:
        okay=balancePlus(Theory::Interpretation::RAT_PLUS,Theory::Interpretation::RAT_UNARY_MINUS,t2term,to_unwrap,t1,result);
        break;
      case Theory::Interpretation::REAL_PLUS:
        okay=balancePlus(Theory::Interpretation::REAL_PLUS,Theory::Interpretation::REAL_UNARY_MINUS,t2term,to_unwrap,t1,result);
        break;

      case Theory::Interpretation::INT_MULTIPLY: 
      {
        okay=balanceIntegerMultiply(t2term,to_unwrap,t1,result,swap,sideConditions);
        break;
      }
      case Theory::Interpretation::RAT_MULTIPLY:
      {
        RationalConstantType zero(0,1);
        okay=balanceMultiply(Theory::Interpretation::RAT_QUOTIENT,zero,t2term,to_unwrap,t1,result,swap,sideConditions);
        break;
      }
      case Theory::Interpretation::REAL_MULTIPLY:
      {
        RealConstantType zero(RationalConstantType(0, 1));
        okay=balanceMultiply(Theory::Interpretation::REAL_QUOTIENT,zero,t2term,to_unwrap,t1,result,swap,sideConditions);
        break;
       }

      case Theory::Interpretation::RAT_QUOTIENT:
        okay=balanceDivide(Theory::Interpretation::RAT_MULTIPLY,t2term,to_unwrap,t1,result,swap,sideConditions);
        break;
      case Theory::Interpretation::REAL_QUOTIENT:
        okay=balanceDivide(Theory::Interpretation::REAL_MULTIPLY,t2term,to_unwrap,t1,result,swap,sideConditions);
        break;

      default:
        okay=false;
        break;
    }
    if(!okay){
        // cannot invert this one, finish here, either by giving up or going to the end
        if(!modified) return false;
        goto endOfUnwrapping; 
    }

    // update t1
    t1=result;
    // set t2 to the non-constant argument
    t2 = *to_unwrap;
    modified = true;
  }
endOfUnwrapping:

  //Evaluate t1
  // We have rearranged things so that t2 is a non-constant term and t1 is a number
  // of interprted functions applied to some constants. By evaluating t1 we will
  //  get a constant (unless evaluation is not possible)

  // don't swap equality
  if(lit->functor()==0){
   resLit = TermTransformerTransformTransformed::transform(Literal::createEquality(lit->polarity(),t2,t1,srt));
  }
  else{
    // important, need to preserve the ordering of t1 and t2 in the original!
    if(swap){
      resLit = TermTransformerTransformTransformed::transform(Literal::create2(lit->functor(),lit->polarity(),t2,t1));
    }else{
      resLit = TermTransformerTransformTransformed::transform(Literal::create2(lit->functor(),lit->polarity(),t1,t2));
    }
  }
  return true;
}


bool InterpretedLiteralEvaluator::balancePlus(Interpretation plus, Interpretation unaryMinus, 
                                              Term* AplusB, TermList* A, TermList C, TermList& result)
{
  CALL("InterpretedLiteralEvaluator::balancePlus");

    unsigned um = env.signature->getInterpretingSymbol(unaryMinus);
    unsigned ip = env.signature->getInterpretingSymbol(plus);
    TermList* B = 0;
    if(AplusB->nthArgument(0)==A){
      B = AplusB->nthArgument(1);
    }
    else{
      ASS(AplusB->nthArgument(1)==A);
      B = AplusB->nthArgument(0);
    }

    TermList mB(Term::create1(um,*B));
    result = TermList(Term::create2(ip,C,mB));
    return true;
}

template<typename ConstantType>
bool InterpretedLiteralEvaluator::balanceMultiply(Interpretation divide,ConstantType zero, 
                                                  Term* AmultiplyB, TermList* A, TermList C, TermList& result,
                                                  bool& swap, Stack<Literal*>& sideConditions)
{
    CALL("InterpretedLiteralEvaluator::balanceMultiply");
    unsigned srt = theory->getOperationSort(divide); 
    ASS(srt == (unsigned)Sorts::DefaultSorts::SRT_REAL || srt == (unsigned)Sorts::DefaultSorts::SRT_RATIONAL); 

    unsigned div = env.signature->getInterpretingSymbol(divide);
    TermList* B = 0;
    if(AmultiplyB->nthArgument(0)==A){
      B = AmultiplyB->nthArgument(1);
    }
    else{
      ASS(AmultiplyB->nthArgument(1)==A);
      B = AmultiplyB->nthArgument(0);
    }
    result = TermList(Term::create2(div,C,*B));

    ConstantType bcon;
    if(theory->tryInterpretConstant(*B,bcon)){
      if(bcon.isZero()) return false;
      if(bcon.isNegative()){ swap=!swap; } // switch the polarity of an inequality if we're under one
      return true;
    }
    // Unsure exactly what the best thing to do here, so for now give up
    // This means we only balance when we have a constant on the variable side
    return false;

    // if B is not a constant we need to ensure that B!=0
    //Literal* notZero = Literal::createEquality(false,B,zero,srt);
    //sideConditions.push(notZero);
    //result = TermList(Term::create2(div,C,*B);
    //return true;
}

bool InterpretedLiteralEvaluator::balanceIntegerMultiply(
                                                  Term* AmultiplyB, TermList* A, TermList C, TermList& result,
                                                  bool& swap, Stack<Literal*>& sideConditions)
{
    CALL("InterpretedLiteralEvaluator::balanceIntegerMultiply");

    // only works if we in the end divid a number by a number
    IntegerConstantType ccon;
    if(!theory->tryInterpretConstant(C,ccon)){ return false; }

    // we are going to use rounding division but ensure that it is non-rounding
    unsigned div = env.signature->getInterpretingSymbol(Theory::Interpretation::INT_QUOTIENT_E);
    TermList* B = 0;
    if(AmultiplyB->nthArgument(0)==A){
      B = AmultiplyB->nthArgument(1);
    }
    else{
      ASS(AmultiplyB->nthArgument(1)==A);
      B = AmultiplyB->nthArgument(0);
    }
    result = TermList(Term::create2(div,C,*B));

    IntegerConstantType bcon;
    if(theory->tryInterpretConstant(*B,bcon)){
      if(bcon.isZero()){ return false; }
      if(!bcon.divides(ccon)){ return false;}
      if(bcon.isNegative()){ swap=!swap; } // switch the polarity of an inequality if we're under one
      return true;
    }
    return false;
}

bool InterpretedLiteralEvaluator::balanceDivide(Interpretation multiply, 
                       Term* AoverB, TermList* A, TermList C, TermList& result, bool& swap, Stack<Literal*>& sideConditions)
{
    CALL("InterpretedLiteralEvaluator::balanceDivide");
    unsigned srt = theory->getOperationSort(multiply); 
    ASS(srt == (unsigned)Sorts::DefaultSorts::SRT_REAL || srt == (unsigned)Sorts::DefaultSorts::SRT_RATIONAL);

    unsigned mul = env.signature->getInterpretingSymbol(multiply);
    if(AoverB->nthArgument(0)!=A)return false;

    TermList* B = AoverB->nthArgument(1);

    result = TermList(Term::create2(mul,C,*B));

    RationalConstantType bcon;
    if(theory->tryInterpretConstant(*B,bcon)){
      ASS(!bcon.isZero());
      if(bcon.isNegative()){ swap=!swap; } // switch the polarity of an inequality if we're under one
      return true;
    }
    // Unsure exactly what the best thing to do here, so for now give up
    // This means we only balance when we have a constant on the variable side
    return false;    
}

/**
 * Used to evaluate a literal, setting isConstant, resLit and resConst in the process
 *
 * Returns true if it has been evaluated, in which case resLit is set 
 * isConstant is true if the literal predicate evaluates to a constant value
 * resConst is set iff isConstant and gives the constant value (true/false) of resLit 
 */
bool InterpretedLiteralEvaluator::evaluate(Literal* lit, bool& isConstant, Literal*& resLit, bool& resConst,Stack<Literal*>& sideConditions)
{
  CALL("InterpretedLiteralEvaluator::evaluate");

#if IDEBUG
  cout << "evaluate " << lit->toString() << endl;
#endif

  // This tries to transform each subterm using tryEvaluateFunc (see transform Subterm below)
  resLit = TermTransformerTransformTransformed::transform(lit);

#if IDEBUG
  cout << "transformed " << resLit->toString() << endl;
#endif

  // If it can be balanced we balance it
  // A predicate on constants will not be balancable
  if(balancable(resLit)){
      Literal* new_resLit=resLit;
      bool balance_result = balance(resLit,new_resLit,sideConditions);
      ASS(balance_result || resLit==new_resLit);
      resLit=new_resLit;
  }
#if IDEBUG
  else{ cout << "NOT" << endl; }
#endif

  // If resLit contains variables the predicate cannot be interpreted
  VariableIterator vit(lit);
  if(vit.hasNext()){
    isConstant=false;
    return (lit!=resLit);
  }
  // If resLit contains uninterpreted functions then it cannot be interpreted
  TermFunIterator tit(lit);
  ASS(tit.hasNext()); tit.next(); // pop off literal symbol
  while(tit.hasNext()){
    unsigned f = tit.next();
    if(!env.signature->getFunction(f)->interpreted()){
      isConstant=false;
      return (lit!=resLit);
    } 
  }
#if IDEBUG
  cout << resLit->toString()<< " is ground and interpreted, evaluating..." << endl;
#endif

  unsigned pred = resLit->functor();

  // Now we try and evaluate the predicate
  Evaluator* predEv = getPredEvaluator(pred);
  if (predEv) {
    if (predEv->tryEvaluatePred(resLit, resConst)) {
#if IDEBUG
        cout << "pred evaluated " << resConst << endl;
#endif
	isConstant = true;
	return true;
    }
  }
#if IDEBUG
	cout << "pred evaluation failed" << endl;
#endif
  if (resLit!=lit) {
    isConstant = false;
    return true;
  }
  return false;
}

/**
 * This attempts to evaluate each subterm.
 * See Kernel/TermTransformerTransformTransformed for how it is used.
 * Terms are evaluated bottom-up
 */
TermList InterpretedLiteralEvaluator::transformSubterm(TermList trm)
{
  CALL("InterpretedLiteralEvaluator::transformSubterm");

#if IDEBUG
  cout << "transformSubterm for " << trm.toString() << endl;
#endif

  if (!trm.isTerm()) { return trm; }
  Term* t = trm.term();
  unsigned func = t->functor();

  Evaluator* funcEv = getFuncEvaluator(func);
  if (funcEv) {
    TermList res;
    if (funcEv->tryEvaluateFunc(t, res)) {
	return res;
    }
  }
  return trm;
}

/**
 * This searches for an Evaluator for a function
 */
InterpretedLiteralEvaluator::Evaluator* InterpretedLiteralEvaluator::getFuncEvaluator(unsigned func)
{
  CALL("InterpretedLiteralEvaluator::getFuncEvaluator");

  if (func>=_funEvaluators.size()) {
    unsigned oldSz = _funEvaluators.size();
    unsigned newSz = func+1;
    _funEvaluators.expand(newSz);
    for (unsigned i=oldSz; i<newSz; i++) {
	EvalStack::Iterator evit(_evals);
	while (evit.hasNext()) {
	  Evaluator* ev = evit.next();
          // we only set the evaluator if it has not yet been set
	  if (_funEvaluators[i]==0 && ev->canEvaluateFunc(i)) {
	    _funEvaluators[i] = ev;
	  }
	}
    }
  }
  return _funEvaluators[func];
}

/**
 * This searches for an Evaluator for a predicate
 */
InterpretedLiteralEvaluator::Evaluator* InterpretedLiteralEvaluator::getPredEvaluator(unsigned pred)
{
  CALL("InterpretedLiteralEvaluator::getPredEvaluator");

  if (pred>=_predEvaluators.size()) {
    unsigned oldSz = _predEvaluators.size();
    unsigned newSz = pred+1;
    _predEvaluators.expand(newSz);
    for (unsigned i=oldSz; i<newSz; i++) {
      EvalStack::Iterator evit(_evals);
      while (evit.hasNext()) {
	Evaluator* ev = evit.next();
	if (ev->canEvaluatePred(i)) {
	  ASS_EQ(_predEvaluators[i], 0); //we should have only one evaluator for each predicate
	  _predEvaluators[i] = ev;
	}
      }
    }
  }
  return _predEvaluators[pred];
}

}
