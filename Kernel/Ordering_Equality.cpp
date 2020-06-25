
/*
 * File Ordering_Equality.cpp.
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
 * @file Ordering_Equality.cpp
 * Implements class Ordering_Equality.
 */

#include "Term.hpp"

#include "Ordering.hpp"

#include "Lib/Allocator.hpp"

namespace Kernel
{

class Ordering::EqCmp
{
public:
  CLASS_NAME(EqCmp);
  USE_ALLOCATOR(EqCmp);

  EqCmp(Ordering* ordering) : _ordering(ordering)
  {
#if VDEBUG
  inUse=false;
#endif
  }

  Result compareEqualities(Literal* eq1, Literal* eq2) const;

#if VDEBUG
  mutable bool inUse;
#endif

private:

  Result compare(TermList trm1, TermList trm2) const
  {
    return _ordering->compare(trm1, trm2);
  }

  Result compare_s1Gt1(TermList s1,TermList s2,TermList t1,TermList t2) const;
  Result compare_s1GEt1(TermList s1,TermList s2,TermList t1,TermList t2) const;
  Result compare_s1It1(TermList s1,TermList s2,TermList t1,TermList t2) const;
  Result compare_s1It1_s2It2(TermList s1,TermList s2,TermList t1,TermList t2) const;
  Result compare_s1Gt1_s2It2(TermList s1,TermList s2,TermList t1,TermList t2) const;
  Result compare_s1Gt1_s2Lt2(TermList s1,TermList s2,TermList t1,TermList t2) const;
  Result compare_s1Gt1_s2LEt2(TermList s1,TermList s2,TermList t1,TermList t2) const;
  Result compare_s1GEt1_s2It2(TermList s1,TermList s2,TermList t1,TermList t2) const;
  Result compare_s1Gt1_s1It2_s2It1(TermList s1,TermList s2,TermList t1,TermList t2) const;
  Result compare_s1Gt1_s1GEt2_s2It1(TermList s1,TermList s2,TermList t1,TermList t2) const;
  Result compare_s1Gt1_s1GEt2_s2It2(TermList s1,TermList s2,TermList t1,TermList t2) const;
  Result compare_s1GEt1_s1GEt2_s2It1(TermList s1,TermList s2,TermList t1,TermList t2) const;
  Result compare_s1GEt1_s1It2_s2It1(TermList s1,TermList s2,TermList t1,TermList t2) const;
  Result compare_s1GEt1_s2LEt2(TermList s1,TermList s2,TermList t1,TermList t2) const;
  Result compare_s1Gt1_s1GEt2_s2Lt2(TermList s1,TermList s2,TermList t1,TermList t2) const;
  Result compare_s1GEt1_s1GEt2_s2LEt1(TermList s1,TermList s2,TermList t1,TermList t2) const;

  mutable TermList s1,s2,t1,t2;

  Ordering* _ordering;
};

void Ordering::createEqualityComparator()
{
  CALL("Ordering::createEqualityComparator");

  _eqCmp=new EqCmp(this);
}

void Ordering::destroyEqualityComparator()
{
  CALL("Ordering::destroyEqualityComparator");

  delete _eqCmp;
#if VDEBUG
  _eqCmp=0;
#endif
}


Ordering::Result Ordering::compareEqualities(Literal* eq1, Literal* eq2) const
{
  CALL("Ordering::compareEqualities");
  ASS(eq1->isEquality());
  ASS(eq2->isEquality());

#if VDEBUG
  ASS(!_eqCmp->inUse);
  _eqCmp->inUse=true;
#endif

  Result res=_eqCmp->compareEqualities(eq1, eq2);

#if VDEBUG
  ASS(_eqCmp->inUse);
  _eqCmp->inUse=false;
#endif

  return res;
}

Ordering::Result Ordering::EqCmp::compareEqualities(Literal* eq1, Literal* eq2) const
{
  CALL("Ordering::EqCmp::compareEqualities");
  ASS(eq1->isEquality());
  ASS(eq2->isEquality());

  s1=*eq1->nthArgument(0);
  s2=*eq1->nthArgument(1);
  t1=*eq2->nthArgument(0);
  t2=*eq2->nthArgument(1);

  if (s1 == t1) {
    return compare(s2,t2);
  }
  if (s1 == t2) {
    return compare(s2,t1);
  }
  if (s2 == t1) {
    return compare(s1,t2);
  }
  if (s2 == t2) {
    return compare(s1,t1);
  }

  switch(compare(s1,t1)) {
  case Kernel::Ordering::Result::GREATER:
    return compare_s1Gt1(s1,s2,t1,t2);
  case Kernel::Ordering::Result::GREATER_EQ:
    return compare_s1GEt1(s1,s2,t1,t2);
  case Kernel::Ordering::Result::INCOMPARABLE:
    return compare_s1It1(s1,s2,t1,t2);
  case Kernel::Ordering::Result::LESS_EQ:
    return reverse(compare_s1GEt1(t1,t2,s1,s2));
  case Kernel::Ordering::Result::LESS:
    return reverse(compare_s1Gt1(t1,t2,s1,s2));
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Return the result of comparison of literals s1=s2 and t1=t2, assuming s1 > t1
 */
Ordering::Result Ordering::EqCmp::compare_s1Gt1(TermList s1,TermList s2,TermList t1,TermList t2) const
{
  CALL("Ordering::EqCmp::compare_s1Gt1");
  ASS_EQ(compare(s1,t1), Kernel::Ordering::Result::GREATER);

  switch(compare(s2,t2)) {
  case Kernel::Ordering::Result::GREATER:
  case Kernel::Ordering::Result::GREATER_EQ:
    return Kernel::Ordering::Result::GREATER;
  case Kernel::Ordering::Result::INCOMPARABLE:
    return compare_s1Gt1_s2It2(s1,s2,t1,t2);
  case Kernel::Ordering::Result::LESS_EQ:
    return compare_s1Gt1_s2LEt2(s1,s2,t1,t2);
  case Kernel::Ordering::Result::LESS:
    return compare_s1Gt1_s2Lt2(s1,s2,t1,t2);
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Return the result of literal comparison assuming s1 >= t1
 */
Ordering::Result Ordering::EqCmp::compare_s1GEt1(TermList s1,TermList s2,TermList t1,TermList t2) const
{
  CALL("Ordering::EqCmp::compare_s1GEt1");  
  ASS_EQ(compare(s1,t1), Kernel::Ordering::Result::GREATER_EQ);

  switch(compare(s2,t2)) {
  case Kernel::Ordering::Result::GREATER:
    return Kernel::Ordering::Result::GREATER;
  case Kernel::Ordering::Result::GREATER_EQ:
    return Kernel::Ordering::Result::GREATER_EQ;
  case Kernel::Ordering::Result::INCOMPARABLE:
    return compare_s1GEt1_s2It2(s1,s2,t1,t2);
  case Kernel::Ordering::Result::LESS_EQ:
    return compare_s1GEt1_s2LEt2(s1,s2,t1,t2);
  case Kernel::Ordering::Result::LESS:
    return reverse(compare_s1Gt1_s2LEt2(t2,t1,s2,s1));
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Return the result of literal comparison assuming s1 inc t1
 */
Ordering::Result Ordering::EqCmp::compare_s1It1(TermList s1,TermList s2,TermList t1,TermList t2) const
{
  CALL("Ordering::EqCmp::compare_s1It1");
  ASS_EQ(compare(s1,t1), Kernel::Ordering::Result::INCOMPARABLE);

  switch(compare(s2,t2)) {
  case Kernel::Ordering::Result::GREATER:
    return compare_s1Gt1_s2It2(s2,s1,t2,t1);
  case Kernel::Ordering::Result::GREATER_EQ:
    return compare_s1GEt1_s2It2(s2,s1,t2,t1);
  case Kernel::Ordering::Result::INCOMPARABLE:
    return compare_s1It1_s2It2(s1,s2,t1,t2);
  case Kernel::Ordering::Result::LESS_EQ:
    return reverse(compare_s1GEt1_s2It2(t2,t1,s2,s1));
  case Kernel::Ordering::Result::LESS:
    return reverse(compare_s1Gt1_s2It2(t2,t1,s2,s1));
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Return the result of literal comparison assuming s1 inc t1 and s2 inc t2
 */
Ordering::Result Ordering::EqCmp::compare_s1It1_s2It2(TermList s1,TermList s2,TermList t1,TermList t2) const
{
  CALL("Ordering::EqCmp::compare_s1It1_s2It2");
  ASS_EQ(compare(s1,t1), Kernel::Ordering::Result::INCOMPARABLE);
  ASS_EQ(compare(s2,t2), Kernel::Ordering::Result::INCOMPARABLE);

  switch(compare(s1,t2)) {
  case Kernel::Ordering::Result::GREATER:
    return compare_s1Gt1_s1It2_s2It1(s1,s2,t2,t1);
  case Kernel::Ordering::Result::GREATER_EQ:
    return compare_s1GEt1_s1It2_s2It1(s1,s2,t2,t1);
  case Kernel::Ordering::Result::INCOMPARABLE:
    return Kernel::Ordering::Result::INCOMPARABLE;
  case Kernel::Ordering::Result::LESS_EQ:
    return reverse(compare_s1GEt1_s1It2_s2It1(t2,t1,s1,s2));
  case Kernel::Ordering::Result::LESS:
    return reverse(compare_s1Gt1_s1It2_s2It1(t2,t1,s1,s2));
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Return the result of literal comparison assuming s1 > t1 and s2 inc t2
 */
Ordering::Result Ordering::EqCmp::compare_s1Gt1_s2It2(TermList s1,TermList s2,TermList t1,TermList t2) const
{
  CALL("Ordering::EqCmp::compare_s1Gt1_s2It2");
  ASS_EQ(compare(s1,t1), Kernel::Ordering::Result::GREATER);
  ASS_EQ(compare(s2,t2), Kernel::Ordering::Result::INCOMPARABLE);

  switch(compare(s1,t2)) {
  case Kernel::Ordering::Result::GREATER:
    return Kernel::Ordering::Result::GREATER;
  case Kernel::Ordering::Result::GREATER_EQ:
    return compare_s1Gt1_s1GEt2_s2It2(s1,s2,t1,t2);
  case Kernel::Ordering::Result::INCOMPARABLE:
    return Kernel::Ordering::Result::INCOMPARABLE;
  case Kernel::Ordering::Result::LESS_EQ:
  case Kernel::Ordering::Result::LESS:
    ASS_NEQ(compare(s2,t1), Kernel::Ordering::Result::LESS); //would cause s2<t2 by transitivity t2>s1>t1>s2 or t2>=s1>t1>s2
    ASS_NEQ(compare(s2,t1), Kernel::Ordering::Result::LESS_EQ); //would cause s2<t2 by transitivity t2>s1>t1>=s2 or t2>=s1>t1>=s2
    ASS_EQ(compare(t1,t2), Kernel::Ordering::Result::LESS); //transitivity through s1
    return Kernel::Ordering::Result::INCOMPARABLE;
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Return the result of literal comparison assuming s1 > t1 and s2 < t2
 */
Ordering::Result Ordering::EqCmp::compare_s1Gt1_s2Lt2(TermList s1,TermList s2,TermList t1,TermList t2) const
{
  CALL("Ordering::EqCmp::compare_s1Gt1_s2Lt2");
  ASS_EQ(compare(s1,t1), Kernel::Ordering::Result::GREATER);
  ASS_EQ(compare(s2,t2), Kernel::Ordering::Result::LESS);

  switch(compare(s1,t2)) {
  case Kernel::Ordering::Result::GREATER:
    ASS_EQ(compare(s1,s2), Kernel::Ordering::Result::GREATER); //transitivity through t2
    return Kernel::Ordering::Result::GREATER;
  case Kernel::Ordering::Result::GREATER_EQ:
    ASS_NEQ(compare(t1,t2), Kernel::Ordering::Result::GREATER); //transitivity would make s1>t2 and not just s1>=t2
    ASS_EQ(compare(s1,s2), Kernel::Ordering::Result::GREATER); //transitivity through t2
    return compare_s1Gt1_s1GEt2_s2Lt2(s1,s2,t1,t2);

  case Kernel::Ordering::Result::INCOMPARABLE:
    return Kernel::Ordering::Result::INCOMPARABLE;
  case Kernel::Ordering::Result::LESS_EQ:
    ASS_NEQ(compare(s1,s2), Kernel::Ordering::Result::LESS); //transitivity would make s1<t2 and not just s1<=t2
    ASS_EQ(compare(t1,t2), Kernel::Ordering::Result::LESS); //transitivity through t2
    return reverse(compare_s1Gt1_s1GEt2_s2Lt2(t2,t1,s2,s1));

  case Kernel::Ordering::Result::LESS:
    ASS_EQ(compare(t1,t2), Kernel::Ordering::Result::LESS); //transitivity through t2
    return Kernel::Ordering::Result::LESS;
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Return the result of literal comparison assuming s1 > t1 and s2 <= t2
 */
Ordering::Result Ordering::EqCmp::compare_s1Gt1_s2LEt2(TermList s1,TermList s2,TermList t1,TermList t2) const
{
  CALL("Ordering::EqCmp::compare_s1Gt1_s2LEt2");
  ASS_EQ(compare(s1,t1), Kernel::Ordering::Result::GREATER);
  ASS_EQ(compare(s2,t2), Kernel::Ordering::Result::LESS_EQ);

  switch(compare(s1,t2)) {
  case Kernel::Ordering::Result::GREATER:
    ASS_EQ(compare(s1,s2), Kernel::Ordering::Result::GREATER); //transitivity through t2
    return Kernel::Ordering::Result::GREATER;
  case Kernel::Ordering::Result::GREATER_EQ:
    ASS_NEQ(compare(t1,t2), Kernel::Ordering::Result::GREATER); //transitivity would make s1>t2 and not just s1>=t2
    ASS(compare(s1,s2)== Kernel::Ordering::Result::LESS || compare(s1,s2)== Kernel::Ordering::Result::LESS_EQ); //transitivity through t2
    return Kernel::Ordering::Result::INCOMPARABLE;
  case Kernel::Ordering::Result::INCOMPARABLE:
    return Kernel::Ordering::Result::INCOMPARABLE;
  case Kernel::Ordering::Result::LESS_EQ:
  case Kernel::Ordering::Result::LESS:
    ASS_EQ(compare(t1,t2), Kernel::Ordering::Result::LESS); //transitivity through s1
    return Kernel::Ordering::Result::INCOMPARABLE;
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Return the result of literal comparison assuming s1 >= t1 and s2 inc t2
 */
Ordering::Result Ordering::EqCmp::compare_s1GEt1_s2It2(TermList s1,TermList s2,TermList t1,TermList t2) const
{
  CALL("Ordering::EqCmp::compare_s1GEt1_s2It2");
  ASS_EQ(compare(s1,t1), Kernel::Ordering::Result::GREATER_EQ);
  ASS_EQ(compare(s2,t2), Kernel::Ordering::Result::INCOMPARABLE);

  switch(compare(s1,t2)) {
  case Kernel::Ordering::Result::GREATER:
    return compare_s1Gt1_s1GEt2_s2It1(s1,s2,t2,t1);
  case Kernel::Ordering::Result::GREATER_EQ:
    return compare_s1GEt1_s1GEt2_s2It1(s1,s2,t2,t1);
  case Kernel::Ordering::Result::INCOMPARABLE:
    return Kernel::Ordering::Result::INCOMPARABLE;
  case Kernel::Ordering::Result::LESS_EQ:
    ASS(compare(t1,t2)== Kernel::Ordering::Result::LESS || compare(t1,t2)== Kernel::Ordering::Result::LESS_EQ); //transitivity through s1
    ASS(compare(s2,t1) != Kernel::Ordering::Result::LESS && compare(s2,t1) != Kernel::Ordering::Result::LESS_EQ);
    return Kernel::Ordering::Result::INCOMPARABLE;
  case Kernel::Ordering::Result::LESS:
    ASS_EQ(compare(t1,t2), Kernel::Ordering::Result::LESS); //transitivity through s1
    return Kernel::Ordering::Result::INCOMPARABLE;
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Return the result of literal comparison assuming s1 > t1, s1 inc t2, s2 inc t1
 */
Ordering::Result Ordering::EqCmp::compare_s1Gt1_s1It2_s2It1(TermList s1,TermList s2,TermList t1,TermList t2) const
{
  CALL("Ordering::EqCmp::compare_s1Gt1_s1It2_s2It1");
  ASS_EQ(compare(s1,t1), Kernel::Ordering::Result::GREATER);
  ASS_EQ(compare(s1,t2), Kernel::Ordering::Result::INCOMPARABLE);
  ASS_EQ(compare(s2,t1), Kernel::Ordering::Result::INCOMPARABLE);

  switch(compare(s2,t2)) {
  case Kernel::Ordering::Result::GREATER:
  case Kernel::Ordering::Result::GREATER_EQ:
    return Kernel::Ordering::Result::GREATER;
  case Kernel::Ordering::Result::INCOMPARABLE:
  case Kernel::Ordering::Result::LESS_EQ:
  case Kernel::Ordering::Result::LESS:
    return Kernel::Ordering::Result::INCOMPARABLE;
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Return the result of literal comparison assuming s1 > t1, s1 >= t2, s2 inc t1
 */
Ordering::Result Ordering::EqCmp::compare_s1Gt1_s1GEt2_s2It1(TermList s1,TermList s2,TermList t1,TermList t2) const
{
  CALL("Ordering::EqCmp::compare_s1Gt1_s1GEt2_s2It1");
  ASS_EQ(compare(s1,t1), Kernel::Ordering::Result::GREATER);
  ASS_EQ(compare(s1,t2), Kernel::Ordering::Result::GREATER_EQ);
  ASS_EQ(compare(s2,t1), Kernel::Ordering::Result::INCOMPARABLE);

  switch(compare(s2,t2)) {
  case Kernel::Ordering::Result::GREATER:
  case Kernel::Ordering::Result::GREATER_EQ:
    return Kernel::Ordering::Result::GREATER;
  case Kernel::Ordering::Result::INCOMPARABLE:
    return Kernel::Ordering::Result::INCOMPARABLE;
  case Kernel::Ordering::Result::LESS_EQ:
    ASS(compare(s1,s2)== Kernel::Ordering::Result::GREATER || compare(s1,s2)== Kernel::Ordering::Result::GREATER_EQ); //transitivity through t2
    return Kernel::Ordering::Result::INCOMPARABLE;
  case Kernel::Ordering::Result::LESS:
    ASS_EQ(compare(s1,s2), Kernel::Ordering::Result::GREATER); //transitivity through t2
    return Kernel::Ordering::Result::INCOMPARABLE;
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Return the result of literal comparison assuming s1 > t1, s1 >= t2, s2 inc t2
 */
Ordering::Result Ordering::EqCmp::compare_s1Gt1_s1GEt2_s2It2(TermList s1,TermList s2,TermList t1,TermList t2) const
{
  CALL("Ordering::EqCmp::compare_s1Gt1_s1GEt2_s2It2");
  ASS_EQ(compare(s1,t1), Kernel::Ordering::Result::GREATER);
  ASS_EQ(compare(s1,t2), Kernel::Ordering::Result::GREATER_EQ);
  ASS_EQ(compare(s2,t2), Kernel::Ordering::Result::INCOMPARABLE);

  switch(compare(s2,t1)) {
  case Kernel::Ordering::Result::GREATER:
    return Kernel::Ordering::Result::GREATER;
  case Kernel::Ordering::Result::GREATER_EQ:
    return Kernel::Ordering::Result::GREATER_EQ;
  case Kernel::Ordering::Result::INCOMPARABLE:
    return Kernel::Ordering::Result::INCOMPARABLE;
  case Kernel::Ordering::Result::LESS_EQ:
  case Kernel::Ordering::Result::LESS:
    ASS_EQ(compare(s1,s2), Kernel::Ordering::Result::GREATER); //transitivity through t1
    ASS_NEQ(compare(t1,t2), Kernel::Ordering::Result::LESS); //otherwise it would hold s1<t2 by transitivity
    ASS_NEQ(compare(t1,t2), Kernel::Ordering::Result::LESS_EQ); //otherwise it would hold s1<t2 or s1<=t2 by transitivity
    return Kernel::Ordering::Result::INCOMPARABLE;
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Return the result of literal comparison assuming s1 >= t1, s1 >= t2, s2 inc t1
 */
Ordering::Result Ordering::EqCmp::compare_s1GEt1_s1GEt2_s2It1(TermList s1,TermList s2,TermList t1,TermList t2) const
{
  CALL("Ordering::EqCmp::compare_s1GEt1_s1GEt2_s2It1");
  ASS_EQ(compare(s1,t1), Kernel::Ordering::Result::GREATER_EQ);
  ASS_EQ(compare(s1,t2), Kernel::Ordering::Result::GREATER_EQ);
  ASS_EQ(compare(s2,t1), Kernel::Ordering::Result::INCOMPARABLE);

  switch(compare(s2,t2)) {
  case Kernel::Ordering::Result::GREATER:
    return Kernel::Ordering::Result::GREATER;
  case Kernel::Ordering::Result::GREATER_EQ:
    return Kernel::Ordering::Result::GREATER_EQ;
  case Kernel::Ordering::Result::INCOMPARABLE:
    return Kernel::Ordering::Result::INCOMPARABLE;
  case Kernel::Ordering::Result::LESS_EQ:
    ASS(compare(s1,s2)== Kernel::Ordering::Result::GREATER || compare(s1,s2)== Kernel::Ordering::Result::GREATER_EQ); //transitivity through t2
    return Kernel::Ordering::Result::INCOMPARABLE;
  case Kernel::Ordering::Result::LESS:
    ASS_EQ(compare(s1,s2), Kernel::Ordering::Result::GREATER); //transitivity through t2
    return Kernel::Ordering::Result::INCOMPARABLE;
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Return the result of literal comparison assuming s1 >= t1, s1 inc t2, s2 inc t1
 */
Ordering::Result Ordering::EqCmp::compare_s1GEt1_s1It2_s2It1(TermList s1,TermList s2,TermList t1,TermList t2) const
{
  CALL("Ordering::EqCmp::compare_s1GEt1_s1It2_s2It1");
  ASS_EQ(compare(s1,t1), Kernel::Ordering::Result::GREATER_EQ);
  ASS_EQ(compare(s1,t2), Kernel::Ordering::Result::INCOMPARABLE);
  ASS_EQ(compare(s2,t1), Kernel::Ordering::Result::INCOMPARABLE);

  ASS_NEQ(compare(t1,t2), Kernel::Ordering::Result::GREATER); //otherwise it would hold s1>t2 by transitivity
  ASS_NEQ(compare(t1,t2), Kernel::Ordering::Result::GREATER_EQ); //otherwise it would hold s1>=t2 by transitivity
  ASS_NEQ(compare(s1,s2), Kernel::Ordering::Result::LESS); //otherwise it would hold s2>t1 by transitivity
  ASS_NEQ(compare(s1,s2), Kernel::Ordering::Result::LESS_EQ); //otherwise it would hold s2>=t1 by transitivity

  switch(compare(s2,t2)) {
  case Kernel::Ordering::Result::GREATER:
    ASS_NEQ(compare(s1,s2), Kernel::Ordering::Result::GREATER); //otherwise it would hold s1>t2 by transitivity
    ASS_NEQ(compare(s1,s2), Kernel::Ordering::Result::GREATER_EQ); //otherwise it would hold s1>t2 by transitivity
    ASS_NEQ(compare(t1,t2), Kernel::Ordering::Result::LESS); //otherwise it would hold s2>t1 by transitivity
    ASS_NEQ(compare(t1,t2), Kernel::Ordering::Result::LESS_EQ); //otherwise it would hold s2>t1 by transitivity
    return Kernel::Ordering::Result::GREATER;
  case Kernel::Ordering::Result::GREATER_EQ:
    ASS_NEQ(compare(s1,s2), Kernel::Ordering::Result::GREATER); //otherwise it would hold s1>=t2 by transitivity
    ASS_NEQ(compare(s1,s2), Kernel::Ordering::Result::GREATER_EQ); //otherwise it would hold s1>=t2 by transitivity
    ASS_NEQ(compare(t1,t2), Kernel::Ordering::Result::LESS); //otherwise it would hold s2>=t1 by transitivity
    ASS_NEQ(compare(t1,t2), Kernel::Ordering::Result::LESS_EQ); //otherwise it would hold s2>=t1 by transitivity
    return Kernel::Ordering::Result::GREATER_EQ;
  case Kernel::Ordering::Result::INCOMPARABLE:
  case Kernel::Ordering::Result::LESS_EQ:
  case Kernel::Ordering::Result::LESS:
    return Kernel::Ordering::Result::INCOMPARABLE;
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Return the result of literal comparison assuming s1 >= t1, s2 <= t2
 */
Ordering::Result Ordering::EqCmp::compare_s1GEt1_s2LEt2(TermList s1,TermList s2,TermList t1,TermList t2) const
{
  CALL("Ordering::EqCmp::compare_s1GEt1_s2LEt2");
  ASS_EQ(compare(s1,t1), Kernel::Ordering::Result::GREATER_EQ);
  ASS_EQ(compare(s2,t2), Kernel::Ordering::Result::LESS_EQ);

  switch(compare(s1,t2)) {
  case Kernel::Ordering::Result::GREATER:
    ASS_EQ(compare(s1,s2), Kernel::Ordering::Result::GREATER); //transitivity through t2
    ASS_NEQ(compare(t2,t1), Kernel::Ordering::Result::GREATER);
    ASS_NEQ(compare(t2,t1), Kernel::Ordering::Result::GREATER_EQ);
    ASS_NEQ(compare(s2,t1), Kernel::Ordering::Result::GREATER_EQ);
    ASS_NEQ(compare(s2,t1), Kernel::Ordering::Result::GREATER);
    return Kernel::Ordering::Result::INCOMPARABLE;

  case Kernel::Ordering::Result::GREATER_EQ:
    ASS(compare(s1,s2)== Kernel::Ordering::Result::GREATER || compare(s1,s2)== Kernel::Ordering::Result::GREATER_EQ); //transitivity through t2
    return compare_s1GEt1_s1GEt2_s2LEt1(s1,s2,t2,t1);

  case Kernel::Ordering::Result::INCOMPARABLE:
    return Kernel::Ordering::Result::INCOMPARABLE;
  case Kernel::Ordering::Result::LESS_EQ:
    ASS(compare(t2,t1)== Kernel::Ordering::Result::GREATER || compare(t2,t1)== Kernel::Ordering::Result::GREATER_EQ); //transitivity through s1
    return reverse(compare_s1GEt1_s1GEt2_s2LEt1(t2,t1,s1,s2));

  case Kernel::Ordering::Result::LESS:
    ASS_EQ(compare(t2,t1), Kernel::Ordering::Result::GREATER); //transitivity through s1
    ASS_NEQ(compare(s2,s1), Kernel::Ordering::Result::GREATER);
    ASS_NEQ(compare(s2,s1), Kernel::Ordering::Result::GREATER_EQ);
    ASS_NEQ(compare(t2,s1), Kernel::Ordering::Result::GREATER_EQ);
    ASS_NEQ(compare(t2,s1), Kernel::Ordering::Result::GREATER);
    return Kernel::Ordering::Result::INCOMPARABLE;

  default:
    ASSERTION_VIOLATION;
  }
}


/**
 * Return the result of literal comparison assuming s1 > t1, s1 >= t2, s2 < t2
 */
Ordering::Result Ordering::EqCmp::compare_s1Gt1_s1GEt2_s2Lt2(TermList s1,TermList s2,TermList t1,TermList t2) const
{
  CALL("Ordering::EqCmp::compare_s1Gt1_s1GEt2_s2Lt2");
  ASS_EQ(compare(s1,t1), Kernel::Ordering::Result::GREATER);
  ASS_EQ(compare(s1,t2), Kernel::Ordering::Result::GREATER_EQ);
  ASS_EQ(compare(s2,t2), Kernel::Ordering::Result::LESS);

  ASS_EQ(compare(s1,s2), Kernel::Ordering::Result::GREATER); //transitivity through t2
  ASS_NEQ(compare(t1,t2), Kernel::Ordering::Result::GREATER);
  ASS_NEQ(compare(t1,t2), Kernel::Ordering::Result::GREATER_EQ);

  switch(compare(s2,t1)) {
  case Kernel::Ordering::Result::GREATER:
    ASS_EQ(compare(t2,t1), Kernel::Ordering::Result::GREATER); //transitivity through s2
    return Kernel::Ordering::Result::GREATER;
  case Kernel::Ordering::Result::GREATER_EQ:
    ASS_EQ(compare(t2,t1), Kernel::Ordering::Result::GREATER); //transitivity through s2
    return Kernel::Ordering::Result::GREATER_EQ;
  case Kernel::Ordering::Result::INCOMPARABLE:
  case Kernel::Ordering::Result::LESS_EQ:
  case Kernel::Ordering::Result::LESS:
    return Kernel::Ordering::Result::INCOMPARABLE;
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Return the result of literal comparison assuming s1 >= t1, s1 >= t2, s2 <= t1
 */
Ordering::Result Ordering::EqCmp::compare_s1GEt1_s1GEt2_s2LEt1(TermList s1,TermList s2,TermList t1,TermList t2) const
{
  CALL("Ordering::EqCmp::compare_s1GEt1_s1GEt2_s2LEt1");
  ASS_EQ(compare(s1,t1), Kernel::Ordering::Result::GREATER_EQ);
  ASS_EQ(compare(s1,t2), Kernel::Ordering::Result::GREATER_EQ);
  ASS_EQ(compare(s2,t1), Kernel::Ordering::Result::LESS_EQ);

  switch(compare(s2,t2)) {
  case Kernel::Ordering::Result::GREATER:
    ASSERTION_VIOLATION;
  case Kernel::Ordering::Result::GREATER_EQ:
    ASS(compare(t1,t2)== Kernel::Ordering::Result::GREATER || compare(t1,t2)== Kernel::Ordering::Result::GREATER_EQ); //transitivity through s2
    return Kernel::Ordering::Result::GREATER_EQ;
  case Kernel::Ordering::Result::INCOMPARABLE:
    return Kernel::Ordering::Result::INCOMPARABLE;
  case Kernel::Ordering::Result::LESS_EQ:
    ASS(compare(s1,s2)== Kernel::Ordering::Result::GREATER || compare(s1,s2)== Kernel::Ordering::Result::GREATER_EQ); //transitivity through s2
    return Kernel::Ordering::Result::INCOMPARABLE;
  case Kernel::Ordering::Result::LESS:
    ASS_EQ(compare(s1,s2), Kernel::Ordering::Result::GREATER); //transitivity through t2
    return Kernel::Ordering::Result::INCOMPARABLE;
  default:
    ASSERTION_VIOLATION;
  }
}


}
