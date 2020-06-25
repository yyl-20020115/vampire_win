
/*
 * File DecisionProcedure.hpp.
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
 * @file DecisionProcedure.hpp
 * Defines class DecisionProcedure.
 */
#ifndef __DecisionProcedure__
#define __DecisionProcedure__

#include "Forwards.hpp"
#include "Kernel/Term.hpp"

namespace DP {

using namespace Lib;
using namespace Kernel;

/**
 * A pure virtual class implementing decision procedures.
 */
class DecisionProcedure {
public:
  enum class Status {
    /** satisfiable */
    SATISFIABLE,
    /** unsatisfiable */
    UNSATISFIABLE,
    /** 
     * When the decision procedure cannot determine
     * the satisfiability status of the literal set
     */
    UNKNOWN,
  };

  virtual ~DecisionProcedure() {}
  /** add literals */
  virtual void addLiterals(LiteralIterator lits, bool onlyEqualites = false) = 0;
  /** return the result */
  virtual Status getStatus(bool getMultipleCores=false) = 0;

  // TODO: this is needed for the model experiment with the SimpleCongruenceClosure class
  // but does it make sense for a general dp?
  virtual void getModel(LiteralStack& model) = 0;

  /**
   * Return number of unsatisfiable cores that can be retrieved.
   * 0 is returned if the status is SATISFIABLE or UNKNOWN. If UNSATISFIABLE,
   * number greater than zero is returned.
   *
   * Can be called only after getStatus before any next call to addLiterals.
   */
  virtual unsigned getUnsatCoreCount() = 0;
  virtual void getUnsatCore(LiteralStack& res, unsigned coreIndex=0) = 0;
  /** reset decision procedure object into state equivalent to its initial state */
  virtual void reset() = 0;
};

}

#endif // __DecisionProcedure__
