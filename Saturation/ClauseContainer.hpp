
/*
 * File ClauseContainer.hpp.
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
 * @file ClauseContainer.hpp
 * Defines class ClauseContainer
 *
 */

#ifndef __ClauseContainer__
#define __ClauseContainer__

#include "Forwards.hpp"

#include "Lib/Event.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Lib/Deque.hpp"
#include "Lib/Stack.hpp"

#include "Lib/Allocator.hpp"

#define OUTPUT_LRS_DETAILS 0

namespace Saturation
{

using namespace Lib;
using namespace Kernel;
using namespace Shell;

class ClauseContainer
{
public:
  CLASS_NAME(ClauseContainer);
  USE_ALLOCATOR(ClauseContainer);

  virtual ~ClauseContainer() {}
  ClauseEvent addedEvent;
  /**
   * This event fires when a clause is removed from the
   * container because it is no longer needed, e.g. it was
   * backward-simplified, or the container is destroyed.
   * It does not fire for clauses that are removed from the
   * container because they are selected to be further
   * processed by the saturation algorithm (e.g. activated).
   */
  ClauseEvent removedEvent;
  /**
   * This event fires when a clause is removed from the
   * container to be further processed by the saturation
   * algorithm (e.g. activated).
   */
  ClauseEvent selectedEvent;
  virtual void add(Clause* c) = 0;
  void addClauses(ClauseIterator cit);
};

class RandomAccessClauseContainer
: public ClauseContainer
{
public:
  CLASS_NAME(RandomAccessClauseContainer);
  USE_ALLOCATOR(RandomAccessClauseContainer);

  virtual void attach(SaturationAlgorithm* salg);
  virtual void detach();

  virtual unsigned sizeEstimate() const = 0;
  virtual void remove(Clause* c) = 0;
  void removeClauses(ClauseIterator cit);

protected:
  RandomAccessClauseContainer() :_salg(0) {}
  SaturationAlgorithm* getSaturationAlgorithm() { return _salg; }

  virtual void onLimitsUpdated() {}
private:
  SaturationAlgorithm* _salg;
  SubscriptionData _limitChangeSData;
};

class PlainClauseContainer : public ClauseContainer {
public:
  CLASS_NAME(PlainClauseContainer);
  USE_ALLOCATOR(PlainClauseContainer);

  void add(Clause* c) override
  {
    addedEvent.fire(c);
  }
};


class UnprocessedClauseContainer
: public ClauseContainer
{
public:
  CLASS_NAME(UnprocessedClauseContainer);
  USE_ALLOCATOR(UnprocessedClauseContainer);

  virtual ~UnprocessedClauseContainer();
  UnprocessedClauseContainer() : _data(64) {}
  void add(Clause* c) override;
  Clause* pop();
  bool isEmpty() const
  { return _data.isEmpty(); }
private:
  Deque<Clause*> _data;
};

typedef PlainEvent LimitsChangeEvent;

class PassiveClauseContainer
: public RandomAccessClauseContainer
{
public:
  CLASS_NAME(PassiveClauseContainer);
  USE_ALLOCATOR(PassiveClauseContainer);

  PassiveClauseContainer(bool isOutermost, const Shell::Options& opt, vstring name = "") : _isOutermost(isOutermost), _opt(opt), _name(name) {}
  virtual ~PassiveClauseContainer(){};

  LimitsChangeEvent changedEvent;

  virtual bool isEmpty() const = 0;
  virtual Clause* popSelected() = 0;

  virtual unsigned sizeEstimate() const = 0;

  /*
   * LRS specific methods for computation of Limits
   */
  void updateLimits(long long estReachableCnt);

  virtual void simulationInit() = 0;
  virtual bool simulationHasNext() = 0;
  virtual void simulationPopSelected() = 0;

  // returns whether at least one of the limits was tightened
  virtual bool setLimitsToMax() = 0;
  // returns whether at least one of the limits was tightened
  virtual bool setLimitsFromSimulation() = 0;

  virtual void onLimitsUpdated() = 0;

  /*
   * LRS specific methods and fields for usage of limits
   */
  virtual bool ageLimited() const = 0;
  virtual bool weightLimited() const = 0;

  virtual bool fulfilsAgeLimit(Clause* c) const = 0;
  // note: w here denotes the weight as returned by weight().
  // age is to be recovered from inference
  // this method internally takes care of computing the corresponding weightForClauseSelection.
  virtual bool fulfilsAgeLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const = 0;

  virtual bool fulfilsWeightLimit(Clause* cl) const = 0;
  // note: w here denotes the weight as returned by weight().
  // age is to be recovered from inference
  // this method internally takes care of computing the corresponding weightForClauseSelection.
  virtual bool fulfilsWeightLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const = 0;
  
  virtual bool childrenPotentiallyFulfilLimits(Clause* cl, unsigned upperBoundNumSelLits) const = 0;

protected:
  bool _isOutermost;
  const Shell::Options& _opt;

public:
  vstring _name;
};

class ActiveClauseContainer
: public RandomAccessClauseContainer
{
public:
  CLASS_NAME(ActiveClauseContainer);
  USE_ALLOCATOR(ActiveClauseContainer);

  ActiveClauseContainer(const Shell::Options& opt) : _size(0), _opt(opt) {}

  void add(Clause* c) override;
  void remove(Clause* c) override;

  unsigned sizeEstimate() const override { return _size; }

protected:
  void onLimitsUpdated() override;
private:
  unsigned _size;
  const Shell::Options& _opt;
};


};

#endif /*__ClauseContainer__*/
