
/*
 * File TimeCounter.cpp.
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
 * @file TimeCounter.cpp
 * Implements class TimeCounter.
 */

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Timer.hpp"

#include "Shell/Options.hpp"
#include "Shell/UIHelper.hpp"

#include "TimeCounter.hpp"

using namespace std;
using namespace Shell;
using namespace Lib;

bool TimeCounter::s_measuring = true;
bool TimeCounter::s_initialized = false;
int TimeCounter::s_measuredTimes[(unsigned)Lib::TimeCounterUnit::__TC_ELEMENT_COUNT];
int TimeCounter::s_measuredTimesChildren[(unsigned)Lib::TimeCounterUnit::__TC_ELEMENT_COUNT];
int TimeCounter::s_measureInitTimes[(unsigned)Lib::TimeCounterUnit::__TC_ELEMENT_COUNT];
TimeCounter* TimeCounter::s_currTop = 0;

/**
 * Reinitializes the time counting
 *
 * This is useful when we fork a new the process and want
 * to start counting from the beginning.
 */
void TimeCounter::reinitialize()
{
  CALL("TimeCounter::reinitialize");

  s_initialized=0;

  initialize();

  int currTime=env.timer->elapsedMilliseconds();

  TimeCounter* counter = s_currTop;
  while(counter) {
    s_measureInitTimes[(unsigned)counter->_tcu]=currTime;
    counter = counter->previousTop;
  }
  // at least OTHER is running, started now
  s_measureInitTimes[(unsigned)Lib::TimeCounterUnit::TC_OTHER] = currTime;
}

void TimeCounter::initialize()
{
  CALL("TimeCounter::initialize");
  ASS(!s_initialized);

  s_initialized=true;

  if(!env.options->timeStatistics()) {
    s_measuring=false;
    return;
  }

  for(int i=0; i<(int)Lib::TimeCounterUnit::__TC_ELEMENT_COUNT; i++) {
    s_measuredTimes[i]=0;
    s_measuredTimesChildren[i]=0;
    s_measureInitTimes[i]=-1;
  }

  // OTHER is running, from time 0
  s_measureInitTimes[(unsigned)Lib::TimeCounterUnit::TC_OTHER]=0;
}

void TimeCounter::startMeasuring(TimeCounterUnit tcu)
{
  CALL("TimeCounter::startMeasuring");
  ASS_NEQ(tcu, TimeCounterUnit::TC_OTHER);

  if(!s_initialized) {
    initialize();
    if(!s_measuring) {
      return;
    }
  }

  // don't run a timer inside itself
  ASS_REP(s_measureInitTimes[(unsigned)tcu] == -1,tcu);

  previousTop = s_currTop;
  s_currTop = this;

  int currTime=env.timer->elapsedMilliseconds();

  _tcu=tcu;
  s_measureInitTimes[(unsigned)_tcu]=currTime;
}

void TimeCounter::stopMeasuring()
{
  CALL("TimeCounter::stopMeasuring");

  if(_tcu==Lib::TimeCounterUnit::__TC_NONE) {
    //we did not start measuring
    return;
  }
  ASS_GE(s_measureInitTimes[(unsigned)_tcu], 0);

  int currTime=env.timer->elapsedMilliseconds();
  int measuredTime = currTime-s_measureInitTimes[(unsigned)_tcu];
  s_measuredTimes[(unsigned)_tcu] += measuredTime;
  s_measureInitTimes[(unsigned)_tcu]=-1;

  if (previousTop) {
    s_measuredTimesChildren[(unsigned)previousTop->_tcu] += measuredTime;
  } else {
    s_measuredTimesChildren[(unsigned)Lib::TimeCounterUnit::TC_OTHER] += measuredTime;
  }

  ASS_EQ(s_currTop,this);
  s_currTop = previousTop;
}

void TimeCounter::snapShot()
{
  CALL("TimeCounter::snapShot");

  int currTime=env.timer->elapsedMilliseconds();

  TimeCounter* counter = s_currTop;
  while(counter) {
    ASS_GE(s_measureInitTimes[(unsigned)counter->_tcu], 0);
    int measuredTime = currTime-s_measureInitTimes[(unsigned)counter->_tcu];
    s_measuredTimes[(unsigned)counter->_tcu] += measuredTime;
    s_measureInitTimes[(unsigned)counter->_tcu]=currTime;

    if (counter->previousTop) {
      s_measuredTimesChildren[(unsigned)counter->previousTop->_tcu] += measuredTime;
    } else {
      s_measuredTimesChildren[(unsigned)Lib::TimeCounterUnit::TC_OTHER] += measuredTime;
    }

    counter = counter->previousTop;
  }

  int measuredTime = currTime-s_measureInitTimes[(unsigned)Lib::TimeCounterUnit::TC_OTHER];
  s_measuredTimes[(unsigned)Lib::TimeCounterUnit::TC_OTHER] += measuredTime;
  s_measureInitTimes[(unsigned)Lib::TimeCounterUnit::TC_OTHER]=currTime;
}

void TimeCounter::printReport(ostream& out)
{
  CALL("TimeCounter::printReport");

  snapShot();

  addCommentSignForSZS(out);
  out << "Time measurement results:" << endl;
  for (int i=0; i< (unsigned)Lib::TimeCounterUnit::__TC_ELEMENT_COUNT; i++) {
    outputSingleStat(static_cast<TimeCounterUnit>(i), out);
  }
  out<<endl;
}

void TimeCounter::outputSingleStat(TimeCounterUnit tcu, ostream& out)
{
  if (s_measureInitTimes[(unsigned)tcu]==-1 && !s_measuredTimes[(unsigned)tcu]) {
    return;
  }

  addCommentSignForSZS(out);
  switch(tcu) {
  case Lib::TimeCounterUnit::TC_RAND_OPT:
    out << "random option generation";
    break;
  case Lib::TimeCounterUnit::TC_BACKWARD_DEMODULATION:
    out<<"backward demodulation";
    break;
  case Lib::TimeCounterUnit::TC_BACKWARD_SUBSUMPTION:
    out<<"backward subsumption";
    break;
  case Lib::TimeCounterUnit::TC_BACKWARD_SUBSUMPTION_RESOLUTION:
    out<<"backward subsumption resolution";
    break;
  case Lib::TimeCounterUnit::TC_BDD:
    out<<"BDD operations";
    break;
  case Lib::TimeCounterUnit::TC_BDD_CLAUSIFICATION:
    out<<"BDD clausification";
    break;
  case Lib::TimeCounterUnit::TC_BDD_MARKING_SUBSUMPTION:
    out<<"BDD marking subsumption";
    break;
  case Lib::TimeCounterUnit::TC_INTERPRETED_EVALUATION:
    out<<"interpreted evaluation";
    break;
  case Lib::TimeCounterUnit::TC_INTERPRETED_SIMPLIFICATION:
    out<<"interpreted simplification";
    break;
  case Lib::TimeCounterUnit::TC_CONDENSATION:
    out<<"condensation";
    break;
  case Lib::TimeCounterUnit::TC_CONSEQUENCE_FINDING:
    out<<"consequence finding";
    break;
  case Lib::TimeCounterUnit::TC_FORWARD_DEMODULATION:
    out<<"forward demodulation";
    break;
  case Lib::TimeCounterUnit::TC_FORWARD_SUBSUMPTION:
    out<<"forward subsumption";
    break;
  case Lib::TimeCounterUnit::TC_FORWARD_SUBSUMPTION_RESOLUTION:
    out<<"forward subsumption resolution";
    break;
  case Lib::TimeCounterUnit::TC_FORWARD_LITERAL_REWRITING:
    out<<"forward literal rewriting";
    break;
  case Lib::TimeCounterUnit::TC_GLOBAL_SUBSUMPTION:
    out<<"global subsumption";
    break;
  case Lib::TimeCounterUnit::TC_SIMPLIFYING_UNIT_LITERAL_INDEX_MAINTENANCE:
    out<<"unit clause index maintenance";
    break;
  case Lib::TimeCounterUnit::TC_NON_UNIT_LITERAL_INDEX_MAINTENANCE:
    out<<"non unit clause index maintenance";
    break;
  case Lib::TimeCounterUnit::TC_FORWARD_SUBSUMPTION_INDEX_MAINTENANCE:
    out<<"forward subsumption index maintenance";
    break;
  case Lib::TimeCounterUnit::TC_BINARY_RESOLUTION_INDEX_MAINTENANCE:
    out<<"binary resolution index maintenance";
    break;
  case Lib::TimeCounterUnit::TC_BACKWARD_SUBSUMPTION_INDEX_MAINTENANCE:
    out<<"backward subsumption index maintenance";
    break;
  case Lib::TimeCounterUnit::TC_BACKWARD_SUPERPOSITION_INDEX_MAINTENANCE:
    out<<"backward superposition index maintenance";
    break;
  case Lib::TimeCounterUnit::TC_FORWARD_SUPERPOSITION_INDEX_MAINTENANCE:
    out<<"forward superposition index maintenance";
    break;
  case Lib::TimeCounterUnit::TC_BACKWARD_DEMODULATION_INDEX_MAINTENANCE:
    out<<"backward demodulation index maintenance";
    break;
  case Lib::TimeCounterUnit::TC_FORWARD_DEMODULATION_INDEX_MAINTENANCE:
    out<<"forward demodulation index maintenance";
    break;
  case Lib::TimeCounterUnit::TC_SPLITTING_COMPONENT_INDEX_MAINTENANCE:
    out<<"splitting component index maintenance";
    break;
  case Lib::TimeCounterUnit::TC_SPLITTING_COMPONENT_INDEX_USAGE:
    out<<"splitting component index usage";
    break;
  case Lib::TimeCounterUnit::TC_SPLITTING_MODEL_UPDATE:
    out<<"splitting model update";
    break;
  case Lib::TimeCounterUnit::TC_CONGRUENCE_CLOSURE:
    out<<"congruence closure";
    break;
  case Lib::TimeCounterUnit::TC_CCMODEL:
    out<<"model from congruence closure";
    break;
  case Lib::TimeCounterUnit::TC_INST_GEN_SAT_SOLVING:
    out<<"inst gen SAT solving";
    break;
  case Lib::TimeCounterUnit::TC_INST_GEN_SIMPLIFICATIONS:
    out<<"inst gen simplifications";
    break;
  case Lib::TimeCounterUnit::TC_INST_GEN_VARIANT_DETECTION:
    out<<"inst gen variant detection";
    break;
  case Lib::TimeCounterUnit::TC_INST_GEN_GEN_INST:
    out<<"inst gen generating instances";
    break;
  case Lib::TimeCounterUnit::TC_LRS_LIMIT_MAINTENANCE:
    out<<"LRS limit maintenance";
    break;
  case Lib::TimeCounterUnit::TC_LITERAL_REWRITE_RULE_INDEX_MAINTENANCE:
    out<<"literal rewrite rule index maintenance";
    break;
  case Lib::TimeCounterUnit::TC_OTHER:
    out<<"other";
    break;
  case Lib::TimeCounterUnit::TC_PARSING:
    out<<"parsing";
    break;
  case Lib::TimeCounterUnit::TC_PREPROCESSING:
    out<<"preprocessing";
    break;
  case Lib::TimeCounterUnit::TC_BCE:
    out<<"blocked clause elimination";
    break;
  case Lib::TimeCounterUnit::TC_PROPERTY_EVALUATION:
    out<<"property evaluation";
    break;
  case Lib::TimeCounterUnit::TC_SINE_SELECTION:
    out<<"sine selection";
    break;
  case Lib::TimeCounterUnit::TC_RESOLUTION:
    out<<"resolution";
    break;
  case Lib::TimeCounterUnit::TC_UR_RESOLUTION:
    out<<"unit resulting resolution";
    break;
  case Lib::TimeCounterUnit::TC_SAT_SOLVER:
    out<<"SAT solver time";
    break;
  case Lib::TimeCounterUnit::TC_TWLSOLVER_ADD:
    out<<"TWLSolver add clauses";
    break;
    break;
  case Lib::TimeCounterUnit::TC_MINIMIZING_SOLVER:
    out << "minimizing solver time";
    break;
  case Lib::TimeCounterUnit::TC_SAT_PROOF_MINIMIZATION:
    out << "sat proof minimization";
    break;
  case Lib::TimeCounterUnit::TC_SUPERPOSITION:
    out<<"superposition";
    break;
  case Lib::TimeCounterUnit::TC_LITERAL_ORDER_AFTERCHECK:
    out<<"literal order aftercheck";
    break;
  case Lib::TimeCounterUnit::TC_HYPER_SUPERPOSITION:
    out<<"hyper superposition";
    break;
  case Lib::TimeCounterUnit::TC_TERM_SHARING:
    out<<"term sharing";
    break;
  case Lib::TimeCounterUnit::TC_TRIVIAL_PREDICATE_REMOVAL:
    out<<"trivial predicate removal";
    break;
  case Lib::TimeCounterUnit::TC_SOLVING:
    out << "Bound propagation solving";
    break;
  case Lib::TimeCounterUnit::TC_BOUND_PROPAGATION:
    out << "Bound propagation";
    break;
  case Lib::TimeCounterUnit::TC_HANDLING_CONFLICTS:
    out << "handling conflicts";
    break;
  case Lib::TimeCounterUnit::TC_VARIABLE_SELECTION:
    out << "variable selection";
    break;
  case Lib::TimeCounterUnit::TC_DISMATCHING:
    out << "dismatching";
    break;
  case Lib::TimeCounterUnit::TC_FMB_DEF_INTRO:
    out << "fmb definition introduction";
    break;
  case Lib::TimeCounterUnit::TC_FMB_SORT_INFERENCE:
    out << "fmb sort inference"; 
    break;
  case Lib::TimeCounterUnit::TC_FMB_FLATTENING:
    out << "fmb flattening";
    break;
  case Lib::TimeCounterUnit::TC_FMB_SPLITTING:
    out << "fmb splitting";
    break;
  case Lib::TimeCounterUnit::TC_FMB_SAT_SOLVING:
    out << "fmb sat solving";
    break;
  case Lib::TimeCounterUnit::TC_FMB_CONSTRAINT_CREATION:
    out << "fmb constraint creation";
    break;
  case Lib::TimeCounterUnit::TC_HCVI_COMPUTE_HASH:
    out << "hvci compute hash";
    break;
  case Lib::TimeCounterUnit::TC_HCVI_INSERT:
    out << "hvci insert";
    break;
  case Lib::TimeCounterUnit::TC_HCVI_RETRIEVE:
      out << "hvci retrieve";
      break;
  case Lib::TimeCounterUnit::TC_MINISAT_ELIMINATE_VAR:
    out << "minisat eliminate var";
    break;
  case Lib::TimeCounterUnit::TC_MINISAT_BWD_SUBSUMPTION_CHECK:
      out << "minisat bwd subsumption check";
      break;
  case Lib::TimeCounterUnit::TC_Z3_IN_FMB:
    out << "smt search for next domain size assignment";
    break;
  case Lib::TimeCounterUnit::TC_NAMING:
    out << "naming";
  case Lib::TimeCounterUnit::TC_LITERAL_SELECTION:
    out << "literal selection";
    break;
  case Lib::TimeCounterUnit::TC_PASSIVE_CONTAINER_MAINTENANCE:
    out << "passive container maintenance";
    break;
  case Lib::TimeCounterUnit::TC_THEORY_INST_SIMP:
    out << "theory instantiation and simplification";
    break;
  default:
    ASSERTION_VIOLATION;
  }
  out<<": ";

  Timer::printMSString(out, s_measuredTimes[(unsigned)tcu]);

  if (s_measuredTimesChildren[(unsigned)tcu] > 0) {
    out << " ( own ";
    Timer::printMSString(out, s_measuredTimes[(unsigned)tcu]-s_measuredTimesChildren[(unsigned)tcu]);
    out << " ) ";
  }
  
  out<<endl;
}

