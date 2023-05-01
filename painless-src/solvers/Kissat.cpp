// -----------------------------------------------------------------------------
// Copyright (C) 2017  Ludovic LE FRIOUX
//
// This file is part of PaInleSS.
//
// PaInleSS is free software: you can redistribute it and/or modify it under the
// terms of the GNU General Public License as published by the Free Software
// Foundation, either version 3 of the License, or (at your option) any later
// version.
//
// This program is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
// FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
// details.
//
// You should have received a copy of the GNU General Public License along with
// this program.  If not, see <http://www.gnu.org/licenses/>.
// -----------------------------------------------------------------------------

// Kissat includes
extern "C" {
   #include "src/application.h"
   #include "src/parse.h"
   #include "src/internal.h"
   #include "src/witness.h"
   #include "src/import.h"
}
#include "../utils/Logger.h"
#include "../utils/System.h"
#include "../utils/Parameters.h"
#include "../clauses/ClauseManager.h"
#include "../solvers/Kissat.h"


// Macros for minisat literal representation conversion
#define MIDX(LIT) (((unsigned)(LIT)) >> 1)
#define MNEGATED(LIT) (((LIT) & 1u))
#define MNOT(LIT) (((LIT) ^ 1u))



void cbkKissatExportClause(void * issuer, int lbd, cvec *cls)
{
	KissatSolver* mp = (KissatSolver*)issuer;

	// if (lbd > mp->lbdLimit || cls->sz > 2)
	if (lbd > mp->lbdLimit)
      return;

	ClauseExchange * ncls = ClauseManager::allocClause(cls->sz);

	for (int i = 0; i < cls->sz; i++) {
      int v = cvec_data(cls, i);
      int iidx = MIDX(v);
      int sign = MNEGATED(v); //sign = 1 -; 0 +
      if (v & 1) assert(sign == 1);
      else assert(sign == 0);
      int eidx = PEEK_STACK(mp->solver->exportk, iidx);
      assert(iidx == eidx - 1);
		ncls->lits[i] = sign == 1 ? -eidx : eidx;      
      // mp->outputf << ncls->lits[i] << " ";
	}
   // mp->outputf << "0" << endl;
   ncls->lbd  = lbd;
   ncls->from = mp->id;

   mp->clausesToExport.addClause(ncls);
}

int cbkKissatImportUnit(void * issuer)
{
   KissatSolver * mp = (KissatSolver*)issuer;

   int l = -1;

   ClauseExchange * cls = NULL;

   if (mp->unitsToImport.getClause(&cls) == false)
      return l;

   int eidx = abs(cls->lits[0]);
   import *import = &PEEK_STACK (mp->solver->import, eidx);
   if (import->eliminated) {
      l = -10;   
   }
   else {
      assert(import->imported);
      l = import->lit;
      if (cls->lits[0] < 0) l = MNOT(l);
   }
   ClauseManager::releaseClause(cls);

   return l;
}

int cbkKissatImportClause(void * issuer, int * lbd, cvec *mcls)
{
   KissatSolver* mp = (KissatSolver*)issuer;

   ClauseExchange * cls = NULL;

   if (mp->clausesToImport.getClause(&cls) == false)
      return -1;
   assert(mcls->sz==0);
   bool alreadySat = false;
   for (size_t i = 0; i < cls->size; i++) {
      int eidx = abs(cls->lits[i]);
      import *import = &PEEK_STACK (mp->solver->import, eidx);
      if (import->eliminated) {
         alreadySat = true;
      }
      else {
         assert(import->imported);
         int ilit = import->lit;
         assert(ilit == 2 * eidx - 2);
         if (cls->lits[i] < 0) ilit = MNOT(ilit);
         cvec_push(mcls, ilit);
      }
   }

   *lbd = cls->lbd;

   ClauseManager::releaseClause(cls);

   if (alreadySat) 
      return -10;

   return 1;
}

KissatSolver::KissatSolver(int id) : SolverInterface(id, MAPLE)
{
	lbdLimit = Parameters::getIntParam("lbd-limit", 2);

	solver = kissat_init();
   // outputf.open((to_string(id) + ".txt").c_str());
	solver->cbkExportClause = cbkKissatExportClause;
	solver->cbkImportClause = cbkKissatImportClause;
	solver->cbkImportUnit   = cbkKissatImportUnit;
	solver->issuer          = this;
}

KissatSolver::~KissatSolver()
{
	delete solver;
}

void 
KissatSolver::addOriginClauses(simplify *S) {
   solver->max_var = S->vars;
   // kissat_mab_parse(solver);
   kissat_reserve(solver, S->vars);
   for (int i = 1; i <= S->clauses; i++) {
      int l = S->clause[i].size();
      for (int j = 0; j < l; j++)
         kissat_add(solver, S->clause[i][j]);
      kissat_add(solver, 0);
   }
}

bool
KissatSolver::loadFormula(const char* filename)
{
   // kissat_mab_parse(solver);
   strictness strict = NORMAL_PARSING;
   file in;
   uint64_t lineno;
   kissat_open_to_read_file(&in, filename);
   kissat_parse_dimacs(solver, strict, &in, &lineno, &solver->max_var);
   kissat_close_file(&in);
   // print_options(solver);
   return true;
}

//Get the number of variables of the formula
int
KissatSolver::getVariablesCount()
{
	return solver->vars;
}

// Get a variable suitable for search splitting
int
KissatSolver::getDivisionVariable()
{
   return (rand() % getVariablesCount()) + 1;
}

// Set initial phase for a given variable
void
KissatSolver::setPhase(const int var, const bool phase)
{
   int idx = MIDX(kissat_import_literal(solver, var));
   //solver->init_phase[idx] = phase ? 1 : -1;
   }

// Bump activity for a given variable
void
KissatSolver::bumpVariableActivity(const int var, const int times)
{
}

// Interrupt the SAT solving, so it can be started again with new assumptions
void
KissatSolver::setSolverInterrupt()
{
   stopSolver = true;

   kissat_terminate(solver);
}

void
KissatSolver::unsetSolverInterrupt()
{
   stopSolver = false;
}

void
KissatSolver::setBumpVar(int v) {
   bump_var = v;
}

// Diversify the solver
void
KissatSolver::diversify(int id)
{

int configId = id%24;
 switch(configId){ 
        case 0 : kissat_set_configuration (solver, "default");
            break;
        case 1 : 
           kissat_set_configuration (solver, "sat");
            break;
        case 2 : 
            kissat_set_configuration (solver, "unsat");
            break;  
        case 3 : 
            //default_chrono_false
            kissat_set_configuration (solver, "default");
            kissat_set_option(solver, "chrono", false);
            break;    
        case 4 :
            //default_chrono_false_phase_false
            kissat_set_configuration (solver, "default");
            kissat_set_option(solver, "chrono", false);
            kissat_set_option(solver, "phase", false);
            
            break;
        case 5 : 
            //default_phase_false
            kissat_set_configuration (solver, "default");
            kissat_set_option(solver, "phase", false);

            break;
        case 6 : 
            //default_stable_2_chrono_false
            kissat_set_configuration (solver, "default");
            kissat_set_option(solver, "stable", 2);
            kissat_set_option(solver, "chrono", false);
            break;
        case 7 : 
            //default_target_0
            kissat_set_configuration (solver, "default");
            kissat_set_option(solver, "target", 0);

            break;
        case 8 : 
            //default_target_0_chrono_false_phase_false
            kissat_set_configuration (solver, "default");
            kissat_set_option(solver, "target", 0);
            kissat_set_option(solver, "chrono", false);
            kissat_set_option(solver, "phase", false);

            break;
        case 9 : 
            //default_target_0_phase_false
            // kissat_set_configuration (solver, "default");
            // kissat_set_option(solver, "target", 0);
            // kissat_set_option(solver, "phase", false);
            kissat_set_configuration (solver, "default");
            kissat_set_option(solver, "target", 1);
            kissat_set_option(solver, "walkinitially", true);
            kissat_set_option(solver, "chrono", true);

            break;
        case 10 : 
            //default_walkinitially_true
            kissat_set_configuration (solver, "default");
            kissat_set_option(solver, "walkinitially", true);

            break;
        case 11 : 
            //sat_chrono_false
            kissat_set_configuration (solver, "sat");
            kissat_set_option(solver, "chrono", false);
            
            break;
        case 12 : 
            //sat_chrono_false_phase_false
            kissat_set_configuration (solver, "sat");
            kissat_set_option(solver, "chrono", false);
            kissat_set_option(solver, "phase", false);

            break;
        case 13 : 
            //sat_chrono_false_phase_false_tier1_3
            kissat_set_configuration (solver, "sat");
            kissat_set_option(solver, "chrono", false);
            kissat_set_option(solver, "phase", false);
            kissat_set_option(solver, "tier1", 3);

            break;
        case 14 : 
            //sat_chrono_false_tier1_3
            kissat_set_configuration (solver, "sat");
            kissat_set_option(solver, "chrono", false);
            kissat_set_option(solver, "tier1", 3);

            break;
        case 15 : 
            //sat_phase_false
            kissat_set_configuration (solver, "sat");
            kissat_set_option(solver, "phase", false);

            break;
        case 16 : 
            //sat_stable_2_chrono_false
            kissat_set_configuration (solver, "sat");
            kissat_set_option(solver, "stable", 2);
            kissat_set_option(solver, "chrono", false);
            break;
        case 17 : 
            //sat_target_0 or default_target_0 (since sat \equiv default && target 2)
            kissat_set_configuration (solver, "default");
            kissat_set_option(solver, "target", 0);
            break;
        case 18 : 
            //sat_target_0_chrono_false_phase_false or default_target_0_chrono_false_phase_false (since sat \equiv default && target 2)
            kissat_set_configuration (solver, "default");
            kissat_set_option(solver, "target", 0);
            kissat_set_option(solver, "chrono", false);
            kissat_set_option(solver, "phase", false);
            break;
        case 19 : 
            //sat_target_0_phase_false or default_target_0_phase_false (since sat \equiv default && target 2)
            kissat_set_configuration (solver, "default");
            kissat_set_option(solver, "target", 0);
            kissat_set_option(solver, "phase", false);
            
            break;
        case 20 : 
            //sat_target_0_tier1_3
            kissat_set_configuration (solver, "sat");
            kissat_set_option(solver, "target", 0);
            kissat_set_option(solver, "tier1", 3);
            break;
        case 21 : 
            //sat_tier1_3
            kissat_set_configuration (solver, "sat");
            kissat_set_option(solver, "tier1", 3);

            break;
        case 22 : 
            //sat_walkinitially_true
            kissat_set_configuration (solver, "sat");
            kissat_set_option(solver, "walkinitially", true);
            break;
        case 23 : 
            //unsat_stable_2_chrono_false
            kissat_set_configuration (solver, "unsat");
            kissat_set_option(solver, "chrono", false);

            break;
        default:
            kissat_set_configuration (solver, "default");
            break;
    }
    
   //  int chrono = kissat_get_option(solver, "chrono");
   //  int stable = kissat_get_option(solver, "stable");
   //  int walkinitially = kissat_get_option(solver, "walkinitially");
   //  int target = kissat_get_option(solver, "target");
   //  int tier1 = kissat_get_option(solver, "tier1");
   //  int phase = kissat_get_option(solver, "phase");
   //  printf("\nc time = %f s ** id = %d / %s=%d / %s=%d / %s=%d / %s=%d / %s=%d/ %s=%d",getRelativeTime(), id, "tier1", tier1, "chrono", chrono, "stable", stable, "walkinitially", walkinitially, "target", target, "phase", phase);
   //  fflush(stdout);

   // if (Parameters::getBoolParam("bump")) {
   //    if (id && solver->initshuffle == -1) solver->bump_one=bump_var;
   // }
   // // if (id == ID_XOR) {
   // //    solver->GE = true;
   // // } else {
   // //    solver->GE = false;
   // // }

   // // if (id % 2) {
   // //    solver->VSIDS = false;
   // // } else {
   // //    solver->VSIDS = true;
   // // }
   // if (Parameters::getBoolParam("verso")) {
   //    if (id % 2 == 0) {
   //       solver->verso = 0;
   //    } else {
   //       solver->verso = 1;
   //    }
   // }
}

void
KissatSolver::initshuffle(int id)
{
   // if (id) solver->initshuffle = id;
   // if (id) solver->bump_one=rand()%solver->max_var+1;
   // if (id == ID_XOR) {
   //    solver->GE = true;
   // } else {
   //    solver->GE = false;
   // }

   // if (id % 2) {
   //    solver->VSIDS = false;
   // } else {
   //    solver->VSIDS = true;
   // }

   // if (id % 4 >= 2) {
   //    solver->verso = false;
   // } else {
   //    solver->verso = true;
   // }
}

void 
KissatSolver::setParameter(parameter p)
{

   kissat_set_option (solver, "tier1", p.tier1);
   kissat_set_option (solver, "chrono", p.chrono);
   kissat_set_option (solver, "stable", p.stable);
   kissat_set_option (solver, "walkinitially", p.walkinitially);
   kissat_set_option (solver, "target", p.target);
   kissat_set_option (solver, "phase", p.phase);
   kissat_set_option (solver, "targetinc", p.targetinc);
   kissat_set_option (solver, "ccanr", p.ccanr);
   if (p.ccanr == 1) {
      kissat_set_option (solver, "rephaseint", 80);
      kissat_set_option (solver, "rephaseinit", 80);
   }
   
   // printf("c\t\t id %d: chrono=%d stable=%d target=%d phase=%d targetinc=%d ccanr=%d initshuffle=%d\n",
   // id,
   // kissat_get_option(solver, "chrono"),
   // kissat_get_option(solver, "stable"),
   // kissat_get_option(solver, "target"),
   // kissat_get_option(solver, "phase"),
   // kissat_get_option(solver, "targetinc"),
   // kissat_get_option(solver, "ccanr"),
   // solver->initshuffle
   // );
   
}
// Solve the formula with a given set of assumptions
// return 10 for SAT, 20 for UNSAT, 0 for UNKNOWN
SatResult
KissatSolver::solve(const std::vector<int> & cube)
{
   unsetSolverInterrupt();

   std::vector<ClauseExchange *> tmp;

   tmp.clear();
   clausesToAdd.getClauses(tmp);
   for (size_t ind = 0; ind < tmp.size(); ind++) {
      for (size_t i = 0; i < tmp[ind]->size; i++)
         kissat_add(solver, tmp[ind]->lits[i]);
      kissat_add(solver, 0);
      ClauseManager::releaseClause(tmp[ind]);
   }
   assert(cube.size() == 0);
   int res = kissat_solve(solver);
   if (res == 10)
      return SAT;
   if (res == 20)
      return UNSAT;
   return UNKNOWN;
}


void
KissatSolver::addClause(ClauseExchange * clause)
{
}

void
KissatSolver::addLearnedClause(ClauseExchange * clause)
{
   if (clause->size == 1) {
      unitsToImport.addClause(clause);
   } else {
      clausesToImport.addClause(clause);
   }
}

void
KissatSolver::addClauses(const std::vector<ClauseExchange *> & clauses)
{
}


void
KissatSolver::addInitialClauses(const std::vector<ClauseExchange *> & clauses)
{
}

void
KissatSolver::addLearnedClauses(const std::vector<ClauseExchange *> & clauses)
{
   for (size_t i = 0; i < clauses.size(); i++) {
      addLearnedClause(clauses[i]);
   }
}

void
KissatSolver::getLearnedClauses(std::vector<ClauseExchange *> & clauses)
{
   clausesToExport.getClauses(clauses);
}

void
KissatSolver::increaseClauseProduction()
{
   //lbdLimit++;
}

void
KissatSolver::decreaseClauseProduction()
{
   if (lbdLimit > 2) {
      lbdLimit--;
   }
}

SolvingStatistics
KissatSolver::getStatistics()
{
   SolvingStatistics stats;

   stats.conflicts    = solver->statistics.conflicts;
   stats.propagations = solver->statistics.propagations;
   stats.restarts     = solver->statistics.restarts;
   stats.decisions    = solver->statistics.decisions;
   stats.memPeak      = 0;

   return stats;
}

std::vector<int>
KissatSolver::getModel()
{
   std::vector<int> model;

   for (int i = 1; i <= solver->max_var; i++) {
      int tmp = kissat_value(solver, i);
      if (!tmp) tmp = i;
      model.push_back(tmp);
   }

   return model;
}


std::vector<int>
KissatSolver::getFinalAnalysis()
{
   std::vector<int> outCls;
   return outCls;
}


std::vector<int>
KissatSolver::getSatAssumptions() {
   std::vector<int> outCls;
   return outCls;
};
