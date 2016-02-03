#include "sat_api.h"
#include "vector.h"

/******************************************************************************
 * We explain here the functions you need to implement
 *
 * Rules:
 * --You cannot change any parts of the function signatures
 * --You can/should define auxiliary functions to help implementation
 * --You can implement the functions in different files if you wish
 * --That is, you do not need to put everything in a single file
 * --You should carefully read the descriptions and must follow each requirement
 ******************************************************************************/

/******************************************************************************
 * Variables
 ******************************************************************************/

//returns a variable structure for the corresponding index
Var* sat_index2var(c2dSize index, const SatState* sat_state) {
	return vector_get(&sat_state->vars, index - 1);
}

//returns the index of a variable
c2dSize sat_var_index(const Var* var) {
	return var->index;
}

//returns the variable of a literal
Var* sat_literal_var(const Lit* lit) {
	return lit->var;
}

//returns 1 if the variable is instantiated, 0 otherwise
//a variable is instantiated either by decision or implication (by unit resolution)
BOOLEAN sat_instantiated_var(const Var* var) {
	Lit* plit = sat_pos_literal(var);
	Lit* nlit = sat_neg_literal(var);
	return sat_implied_literal(plit) || sat_implied_literal(nlit);
}

//returns 1 if all the clauses mentioning the variable are subsumed, 0 otherwise
BOOLEAN sat_irrelevant_var(const Var* var) {
	c2dSize occurences = sat_var_occurences(var);
	for (c2dSize i = 0; i < occurences; i++) {
		Clause* clause = sat_clause_of_var(i, var);
		if (!sat_subsumed_clause(clause))
			return 0;
	}
	return 1;
}

//returns the number of variables in the cnf of sat state
c2dSize sat_var_count(const SatState* sat_state) {
	return sat_state->varnum;
}

//returns the number of clauses mentioning a variable
//a variable is mentioned by a clause if one of its literals appears in the clause
c2dSize sat_var_occurences(const Var* var) {
	return vector_size(&var->mentions);
}

//returns the index^th clause that mentions a variable
//index starts from 0, and is less than the number of clauses mentioning the variable
//this cannot be called on a variable that is not mentioned by any clause
Clause* sat_clause_of_var(c2dSize index, const Var* var) {
	return vector_get(&var->mentions, index);
}

/******************************************************************************
 * Literals 
 ******************************************************************************/

//returns a literal structure for the corresponding index
Lit* sat_index2literal(c2dLiteral index, const SatState* sat_state) {
	if (index == 0)
		return NULL;
	if (index > 0)
		return vector_get(&sat_state->plits, index - 1);
	else
		return vector_get(&sat_state->nlits, -index - 1);
}

//returns the index of a literal
c2dLiteral sat_literal_index(const Lit* lit) {
	return lit->index;
}

//returns the positive literal of a variable
Lit* sat_pos_literal(const Var* var) {
	return var->plit;
}

//returns the negative literal of a variable
Lit* sat_neg_literal(const Var* var) {
	return var->nlit;
}

Lit* sat_opp_literal(const Lit* lit) {
	Var* var = sat_literal_var(lit);
	return lit->index > 0 ? sat_neg_literal(var) : sat_pos_literal(var);
}

//returns 1 if the literal is implied, 0 otherwise
//a literal is implied by deciding its variable, or by inference using unit resolution
BOOLEAN sat_implied_literal(const Lit* lit) {
	return lit->implied;
}

//sets the literal to true, and then runs unit resolution
//returns a learned clause if unit resolution detected a contradiction, NULL otherwise
//
//if the current decision level is L in the beginning of the call, it should be updated 
//to L+1 so that the decision level of lit and all other literals implied by unit resolution is L+1
Clause* sat_decide_literal(Lit* lit, SatState* sat_state) {
	lit->implied = 1;
	vector_push(&sat_state->ds, lit);
	vector_push(&sat_state->s, lit);
	sat_literal_var(lit)->level = vector_size(&sat_state->ds) + 1;
	if (sat_unit_resolution(sat_state))
		return NULL;
	return sat_state->ac;
}

BOOLEAN sat_check_subsumed_clause(const Clause* clause);
void sat_restore_literal(SatState* sat_state, Lit* lit) {
	lit->implied = 0;
	Var* var = sat_literal_var(lit);
	for (c2dSize i = 0; i < sat_var_occurences(var); i++) {
		Clause* clause = sat_clause_of_var(i, var);
		if (sat_subsumed_clause(clause)) {
			clause->subsumed = sat_check_subsumed_clause(clause);
			if (!sat_subsumed_clause(clause))
				vector_push(&sat_state->q, clause);
		}
	}
	for (c2dSize i = 0; i < vector_size(&var->mentions_lc); i++) {
		Clause* clause = vector_get(&var->mentions_lc, i);
		if (sat_subsumed_clause(clause)) {
			clause->subsumed = sat_check_subsumed_clause(clause);
			if (!sat_subsumed_clause(clause))
				vector_push(&sat_state->q, clause);
		}
	}
}

//undoes the last literal decision and the corresponding implications obtained by unit resolution
//
//if the current decision level is L in the beginning of the call, it should be updated 
//to L-1 before the call ends
void sat_undo_decide_literal(SatState* sat_state) {
	Lit* lit = vector_top(&sat_state->ds);
	sat_restore_literal(sat_state, lit);
	vector_pop(&sat_state->ds);
	vector_pop(&sat_state->s);
	sat_undo_unit_resolution(sat_state);
}

/******************************************************************************
 * Clauses 
 ******************************************************************************/

//returns a clause structure for the corresponding index
Clause* sat_index2clause(c2dSize index, const SatState* sat_state) {
	return vector_get(&sat_state->kb, index - 1);
}

//returns the index of a clause
c2dSize sat_clause_index(const Clause* clause) {
	return clause->index;
}

//returns the literals of a clause
Lit** sat_clause_literals(const Clause* clause) {
	return (Lit**) vector_toarr(&clause->lits);
}

//returns the number of literals in a clause
c2dSize sat_clause_size(const Clause* clause) {
	return vector_size(&clause->lits);
}

//returns 1 if the clause is subsumed, 0 otherwise
BOOLEAN sat_subsumed_clause(const Clause* clause) {
	return clause->subsumed;
}

BOOLEAN sat_check_subsumed_clause(const Clause* clause) {
	c2dSize size = sat_clause_size(clause);
	for (c2dSize i = 0; i < size; i++) {
		Lit* lit = vector_get(&clause->lits, i);
		if (sat_implied_literal(lit))
			return 1;
	}
	return 0;
}

//returns the number of clauses in the cnf of sat state
c2dSize sat_clause_count(const SatState* sat_state) {
	return sat_state->clausenum;
}

//returns the number of learned clauses in a sat state (0 when the sat state is constructed)
c2dSize sat_learned_clause_count(const SatState* sat_state) {
	return vector_size(&sat_state->lc);
}

//adds clause to the set of learned clauses, and runs unit resolution
//returns a learned clause if unit resolution finds a contradiction, NULL otherwise
//
//this function is called on a clause returned by sat_decide_literal() or sat_assert_clause()
//moreover, it should be called only if sat_at_assertion_level() succeeds
Clause* sat_assert_clause(Clause* clause, SatState* sat_state) {
	clause->index = sat_clause_count(sat_state) + sat_learned_clause_count(sat_state) + 1;
	for (c2dSize i = 0; i < sat_clause_size(clause); i++) {
		Lit* lit = vector_get(&clause->lits, i);
		Var* var = sat_literal_var(lit);
		if (vector_size(&var->mentions_lc) == 0 || vector_top(&var->mentions_lc) != clause)
			vector_push(&var->mentions_lc, clause);
	}
	vector_push(&sat_state->lc, clause);
	vector_push(&sat_state->q, clause);
	if (sat_unit_resolution(sat_state))
		return NULL;
	return sat_state->ac;
}

void sat_get_assert_clause(SatState* sat_state, Clause *ac, c2dSize clauseindex, c2dSize m, c2dLiteral p) {
	while (1) {
		Clause* clause;
		if (clauseindex < sat_clause_count(sat_state))
			clause = vector_get(&sat_state->kb, clauseindex);
		else
			clause = vector_get(&sat_state->lc, clauseindex - sat_clause_count(sat_state));
		for (c2dSize i = 0; i < vector_size(&clause->lits); i++) {
			Lit* lit = vector_get(&clause->lits, i);
			Var* var = sat_literal_var(lit);
			if (var->u)
				continue;
			var->u = 1;
			if (var->level < vector_size(&sat_state->ds) + 1)
				vector_push(&ac->lits, lit);
			else
				m++;
		}
		if (p < 0)
			return;
		Lit* lit = vector_get(&sat_state->s, p);
		Var* var = sat_literal_var(lit);
		while (!var->u) {
			if (--p < 0)
				return;
			lit = vector_get(&sat_state->s, p);
			var = sat_literal_var(lit);
		}
		if (m == 1) {
			vector_push(&ac->lits, sat_opp_literal(lit));
			break;
		}
		clauseindex = lit->locate;
		m--;
		p--;
	}
}

/******************************************************************************
 * A SatState should keep track of pretty much everything you will need to
 * condition/uncondition variables, perform unit resolution, and do clause learning
 *
 * Given an input cnf file you should construct a SatState
 *
 * This construction will depend on how you define a SatState
 * Still, you should at least do the following:
 * --read a cnf (in DIMACS format, possible with weights) from the file
 * --initialize variables (n of them)
 * --initialize literals  (2n of them)
 * --initialize clauses   (m of them)
 *
 * Once a SatState is constructed, all of the functions that work on a SatState
 * should be ready to use
 *
 * You should also write a function that frees the memory allocated by a
 * SatState (sat_state_free)
 ******************************************************************************/

//constructs a SatState from an input cnf file
SatState* sat_state_new(const char* file_name) {
	FILE *file;
	if (!(file = fopen(file_name, "r")))
		return NULL;
	SatState *sat_state = malloc(sizeof(SatState));
	while (!feof(file)) {
		if (fgetc(file) == 'p')
			break;
		while (fgetc(file) != '\n')
			continue;
	}
	fscanf(file, " cnf %lu %lu", &sat_state->varnum, &sat_state->clausenum);
	vector_init(&sat_state->vars);
	vector_init(&sat_state->plits);
	vector_init(&sat_state->nlits);
	vector_init(&sat_state->kb);
	vector_init(&sat_state->lc);
	vector_init(&sat_state->ds);
	vector_init(&sat_state->il);
	vector_init(&sat_state->q);
	vector_init(&sat_state->s);
	sat_state->ac = NULL;
	for (c2dSize i = 1; i <= sat_var_count(sat_state); i++) {
		Var* var = malloc(sizeof(Var));
		var->index = i;
		var->mark = 0;
		vector_init(&var->mentions);
		vector_init(&var->mentions_lc);
		Lit* plit = malloc(sizeof(Lit));
		plit->index = i;
		plit->implied = 0;
		plit->var = var;
		Lit* nlit = malloc(sizeof(Lit));
		nlit->index = -i;
		nlit->implied = 0;
		nlit->var = var;
		vector_push(&sat_state->plits, plit);
		vector_push(&sat_state->nlits, nlit);
		var->plit = plit;
		var->nlit = nlit;
		vector_push(&sat_state->vars, var);
	}
	for (c2dSize i = 1; i <= sat_clause_count(sat_state); i++) {
		Clause* clause = malloc(sizeof(Clause));
		clause->index = i;
		clause->subsumed = 0;
		clause->mark = 0;
		vector_init(&clause->lits);
		while (1) {
			c2dLiteral index;
			while (!fscanf(file, "%ld", &index) || (index == 0 && vector_size(&clause->lits) == 0)) {
				while (fgetc(file) != '\n')
					continue;
			}
			if (index == 0)
				break;
			vector_push(&clause->lits, sat_index2literal(index, sat_state));
		}
		vector_push(&sat_state->kb, clause);
		vector_push(&sat_state->q, clause);
	}
	for (c2dSize i = 1; i <= sat_clause_count(sat_state); i++) {
		Clause* clause = sat_index2clause(i, sat_state);
		for (c2dSize j = 0; j < sat_clause_size(clause); j++) {
			Lit* lit = vector_get(&clause->lits, j);
			Var* var = sat_literal_var(lit);
			if (vector_size(&var->mentions) == 0 || vector_top(&var->mentions) != clause)
				vector_push(&var->mentions, clause);
		}
	}
	fclose(file);
	return sat_state;
}

//frees the SatState
void sat_state_free(SatState* sat_state) {
	for (c2dSize i = 1; i <= sat_var_count(sat_state); i++) {
		Var* var = sat_index2var(i, sat_state);
		vector_free(&var->mentions);
		vector_free(&var->mentions_lc);
		free(var);
		free(sat_index2literal(i, sat_state));
		free(sat_index2literal(-i, sat_state));
	}
	for (c2dSize i = 1; i <= sat_clause_count(sat_state); i++) {
		Clause* clause = sat_index2clause(i, sat_state);
		vector_free(&clause->lits);
		free(clause);
	}
	vector_free(&sat_state->vars);
	vector_free(&sat_state->plits);
	vector_free(&sat_state->nlits);
	vector_free(&sat_state->kb);
	vector_free(&sat_state->lc);
	vector_free(&sat_state->ds);
	vector_free(&sat_state->il);
	vector_free(&sat_state->q);
	vector_free(&sat_state->s);
	free(sat_state);
}

/******************************************************************************
 * Given a SatState, which should contain data related to the current setting
 * (i.e., decided literals, subsumed clauses, decision level, etc.), this function 
 * should perform unit resolution at the current decision level 
 *
 * It returns 1 if succeeds, 0 otherwise (after constructing an asserting
 * clause)
 *
 * There are three possible places where you should perform unit resolution:
 * (1) after deciding on a new literal (i.e., in sat_decide_literal())
 * (2) after adding an asserting clause (i.e., in sat_assert_clause(...)) 
 * (3) neither the above, which would imply literals appearing in unit clauses
 *
 * (3) would typically happen only once and before the other two cases
 * It may be useful to distinguish between the above three cases
 * 
 * Note if the current decision level is L, then the literals implied by unit
 * resolution must have decision level L
 *
 * This implies that there must be a start level S, which will be the level
 * where the decision sequence would be empty
 *
 * We require you to choose S as 1, then literals implied by (3) would have 1 as
 * their decision level (this level will also be the assertion level of unit
 * clauses)
 *
 * Yet, the first decided literal must have 2 as its decision level
 ******************************************************************************/

//applies unit resolution to the cnf of sat state
//returns 1 if unit resolution succeeds, 0 if it finds a contradiction
BOOLEAN sat_unit_resolution(SatState* sat_state) {
	BOOLEAN more = 1;
	while (more) {
		more = 0;
		for (c2dSize i = vector_size(&sat_state->q); i >= 1; i--) {
			Clause* clause = vector_get(&sat_state->q, i - 1);
			clause->subsumed = sat_check_subsumed_clause(clause);
			if (sat_subsumed_clause(clause)) {
				vector_erase(&sat_state->q, i - 1);
				continue;
			}
			BOOLEAN flag = 0;
			c2dSize pos;
			for (c2dSize j = 0; j < sat_clause_size(clause); j++) {
				Lit* lit = vector_get(&clause->lits, j);
				if (!sat_implied_literal(sat_opp_literal(lit))) {
					flag++;
					pos = j;
					if (flag == 2)
						break;
				}
			}
			if (flag == 0) {
				sat_state->ac = malloc(sizeof(Clause));
				vector_init(&sat_state->ac->lits);
				sat_state->ac->subsumed = 0;
				sat_state->ac->mark = 0;
				if (vector_size(&sat_state->ds) > 0) {
					for (c2dSize j = 0; j < sat_var_count(sat_state); j++) {
						Var* var = vector_get(&sat_state->vars, j);
						var->u = var->level <= 1;
					}
					sat_get_assert_clause(sat_state, sat_state->ac, clause->index - 1, 0,
							vector_size(&sat_state->s) - 1);
				}
				return 0;
			}
			if (flag == 1) {
				Lit* lit = vector_get(&clause->lits, pos);
				lit->implied = 1;
				lit->locate = clause->index - 1;
				lit->var->level = vector_size(&sat_state->ds) + 1;
				vector_push(&sat_state->il, lit);
				vector_push(&sat_state->s, lit);
				clause->subsumed = 1;
				vector_erase(&sat_state->q, i - 1);
				more = 1;
			}
		}
	}
	return 1;
}

//undoes sat_unit_resolution(), leading to un-instantiating variables that have been instantiated
//after sat_unit_resolution()
void sat_undo_unit_resolution(SatState* sat_state) {
	while (vector_size(&sat_state->il) > 0) {
		Lit* lit = vector_top(&sat_state->il);
		if (lit->var->level > vector_size(&sat_state->ds) + 1) {
			sat_restore_literal(sat_state, lit);
			vector_pop(&sat_state->il);
			vector_pop(&sat_state->s);
		} else
			break;
	}
}

//returns 1 if the decision level of the sat state equals to the assertion level of clause,
//0 otherwise
//
//this function is called after sat_decide_literal() or sat_assert_clause() returns clause.
//it is used to decide whether the sat state is at the right decision level for adding clause.
BOOLEAN sat_at_assertion_level(const Clause* clause, const SatState* sat_state) {
	c2dSize h1 = 1;
	c2dSize h2 = 1;
	for (c2dSize i = 0; i < vector_size(&clause->lits); i++) {
		Lit* lit = vector_get(&clause->lits, i);
		Var* var = sat_literal_var(lit);
		if (var->level >= h1) {
			h2 = h1;
			h1 = var->level;
		} else {
			if (var->level >= h2)
				h2 = var->level;
		}
	}
	return h2 == vector_size(&sat_state->ds) + 1;
}

/******************************************************************************
 * The functions below are already implemented for you and MUST STAY AS IS
 ******************************************************************************/

//returns the weight of a literal (which is 1 for our purposes)
c2dWmc sat_literal_weight(const Lit* lit) {
	return 1;
}

//returns 1 if a variable is marked, 0 otherwise
BOOLEAN sat_marked_var(const Var* var) {
	return var->mark;
}

//marks a variable (which is not marked already)
void sat_mark_var(Var* var) {
	var->mark = 1;
}

//unmarks a variable (which is marked already)
void sat_unmark_var(Var* var) {
	var->mark = 0;
}

//returns 1 if a clause is marked, 0 otherwise
BOOLEAN sat_marked_clause(const Clause* clause) {
	return clause->mark;
}

//marks a clause (which is not marked already)
void sat_mark_clause(Clause* clause) {
	clause->mark = 1;
}
//unmarks a clause (which is marked already)
void sat_unmark_clause(Clause* clause) {
	clause->mark = 0;
}

/******************************************************************************
 * end
 ******************************************************************************/
