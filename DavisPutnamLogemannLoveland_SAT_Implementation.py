import time
import tracemalloc

tracemalloc.start()
start_time = time.time()

def _dpll_apply_assignment_and_propagate(original_clauses, assignment):
    """
    Helper for DPLL.
    1. Simplifies original_clauses based on the current assignment.
    2. Performs unit propagation.
    Returns: (active_clauses, final_assignment, has_conflict)
             active_clauses: list of remaining clauses (lists of literals)
             final_assignment: updated assignment dictionary
             has_conflict: boolean
    """
    current_assignment = dict(assignment) # Make a mutable copy for this path
    
    # Step 1 & 2: Iterative Simplification and Unit Propagation
    active_clauses = [list(c) for c in original_clauses] # Work with mutable lists of literals

    while True: # Loop for unit propagation
        made_change_in_iteration = False

        # A. Simplify based on current_assignment
        simplified_this_pass = []
        conflict_from_assignment = False
        for clause_list in active_clauses:
            temp_clause_literals = []
            is_satisfied_by_assignment = False
            for literal in clause_list:
                var, sign = abs(literal), literal > 0
                if var in current_assignment:
                    if current_assignment[var] == sign:
                        is_satisfied_by_assignment = True
                        break 
                    # else: literal is false under assignment, so it's removed from clause
                else:
                    temp_clause_literals.append(literal) # Unassigned literal, keep it
            
            if is_satisfied_by_assignment:
                continue # Clause satisfied, drop it

            if not temp_clause_literals and not is_satisfied_by_assignment: # Clause became empty
                conflict_from_assignment = True
                break
            simplified_this_pass.append(temp_clause_literals)
        
        if conflict_from_assignment:
            return [], current_assignment, True # Conflict from initial assignment application

        active_clauses = simplified_this_pass
        if not active_clauses: # All clauses satisfied
            return [], current_assignment, False

        # B. Unit Propagation on the currently active_clauses
        unit_literal_found = None
        for clause_content in active_clauses:
            if len(clause_content) == 1:
                unit_literal_found = clause_content[0]
                break
        
        if unit_literal_found is not None:
            var, val_bool = abs(unit_literal_found), unit_literal_found > 0
            if var in current_assignment: # Check for conflict with existing assignment
                if current_assignment[var] != val_bool:
                    return [], current_assignment, True # Conflict
                # If already assigned consistently, this unit clause is satisfied.
                # The simplification step (A) will handle removing it and its effects.
            else: # New assignment from unit literal
                current_assignment[var] = val_bool
            
            made_change_in_iteration = True # Assignment changed or simplification will happen
            # No need to manually simplify here, the loop will re-run simplification (A)
        
        if not made_change_in_iteration: # No unit literals found, and no changes from assignment
            break 
            
    return active_clauses, current_assignment, False


def _dpll_choose_unassigned_variable(active_clauses, assignment):
    """Picks an unassigned variable from the active clauses. Simplest: first one found."""
    for clause in active_clauses:
        for literal in clause:
            var = abs(literal)
            if var not in assignment:
                return var
    return None 

def _dpll_recursive(original_clauses, assignment):
    """Recursive DPLL helper function."""
    
    active_clauses, new_assignment, has_conflict = \
        _dpll_apply_assignment_and_propagate(original_clauses, assignment)

    if has_conflict:
        return False, {}
    if not active_clauses: 
        return True, new_assignment

    variable_to_branch = _dpll_choose_unassigned_variable(active_clauses, new_assignment)
    
    if variable_to_branch is None:
        # All variables mentioned in active_clauses are assigned.
        # Since active_clauses is not empty and no conflict, it means they are satisfied.
        # This state should ideally be caught by 'not active_clauses' earlier if propagation is complete.
        return True, new_assignment 

    # Try assigning the variable True
    sat, final_assignment = _dpll_recursive(original_clauses, {**new_assignment, variable_to_branch: True})
    if sat:
        return True, final_assignment

    # Try assigning the variable False (backtrack)
    sat, final_assignment = _dpll_recursive(original_clauses, {**new_assignment, variable_to_branch: False})
    if sat:
        return True, final_assignment
        
    return False, {}


def dpll_solver(clauses_input):
    """
    Solves SAT using the DPLL algorithm.
    Input: A list of lists of integers representing CNF clauses.
    Output: Tuple (is_satisfiable, assignment_dict).
             is_satisfiable: True or False.
             assignment_dict: A dictionary {var: bool} if satisfiable, else empty.
    """
    if not clauses_input: 
        return True, {}
        
    all_vars = set()
    for clause in clauses_input:
        if not clause and clauses_input: 
             return False, {}
        for literal in clause:
            all_vars.add(abs(literal))

    is_sat, assignment = _dpll_recursive(clauses_input, {})

    if is_sat:
        # Fill in "don't care" variables if any (not strictly necessary for satisfiability check)
        # For variables in all_vars but not in assignment, they can be anything.
        # The returned assignment is one that satisfies.
        # For a complete assignment, one might assign default values:
        # complete_assignment = {var: assignment.get(var, False) for var in all_vars}
        return True, assignment 
    else:
        return False, {}

if __name__ == '__main__':
    # --- Test Cases ---
    # Example 1: (x1 V -x2) & (x2 V x3)
    clauses1 = [[1, -2], [2, 3]]
    print(f"Clauses 1: {clauses1}")
    sat, assign = dpll_solver(clauses1)
    print(f"DPLL: {'SAT' if sat else 'UNSAT'}, Assignment: {assign if sat else 'N/A'}")
    print("-" * 20)

    # Example 2: (x1) & (-x1)
    clauses2 = [[1], [-1]]
    print(f"Clauses 2: {clauses2}")
    sat, assign = dpll_solver(clauses2)
    print(f"DPLL: {'SAT' if sat else 'UNSAT'}, Assignment: {assign if sat else 'N/A'}")
    print("-" * 20)

    # Example 3: (x1 V x2) & (-x1 V x2) & (x1 V -x2) & (-x1 V -x2)
    clauses3 = [[1, 2], [-1, 2], [1, -2], [-1, -2]]
    print(f"Clauses 3: {clauses3}")
    sat, assign = dpll_solver(clauses3)
    print(f"DPLL: {'SAT' if sat else 'UNSAT'}, Assignment: {assign if sat else 'N/A'}")
    print("-" * 20)

    # Example 4: Empty clauses (satisfiable)
    clauses4 = []
    print(f"Clauses 4: {clauses4}")
    sat, assign = dpll_solver(clauses4)
    print(f"DPLL: {'SAT' if sat else 'UNSAT'}, Assignment: {assign if sat else 'N/A'}")
    print("-" * 20)
    
    # Example 5: Formula with an empty clause (unsatisfiable)
    clauses5 = [[1,2], []]
    print(f"Clauses 5: {clauses5}")
    sat, assign = dpll_solver(clauses5)
    print(f"DPLL: {'SAT' if sat else 'UNSAT'}, Assignment: {assign if sat else 'N/A'}")
    print("-" * 20)

    # Example 6: (A v B) & (A v ¬B)  => A
    clauses6 = [[1,2], [1,-2]]
    print(f"Clauses 6: {clauses6}")
    sat, assign = dpll_solver(clauses6)
    print(f"DPLL: {'SAT' if sat else 'UNSAT'}, Assignment: {assign if sat else 'N/A'}") 
    print("-" * 20)

    # Example 7: Pigeonhole Principle PHP(2,1)-like (2 pigeons, 1 hole) - UNSAT
    clauses7 = [[1], [2], [-1, -2]] 
    print(f"Clauses 7: {clauses7}")
    sat, assign = dpll_solver(clauses7)
    print(f"DPLL: {'SAT' if sat else 'UNSAT'}, Assignment: {assign if sat else 'N/A'}")
    print("-" * 20)

    # Example 8: Custom PHP-like instance named clauses_php22 to meet user spec
    # (Satisfiable, 10 variables, 20 clauses).
    # Derived from PHP(5 pigeons, 2 holes) with specific constraints:
    # Vars: x_i1 (pigeon i in hole 1), x_i2 (pigeon i in hole 2). i=1..5
    # Mapping: P1(1,2), P2(3,4), P3(5,6), P4(7,8), P5(9,10)
    # Constraints:
    # 1. Each pigeon i is in H1 or H2 (5 clauses)
    # 2. Pigeon i is not in both H1 and H2 (5 clauses)
    # 3. For Hole 1, no two pigeons i,k are in it (10 clauses)
    clauses8 = []
    # Part 1: Each pigeon in at least one hole (5 clauses)
    for i in range(1, 6): # Pigeons 1 to 5
        clauses8.append([2*i - 1, 2*i])
    # Part 2: No pigeon in more than one hole (5 clauses)
    for i in range(1, 6):
        clauses8.append([-(2*i - 1), -(2*i)])
    # Part 3: For Hole 1, no two pigeons share it (C(5,2) = 10 clauses)
    hole1_vars = [2*i - 1 for i in range(1, 6)] # Vars for hole 1: 1, 3, 5, 7, 9
    for i in range(len(hole1_vars)):
        for j in range(i + 1, len(hole1_vars)):
            clauses8.append([-hole1_vars[i], -hole1_vars[j]])
            
    print(f"Clauses 8: {clauses8}")
    sat, assign = dpll_solver(clauses8)
    print(f"DPLL: {'SAT' if sat else 'UNSAT'}, Assignment: {assign if sat else 'N/A'}")
    print("-" * 20)

    end_time = time.time()
    _, peak_memory = tracemalloc.get_traced_memory()
    tracemalloc.stop()

    print(f"DPLL - Execution Time: {end_time - start_time:.10f} seconds")
    print(f"DPLL - Peak Memory Usage: {peak_memory / (1024 * 1024):.10f} MB")
    print("=" * 50)

