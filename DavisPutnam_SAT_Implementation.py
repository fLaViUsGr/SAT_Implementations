import time
import tracemalloc

tracemalloc.start()
start_time = time.time()

def _dp_simplify_clauses(clauses_set_of_sets, literal_to_make_true):
    """
    Simplifies a list of clauses (represented as sets of literals)
    given that literal_to_make_true is true.
    - Removes clauses containing literal_to_make_true.
    - Removes -literal_to_make_true from clauses where it appears.
    Returns: A new list of simplified clauses (as sets), and a conflict flag.
             Conflict is True if an empty clause is generated.
    """
    new_clauses = []
    conflict = False
    for c_orig in clauses_set_of_sets:
        c = set(c_orig) # Work with a mutable copy
        if literal_to_make_true in c:
            continue # Clause satisfied
        
        if -literal_to_make_true in c:
            c.remove(-literal_to_make_true)
        
        if not c: # Clause became empty
             # Check if it became empty *because* -literal_to_make_true was in original c_orig
             # This condition is a bit tricky. An empty clause is an empty clause.
             # The original check was: if not simplified_clause and -literal_to_make_true in c_orig_before_potential_removal:
             # This means the literal whose negation was removed was the *only* literal.
            if -literal_to_make_true in c_orig: # It became empty due to this simplification
                conflict = True
                break
            # If it was already empty, or became empty for other reasons, it's still a problem
            # but the conflict flag is more about *this specific* simplification causing it.
            # However, an empty clause means conflict regardless.
            # For DP, an empty clause at any point is a conflict.
            conflict = True 
            break

        new_clauses.append(c)
        
    if conflict:
        # Returning [{}] (list containing an empty set) is a clear signal of an empty clause.
        return [set()], True 
    return new_clauses, False


def dp_original_solver(clauses_input):
    """
    Solves SAT using the original Davis-Putnam algorithm.
    This version involves iterative unit propagation, pure literal elimination,
    and variable elimination by resolution.
    Input: A list of lists of integers representing CNF clauses.
    Output: True if satisfiable, False if unsatisfiable.
    """
    if not clauses_input:
        return True
    
    clauses = [set(c) for c in clauses_input] 
    if any(not c for c in clauses): 
        return False

    all_vars = sorted(list(set(abs(lit) for cl in clauses for lit in cl)))

    for var_to_eliminate in all_vars:
        # Loop for unit propagation and pure literal elimination until no changes
        while True:
            made_change_in_iteration = False

            # 1. Unit Propagation
            unit_literal = None
            for c in clauses:
                if len(c) == 1:
                    unit_literal = list(c)[0]
                    break
            
            if unit_literal:
                clauses_after_simplify, conflict = _dp_simplify_clauses(clauses, unit_literal)
                if conflict: return False
                if not clauses_after_simplify and not any(c for c in clauses_after_simplify if c): # All clauses satisfied
                    return True 
                if clauses_after_simplify != clauses: # Check if actual change occurred
                    clauses = clauses_after_simplify
                    made_change_in_iteration = True
                # Re-check if var_to_eliminate is still relevant
                if not any(var_to_eliminate in cl or -var_to_eliminate in cl for cl in clauses):
                    break # var_to_eliminate got eliminated by propagation

            # 2. Pure Literal Rule
            current_vars_in_formula = set(abs(lit) for cl in clauses for lit in cl)
            pure_literal_val = None
            for current_var_check in current_vars_in_formula:
                is_pos = any(current_var_check in c for c in clauses)
                is_neg = any(-current_var_check in c for c in clauses)

                if is_pos and not is_neg:
                    pure_literal_val = current_var_check
                    break
                if is_neg and not is_pos:
                    pure_literal_val = -current_var_check
                    break
            
            if pure_literal_val:
                clauses_after_simplify, conflict = _dp_simplify_clauses(clauses, pure_literal_val)
                if conflict: return False 
                if not clauses_after_simplify and not any(c for c in clauses_after_simplify if c):
                     return True
                if clauses_after_simplify != clauses:
                    clauses = clauses_after_simplify
                    made_change_in_iteration = True
                if not any(var_to_eliminate in cl or -var_to_eliminate in cl for cl in clauses):
                    break 
            
            if not made_change_in_iteration:
                break # No changes from unit prop or pure lit in this pass

        # Check if var_to_eliminate is still in the formula
        var_present_in_formula = any(var_to_eliminate in cl or -var_to_eliminate in cl for cl in clauses)
        if not var_present_in_formula:
            if not clauses and not any(c for c in clauses if c): return True # All clauses satisfied
            continue # Variable already eliminated by previous steps

        if not clauses and not any(c for c in clauses if c): return True


        # 3. Eliminate 'var_to_eliminate' by Resolution
        clauses_with_pos_var = [c for c in clauses if var_to_eliminate in c]
        clauses_with_neg_var = [c for c in clauses if -var_to_eliminate in c]
        clauses_without_var = [c for c in clauses if var_to_eliminate not in c and -var_to_eliminate not in c]

        # If var_to_eliminate is now pure (only appears in one polarity), its clauses are effectively removed.
        # This should have been handled by pure literal rule, but as a safeguard:
        if not clauses_with_pos_var or not clauses_with_neg_var:
            clauses = clauses_without_var # All clauses with var_to_eliminate are removed
            if any(not c for c in clauses): return False # Empty clause resulted
            if not clauses and not any(c for c in clauses if c): return True
            continue

        new_resolvents_for_var = set() 
        for c1 in clauses_with_pos_var:
            for c2 in clauses_with_neg_var:
                resolvent = (c1 - {var_to_eliminate}) | (c2 - {-var_to_eliminate})
                
                is_tautology = any(lit_r in resolvent and -lit_r in resolvent for lit_r in resolvent)
                if is_tautology:
                    continue

                if not resolvent: 
                    return False 
                new_resolvents_for_var.add(frozenset(resolvent))

        clauses = clauses_without_var + [set(r) for r in new_resolvents_for_var]
        
        if any(not c for c in clauses): 
            return False
        if not clauses and not any(c for c in clauses if c): 
            return True
            
    if any(not c for c in clauses):
        return False
    return True

if __name__ == '__main__':
    # --- Test Cases ---
    # Example 1: (x1 V -x2) & (x2 V x3)
    clauses1 = [[1, -2], [2, 3]]
    print(f"Clauses 1: {clauses1}")
    print(f"DP Original: {'SAT' if dp_original_solver(clauses1) else 'UNSAT'}")
    print("-" * 20)

    # Example 2: (x1) & (-x1)
    clauses2 = [[1], [-1]]
    print(f"Clauses 2: {clauses2}")
    print(f"DP Original: {'SAT' if dp_original_solver(clauses2) else 'UNSAT'}")
    print("-" * 20)

    # Example 3: (x1 V x2) & (-x1 V x2) & (x1 V -x2) & (-x1 V -x2)
    clauses3 = [[1, 2], [-1, 2], [1, -2], [-1, -2]]
    print(f"Clauses 3: {clauses3}")
    print(f"DP Original: {'SAT' if dp_original_solver(clauses3) else 'UNSAT'}")
    print("-" * 20)

    # Example 4: Empty clauses (satisfiable)
    clauses4 = []
    print(f"Clauses 4: {clauses4}")
    print(f"DP Original: {'SAT' if dp_original_solver(clauses4) else 'UNSAT'}")
    print("-" * 20)
    
    # Example 5: Formula with an empty clause (unsatisfiable)
    clauses5 = [[1,2], []]
    print(f"Clauses 5: {clauses5}")
    print(f"DP Original: {'SAT' if dp_original_solver(clauses5) else 'UNSAT'}")
    print("-" * 20)

    # Example 6: (A v B) & (A v ¬B)  => A
    clauses6 = [[1,2], [1,-2]]
    print(f"Clauses 6: {clauses6}")
    print(f"DP Original: {'SAT' if dp_original_solver(clauses6) else 'UNSAT'}") 
    print("-" * 20)

    # Example 7: Pigeonhole Principle PHP(2,1)-like (2 pigeons, 1 hole) - UNSAT
    clauses7 = [[1], [2], [-1, -2]] 
    print(f"Clauses 7: {clauses7}")
    print(f"DP Original: {'SAT' if dp_original_solver(clauses7) else 'UNSAT'}")
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
    print(f"DP Original: {'SAT' if dp_original_solver(clauses8) else 'UNSAT'}")
    print("-" * 20)

    end_time = time.time()
    _, peak_memory = tracemalloc.get_traced_memory()
    tracemalloc.stop()

    print(f"DP - Execution Time: {end_time - start_time:.10f} seconds")
    print(f"DP - Peak Memory Usage: {peak_memory / (1024 * 1024):.10f} MB")
    print("=" * 50)

