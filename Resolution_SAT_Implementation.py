import time
import tracemalloc

tracemalloc.start()
start_time = time.time()

def to_frozenset_clauses(clauses_list_of_lists):
    """Converts a list of lists of literals to a set of frozensets of literals."""
    if not clauses_list_of_lists: # Handles empty list of clauses (satisfiable)
        return set()
    return {frozenset(clause) for clause in clauses_list_of_lists}

def resolve_two_clauses(c1, c2):
    """
    Attempts to resolve two clauses c1 and c2.
    Returns a set of all possible unique resolvents.
    A resolvent is formed if one clause contains a literal L
    and the other contains -L. The resolvent is (c1 - {L}) U (c2 - {-L}).
    Tautologies (clauses containing both X and -X) are excluded from resolvents.
    """
    resolvents = set()
    for lit1 in c1:
        if -lit1 in c2:
            # Potential resolvent
            temp_resolvent = (c1 - {lit1}) | (c2 - {-lit1})
            
            # Check for tautology in the resolvent
            is_tautology = False
            for lit_r in temp_resolvent:
                if -lit_r in temp_resolvent:
                    is_tautology = True
                    break
            if not is_tautology:
                resolvents.add(temp_resolvent)
    return resolvents

def resolution_solver(clauses_input):
    """
    Solves SAT using the Resolution algorithm.
    Input: A list of lists of integers representing CNF clauses.
    Output: True if satisfiable, False if unsatisfiable.
    """
    if not clauses_input:
        return True # Empty set of clauses is satisfiable

    clauses = to_frozenset_clauses(clauses_input)

    if frozenset() in clauses: # Contains an empty clause initially
        return False

    # Using a list for new_clauses_this_round and checking against the main set 'clauses'
    # is generally more robust than relying on processed_pairs for termination in basic resolution.
    # The loop terminates when no new clauses can be added to the main 'clauses' set.
    while True:
        newly_derived_this_iteration = set()
        clauses_list = list(clauses) # For pairing
        
        for i in range(len(clauses_list)):
            for j in range(i + 1, len(clauses_list)):
                c1 = clauses_list[i]
                c2 = clauses_list[j]
                
                resolvents_from_pair = resolve_two_clauses(c1, c2)
                
                for r in resolvents_from_pair:
                    if not r: # Empty clause derived
                        return False # Unsatisfiable
                    # Add only if it's truly new and not already in the main clauses set
                    if r not in clauses:
                        newly_derived_this_iteration.add(r)

        if not newly_derived_this_iteration:
            # No new clauses were generated that were not already present
            return True # Satisfiable (empty clause not found)
        
        # Add all genuinely new clauses to the main set
        clauses.update(newly_derived_this_iteration)

if __name__ == '__main__':
    # --- Test Cases ---
    # Example 1: 
    clauses1 = [[1, -2], [2, 3]]
    print(f"Clauses 1: {clauses1}")
    print(f"Resolution: {'SAT' if resolution_solver(clauses1) else 'UNSAT'}")
    print("-" * 20)

    # Example 2:
    clauses2 = [[1], [-1]]
    print(f"Clauses 2: {clauses2}")
    print(f"Resolution: {'SAT' if resolution_solver(clauses2) else 'UNSAT'}")
    print("-" * 20)

    # Example 3: 
    clauses3 = [[1, 2], [-1, 2], [1, -2], [-1, -2]]
    print(f"Clauses 3: {clauses3}")
    print(f"Resolution: {'SAT' if resolution_solver(clauses3) else 'UNSAT'}")
    print("-" * 20)

    # Example 4: 
    clauses4 = []
    print(f"Clauses 4: {clauses4}")
    print(f"Resolution: {'SAT' if resolution_solver(clauses4) else 'UNSAT'}")
    print("-" * 20)
    
    # Example 5: 
    clauses5 = [[1,2], []]
    print(f"Clauses 5: {clauses5}")
    print(f"Resolution: {'SAT' if resolution_solver(clauses5) else 'UNSAT'}")
    print("-" * 20)

    # Example 6: 
    clauses6 = [[1,2], [1,-2]]
    print(f"Clauses 6: {clauses6}")
    print(f"Resolution: {'SAT' if resolution_solver(clauses6) else 'UNSAT'}") 
    print("-" * 20)

    # Example 7:
    clauses7 = [[1], [2], [-1, -2]] 
    print(f"Clauses 7: {clauses7}")
    print(f"Resolution: {'SAT' if resolution_solver(clauses7) else 'UNSAT'}")
    print("-" * 20)

    # Example 8:
    clauses8 = []
    for i in range(1, 6): # Pigeons 1 to 5
        clauses8.append([2*i - 1, 2*i])

    for i in range(1, 6):
        clauses8.append([-(2*i - 1), -(2*i)])

    hole1_vars = [2*i - 1 for i in range(1, 6)] 
    for i in range(len(hole1_vars)):
        for j in range(i + 1, len(hole1_vars)):
            clauses8.append([-hole1_vars[i], -hole1_vars[j]])
            
    print(f"Clauses 8: {clauses8}")
    print(f"Resolution: {'SAT' if resolution_solver(clauses8) else 'UNSAT'}")
    print("-" * 20)
    
    end_time = time.time()
    _, peak_memory = tracemalloc.get_traced_memory()
    tracemalloc.stop()

    print(f"Resolution - Execution Time: {end_time - start_time:.10f} seconds")
    print(f"Resolution - Peak Memory Usage: {peak_memory / (1024 * 1024):.10f} MB")
    print("=" * 50)
