from typing import Dict, List, Tuple, Any, Optional
from ssa import *
from smt import check_assertion, check_equivalence

def verify_program(ssa: SSAProgram) -> Tuple[bool, List[Dict[str, Any]], List[Dict[str, Any]]]:
    """
    Verify the correctness of a program by checking if all assertions hold.
    
    Args:
        ssa: The SSA program to verify
        
    Returns:
        Tuple of (result, examples, counterexamples) where:
        - result is a boolean indicating if all assertions hold
        - examples is a list of dictionaries mapping variable names to values that satisfy the assertions
        - counterexamples is a list of dictionaries mapping variable names to values that violate the assertions
    """
    return check_assertion(ssa)

def check_program_equivalence(ssa1: SSAProgram, ssa2: SSAProgram) -> Tuple[bool, List[Dict[str, Any]], List[Dict[str, Tuple[Any, Any]]]]:
    """
    Check if two programs are semantically equivalent.
    
    Args:
        ssa1: The first SSA program
        ssa2: The second SSA program
        
    Returns:
        Tuple of (result, examples, counterexamples) where:
        - result is a boolean indicating if the programs are equivalent
        - examples is a list of dictionaries mapping variable names to values where both programs produce the same output
        - counterexamples is a list of dictionaries mapping variable names to (value1, value2) tuples
          where the programs produce different outputs
    """
    return check_equivalence(ssa1, ssa2)
