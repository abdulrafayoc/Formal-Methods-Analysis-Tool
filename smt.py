from typing import Dict, List, Tuple, Any, Optional, Set
from ssa import *
from z3 import *
import re

def generate_smt(ssa: SSAProgram, second_ssa: Optional[SSAProgram] = None) -> str:
    """
    Generate SMT constraints for a single program or to check equivalence between two programs.
    
    Args:
        ssa: The first SSA program
        second_ssa: Optional second SSA program for equivalence checking
        
    Returns:
        String representation of the SMT constraints
    """
    if second_ssa is None:
        return generate_verification_smt(ssa)
    else:
        return generate_equivalence_smt(ssa, second_ssa)

def generate_verification_smt(ssa: SSAProgram) -> str:
    """
    Generate SMT constraints for program verification.
    
    Args:
        ssa: The SSA program to verify
        
    Returns:
        String representation of the SMT constraints
    """
    # Initialize Z3 solver
    solver = Solver()
    
    # Keep track of variable declarations
    variables = {}
    assertions = []
    
    # Helper function to convert SSA nodes to Z3 expressions
    def convert_expr(node: SSANode) -> z3.ExprRef:
        if isinstance(node, SSAVariable):
            var_name = f"{node.name}_{node.version}"
            if var_name not in variables:
                variables[var_name] = Int(var_name)
            return variables[var_name]
        
        elif isinstance(node, SSAConstant):
            if isinstance(node.value, bool):
                return BoolVal(node.value)
            return IntVal(node.value)
        
        elif isinstance(node, SSABinaryOp):
            left = convert_expr(node.left)
            right = convert_expr(node.right)
            
            if node.op == '+':
                return left + right
            elif node.op == '-':
                return left - right
            elif node.op == '*':
                return left * right
            elif node.op == '/':
                return left / right
            elif node.op == '%':
                return left % right
            elif node.op == '==':
                return left == right
            elif node.op == '!=':
                return left != right
            elif node.op == '<':
                return left < right
            elif node.op == '>':
                return left > right
            elif node.op == '<=':
                return left <= right
            elif node.op == '>=':
                return left >= right
            elif node.op == 'and':
                return And(left, right)
            elif node.op == 'or':
                return Or(left, right)
            else:
                raise ValueError(f"Unknown binary operator: {node.op}")
        
        elif isinstance(node, SSAUnaryOp):
            expr = convert_expr(node.expr)
            
            if node.op == '-':
                return -expr
            elif node.op == 'not':
                return Not(expr)
            else:
                raise ValueError(f"Unknown unary operator: {node.op}")
        
        elif isinstance(node, SSAPhiFunction):
            # Φ functions are handled when processing statements
            var_name = f"{node.name}_{node.version}"
            if var_name not in variables:
                variables[var_name] = Int(var_name)
            return variables[var_name]
        
        else:
            raise ValueError(f"Unknown expression type: {type(node)}")
    
    # Helper function to process SSA statements
    def process_statement(stmt: SSANode):
        if isinstance(stmt, SSAVarDecl) or isinstance(stmt, SSAAssignment):
            var_name = f"{stmt.name}_{stmt.version}"
            if var_name not in variables:
                variables[var_name] = Int(var_name)
            
            value = convert_expr(stmt.value)
            solver.add(variables[var_name] == value)
        
        elif isinstance(stmt, SSAPhiFunction):
            var_name = f"{stmt.name}_{stmt.version}"
            if var_name not in variables:
                variables[var_name] = Int(var_name)
            
            # Add constraints for possible values
            source_exprs = []
            for source_name, source_version in stmt.sources:
                source_var_name = f"{source_name}_{source_version}"
                if source_var_name not in variables:
                    variables[source_var_name] = Int(source_var_name)
                source_exprs.append(variables[var_name] == variables[source_var_name])
            
            if source_exprs:
                solver.add(Or(source_exprs))
        
        elif isinstance(stmt, SSAAssert):
            assertion = convert_expr(stmt.condition)
            assertions.append(assertion)
        
        elif isinstance(stmt, SSAIf):
            condition = convert_expr(stmt.condition)
            
            # Process all true branch statements
            for true_stmt in stmt.true_branch:
                process_statement(true_stmt)
            
            # Process all false branch statements if they exist
            if stmt.false_branch:
                for false_stmt in stmt.false_branch:
                    process_statement(false_stmt)
            
            # Process phi functions
            for phi in stmt.phi_functions:
                process_statement(phi)
        
        elif isinstance(stmt, SSAWhile):
            # Process the condition
            condition = convert_expr(stmt.condition)
            
            # Process the body statements
            for body_stmt in stmt.body:
                process_statement(body_stmt)
            
            # Process phi functions
            for phi in stmt.phi_functions:
                process_statement(phi)
    
    # Process all statements in the program
    for stmt in ssa.statements:
        process_statement(stmt)
    
    # Generate SMT code as a string
    smt_code = "(declare-const " + " Int)\n(declare-const ".join(variables.keys()) + " Int)\n\n"
    
    # Add constraints
    for constraint in solver.assertions():
        smt_code += f"(assert {constraint})\n"
    
    # Add assertions if they exist
    for assertion in assertions:
        smt_code += f"(assert {assertion})\n"
    
    smt_code += "\n(check-sat)\n(get-model)"
    
    return smt_code

def generate_equivalence_smt(ssa1: SSAProgram, ssa2: SSAProgram) -> str:
    """
    Generate SMT constraints for checking equivalence between two programs.
    
    Args:
        ssa1: The first SSA program
        ssa2: The second SSA program
        
    Returns:
        String representation of the SMT constraints
    """
    # Initialize Z3 solver
    solver = Solver()
    
    # Rename variables in the second program to avoid conflicts
    variables1 = {}  # Maps variable names to Z3 variables for program 1
    variables2 = {}  # Maps variable names to Z3 variables for program 2
    
    # Find all output variables (those with the highest version number)
    output_vars1 = set()
    output_vars2 = set()
    
    # Helper function to convert SSA nodes to Z3 expressions
    def convert_expr(node: SSANode, program_idx: int) -> z3.ExprRef:
        variables_map = variables1 if program_idx == 1 else variables2
        
        if isinstance(node, SSAVariable):
            var_name = f"{node.name}_{node.version}"
            if program_idx == 2:
                var_name = f"p2_{var_name}"  # Rename variables in the second program
            
            if var_name not in variables_map:
                variables_map[var_name] = Int(var_name)
            return variables_map[var_name]
        
        elif isinstance(node, SSAConstant):
            if isinstance(node.value, bool):
                return BoolVal(node.value)
            return IntVal(node.value)
        
        elif isinstance(node, SSABinaryOp):
            left = convert_expr(node.left, program_idx)
            right = convert_expr(node.right, program_idx)
            
            if node.op == '+':
                return left + right
            elif node.op == '-':
                return left - right
            elif node.op == '*':
                return left * right
            elif node.op == '/':
                return left / right
            elif node.op == '%':
                return left % right
            elif node.op == '==':
                return left == right
            elif node.op == '!=':
                return left != right
            elif node.op == '<':
                return left < right
            elif node.op == '>':
                return left > right
            elif node.op == '<=':
                return left <= right
            elif node.op == '>=':
                return left >= right
            elif node.op == 'and':
                return And(left, right)
            elif node.op == 'or':
                return Or(left, right)
            else:
                raise ValueError(f"Unknown binary operator: {node.op}")
        
        elif isinstance(node, SSAUnaryOp):
            expr = convert_expr(node.expr, program_idx)
            
            if node.op == '-':
                return -expr
            elif node.op == 'not':
                return Not(expr)
            else:
                raise ValueError(f"Unknown unary operator: {node.op}")
        
        elif isinstance(node, SSAPhiFunction):
            var_name = f"{node.name}_{node.version}"
            if program_idx == 2:
                var_name = f"p2_{var_name}"
            
            if var_name not in variables_map:
                variables_map[var_name] = Int(var_name)
            return variables_map[var_name]
        
        else:
            raise ValueError(f"Unknown expression type: {type(node)}")
    
    # Helper function to process SSA statements
    def process_statement(stmt: SSANode, program_idx: int, output_vars: Set[str]):
        variables_map = variables1 if program_idx == 1 else variables2
        prefix = "" if program_idx == 1 else "p2_"
        
        if isinstance(stmt, SSAVarDecl) or isinstance(stmt, SSAAssignment):
            var_name = f"{prefix}{stmt.name}_{stmt.version}"
            if var_name not in variables_map:
                variables_map[var_name] = Int(var_name)
            
            value = convert_expr(stmt.value, program_idx)
            solver.add(variables_map[var_name] == value)
            
            # Track output variables (those not used as inputs to other operations)
            output_vars.add(stmt.name)
        
        elif isinstance(stmt, SSAPhiFunction):
            var_name = f"{prefix}{stmt.name}_{stmt.version}"
            if var_name not in variables_map:
                variables_map[var_name] = Int(var_name)
            
            # Add constraints for possible values
            source_exprs = []
            for source_name, source_version in stmt.sources:
                source_var_name = f"{prefix}{source_name}_{source_version}"
                if source_var_name not in variables_map:
                    variables_map[source_var_name] = Int(source_var_name)
                source_exprs.append(variables_map[var_name] == variables_map[source_var_name])
            
            if source_exprs:
                solver.add(Or(source_exprs))
            
            # Track output variables
            output_vars.add(stmt.name)
        
        elif isinstance(stmt, SSAAssert):
            assertion = convert_expr(stmt.condition, program_idx)
            solver.add(assertion)
        
        elif isinstance(stmt, SSAIf):
            condition = convert_expr(stmt.condition, program_idx)
            
            # Process all true branch statements
            for true_stmt in stmt.true_branch:
                process_statement(true_stmt, program_idx, output_vars)
            
            # Process all false branch statements if they exist
            if stmt.false_branch:
                for false_stmt in stmt.false_branch:
                    process_statement(false_stmt, program_idx, output_vars)
            
            # Process phi functions
            for phi in stmt.phi_functions:
                process_statement(phi, program_idx, output_vars)
        
        elif isinstance(stmt, SSAWhile):
            # Process the condition
            condition = convert_expr(stmt.condition, program_idx)
            
            # Process the body statements
            for body_stmt in stmt.body:
                process_statement(body_stmt, program_idx, output_vars)
            
            # Process phi functions
            for phi in stmt.phi_functions:
                process_statement(phi, program_idx, output_vars)
    
    # Process all statements in both programs
    for stmt in ssa1.statements:
        process_statement(stmt, 1, output_vars1)
    
    for stmt in ssa2.statements:
        process_statement(stmt, 2, output_vars2)
    
    # Add equivalence constraints for common output variables
    common_outputs = output_vars1.intersection(output_vars2)
    equivalence_constraints = []
    
    for var_name in common_outputs:
        # Find the highest version for each variable
        var1_highest = max([int(m.group(1)) for m in [re.match(f"{var_name}_(\\d+)$", v) for v in variables1.keys()] if m], default=0)
        var2_highest = max([int(m.group(1)) for m in [re.match(f"p2_{var_name}_(\\d+)$", v) for v in variables2.keys()] if m], default=0)
        
        if var1_highest > 0 and var2_highest > 0:
            var1_name = f"{var_name}_{var1_highest}"
            var2_name = f"p2_{var_name}_{var2_highest}"
            
            equivalence_constraints.append(variables1[var1_name] == variables2[var2_name])
    
    # Generate SMT code as a string
    smt_code = ";;; Program 1 variables\n"
    smt_code += "(declare-const " + " Int)\n(declare-const ".join(variables1.keys()) + " Int)\n\n"
    
    smt_code += ";;; Program 2 variables\n"
    smt_code += "(declare-const " + " Int)\n(declare-const ".join(variables2.keys()) + " Int)\n\n"
    
    smt_code += ";;; Program 1 constraints\n"
    for constraint in solver.assertions():
        smt_code += f"(assert {constraint})\n"
    
    smt_code += "\n;;; Equivalence constraints\n"
    for constraint in equivalence_constraints:
        smt_code += f"(assert (not {constraint}))\n"
    
    smt_code += "\n(check-sat)\n(get-model)"
    
    return smt_code

def check_assertion(ssa: SSAProgram) -> Tuple[bool, List[Dict[str, Any]], List[Dict[str, Any]]]:
    """
    Check if all assertions in the program hold.
    
    Args:
        ssa: The SSA program to check
        
    Returns:
        Tuple of (result, examples, counterexamples) where:
        - result is a boolean indicating if all assertions hold
        - examples is a list of dictionaries mapping variable names to values that satisfy the assertions
        - counterexamples is a list of dictionaries mapping variable names to values that violate the assertions
    """
    # Initialize Z3 solver
    solver = Solver()
    
    # Keep track of variable declarations and assertions
    variables = {}
    assertions = []
    
    # Helper function to convert SSA nodes to Z3 expressions
    def convert_expr(node: SSANode) -> z3.ExprRef:
        if isinstance(node, SSAVariable):
            var_name = f"{node.name}_{node.version}"
            if var_name not in variables:
                variables[var_name] = Int(var_name)
            return variables[var_name]
        
        elif isinstance(node, SSAConstant):
            if isinstance(node.value, bool):
                return BoolVal(node.value)
            return IntVal(node.value)
        
        elif isinstance(node, SSABinaryOp):
            left = convert_expr(node.left)
            right = convert_expr(node.right)
            
            if node.op == '+':
                return left + right
            elif node.op == '-':
                return left - right
            elif node.op == '*':
                return left * right
            elif node.op == '/':
                return left / right
            elif node.op == '%':
                return left % right
            elif node.op == '==':
                return left == right
            elif node.op == '!=':
                return left != right
            elif node.op == '<':
                return left < right
            elif node.op == '>':
                return left > right
            elif node.op == '<=':
                return left <= right
            elif node.op == '>=':
                return left >= right
            elif node.op == 'and':
                return And(left, right)
            elif node.op == 'or':
                return Or(left, right)
            else:
                raise ValueError(f"Unknown binary operator: {node.op}")
        
        elif isinstance(node, SSAUnaryOp):
            expr = convert_expr(node.expr)
            
            if node.op == '-':
                return -expr
            elif node.op == 'not':
                return Not(expr)
            else:
                raise ValueError(f"Unknown unary operator: {node.op}")
        
        else:
            raise ValueError(f"Unknown expression type: {type(node)}")
    
    # Helper function to process SSA statements
    def process_statement(stmt: SSANode):
        if isinstance(stmt, SSAVarDecl) or isinstance(stmt, SSAAssignment):
            var_name = f"{stmt.name}_{stmt.version}"
            if var_name not in variables:
                variables[var_name] = Int(var_name)
            
            value = convert_expr(stmt.value)
            solver.add(variables[var_name] == value)
        
        elif isinstance(stmt, SSAPhiFunction):
            var_name = f"{stmt.name}_{stmt.version}"
            if var_name not in variables:
                variables[var_name] = Int(var_name)
            
            # Add constraints for possible values
            source_exprs = []
            for source_name, source_version in stmt.sources:
                source_var_name = f"{source_name}_{source_version}"
                if source_var_name not in variables:
                    variables[source_var_name] = Int(source_var_name)
                source_exprs.append(variables[var_name] == variables[source_var_name])
            
            if source_exprs:
                solver.add(Or(source_exprs))
        
        elif isinstance(stmt, SSAAssert):
            assertion = convert_expr(stmt.condition)
            assertions.append(assertion)
        
        elif isinstance(stmt, SSAIf):
            condition = convert_expr(stmt.condition)
            
            # Process all true branch statements
            for true_stmt in stmt.true_branch:
                process_statement(true_stmt)
            
            # Process all false branch statements if they exist
            if stmt.false_branch:
                for false_stmt in stmt.false_branch:
                    process_statement(false_stmt)
            
            # Process phi functions
            for phi in stmt.phi_functions:
                process_statement(phi)
        
        elif isinstance(stmt, SSAWhile):
            # Process the condition
            condition = convert_expr(stmt.condition)
            
            # Process the body statements
            for body_stmt in stmt.body:
                process_statement(body_stmt)
            
            # Process phi functions
            for phi in stmt.phi_functions:
                process_statement(phi)
    
    # Process all statements in the program
    for stmt in ssa.statements:
        process_statement(stmt)
    
    # Check if all assertions hold
    examples = []
    counterexamples = []
    
    # First, check if the program constraints are satisfiable
    if solver.check() == sat:
        model = solver.model()
        example = {}
        
        # Extract variable values from the model
        for var_name, var in variables.items():
            if model[var] is not None:
                # Extract the base variable name (without version)
                base_name = var_name.split('_')[0]
                value = model[var].as_long() if model[var].sort().kind() == Z3_INT_SORT else model[var]
                example[base_name] = value
        
        examples.append(example)
        
        # Check if any assertion fails
        for assertion in assertions:
            # Create a new solver to check the negation of each assertion
            assertion_solver = Solver()
            
            # Add program constraints
            for constraint in solver.assertions():
                assertion_solver.add(constraint)
            
            # Add negation of the assertion
            assertion_solver.add(Not(assertion))
            
            # Check if there's a counterexample
            if assertion_solver.check() == sat:
                model = assertion_solver.model()
                counterexample = {}
                
                # Extract variable values from the model
                for var_name, var in variables.items():
                    if model[var] is not None:
                        # Extract the base variable name (without version)
                        base_name = var_name.split('_')[0]
                        value = model[var].as_long() if model[var].sort().kind() == Z3_INT_SORT else model[var]
                        counterexample[base_name] = value
                
                counterexamples.append(counterexample)
        
        # Get one more counterexample if possible
        if len(counterexamples) == 1:
            # Add a constraint to exclude the first counterexample
            constraint = False
            for var_name, var in variables.items():
                base_name = var_name.split('_')[0]
                if base_name in counterexamples[0]:
                    constraint = Or(constraint, var != IntVal(counterexamples[0][base_name]))
            
            assertion_solver.add(constraint)
            
            # Check for a second counterexample
            if assertion_solver.check() == sat:
                model = assertion_solver.model()
                counterexample = {}
                
                # Extract variable values from the model
                for var_name, var in variables.items():
                    if model[var] is not None:
                        # Extract the base variable name (without version)
                        base_name = var_name.split('_')[0]
                        value = model[var].as_long() if model[var].sort().kind() == Z3_INT_SORT else model[var]
                        counterexample[base_name] = value
                
                counterexamples.append(counterexample)
    
    return len(counterexamples) == 0, examples, counterexamples

def check_equivalence(ssa1: SSAProgram, ssa2: SSAProgram) -> Tuple[bool, List[Dict[str, Any]], List[Dict[str, Tuple[Any, Any]]]]:
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
    # Initialize Z3 solver
    solver = Solver()
    
    # Rename variables in the second program to avoid conflicts
    variables1 = {}  # Maps variable names to Z3 variables for program 1
    variables2 = {}  # Maps variable names to Z3 variables for program 2
    
    # Find all output variables (final versions of each variable)
    output_vars1 = {}  # name -> highest version
    output_vars2 = {}  # name -> highest version
    
    # Helper function to convert SSA nodes to Z3 expressions
    def convert_expr(node: SSANode, program_idx: int) -> z3.ExprRef:
        variables_map = variables1 if program_idx == 1 else variables2
        
        if isinstance(node, SSAVariable):
            var_name = f"{node.name}_{node.version}"
            if program_idx == 2:
                var_name = f"p2_{var_name}"  # Rename variables in the second program
            
            if var_name not in variables_map:
                variables_map[var_name] = Int(var_name)
            return variables_map[var_name]
        
        elif isinstance(node, SSAConstant):
            if isinstance(node.value, bool):
                return BoolVal(node.value)
            return IntVal(node.value)
        
        elif isinstance(node, SSABinaryOp):
            left = convert_expr(node.left, program_idx)
            right = convert_expr(node.right, program_idx)
            
            if node.op == '+':
                return left + right
            elif node.op == '-':
                return left - right
            elif node.op == '*':
                return left * right
            elif node.op == '/':
                return left / right
            elif node.op == '%':
                return left % right
            elif node.op == '==':
                return left == right
            elif node.op == '!=':
                return left != right
            elif node.op == '<':
                return left < right
            elif node.op == '>':
                return left > right
            elif node.op == '<=':
                return left <= right
            elif node.op == '>=':
                return left >= right
            elif node.op == 'and':
                return And(left, right)
            elif node.op == 'or':
                return Or(left, right)
            else:
                raise ValueError(f"Unknown binary operator: {node.op}")
        
        elif isinstance(node, SSAUnaryOp):
            expr = convert_expr(node.expr, program_idx)
            
            if node.op == '-':
                return -expr
            elif node.op == 'not':
                return Not(expr)
            else:
                raise ValueError(f"Unknown unary operator: {node.op}")
        
        else:
            raise ValueError(f"Unknown expression type: {type(node)}")
    
    # Helper function to track variables and their assignments
    def track_variable(name: str, version: int, program_idx: int):
        var_map = output_vars1 if program_idx == 1 else output_vars2
        
        # Update to the highest version seen
        if name not in var_map or version > var_map[name]:
            var_map[name] = version
    
    # Helper function to process SSA statements
    def process_statement(stmt: SSANode, program_idx: int):
        variables_map = variables1 if program_idx == 1 else variables2
        prefix = "" if program_idx == 1 else "p2_"
        
        if isinstance(stmt, SSAVarDecl) or isinstance(stmt, SSAAssignment):
            var_name = f"{prefix}{stmt.name}_{stmt.version}"
            if var_name not in variables_map:
                variables_map[var_name] = Int(var_name)
            
            value = convert_expr(stmt.value, program_idx)
            solver.add(variables_map[var_name] == value)
            
            # Track highest version for each variable
            track_variable(stmt.name, stmt.version, program_idx)
        
        elif isinstance(stmt, SSAPhiFunction):
            var_name = f"{prefix}{stmt.name}_{stmt.version}"
            if var_name not in variables_map:
                variables_map[var_name] = Int(var_name)
            
            # Add constraints for possible values
            source_exprs = []
            for source_name, source_version in stmt.sources:
                source_var_name = f"{prefix}{source_name}_{source_version}"
                if source_var_name not in variables_map:
                    variables_map[source_var_name] = Int(source_var_name)
                source_exprs.append(variables_map[var_name] == variables_map[source_var_name])
            
            if source_exprs:
                solver.add(Or(source_exprs))
            
            # Track highest version
            track_variable(stmt.name, stmt.version, program_idx)
        
        elif isinstance(stmt, SSAAssert):
            assertion = convert_expr(stmt.condition, program_idx)
            solver.add(assertion)
        
        elif isinstance(stmt, SSAIf):
            condition = convert_expr(stmt.condition, program_idx)
            
            # Process all true branch statements
            for true_stmt in stmt.true_branch:
                process_statement(true_stmt, program_idx)
            
            # Process all false branch statements if they exist
            if stmt.false_branch:
                for false_stmt in stmt.false_branch:
                    process_statement(false_stmt, program_idx)
            
            # Process phi functions
            for phi in stmt.phi_functions:
                process_statement(phi, program_idx)
        
        elif isinstance(stmt, SSAWhile):
            # Process the condition
            condition = convert_expr(stmt.condition, program_idx)
            
            # Process the body statements
            for body_stmt in stmt.body:
                process_statement(body_stmt, program_idx)
            
            # Process phi functions
            for phi in stmt.phi_functions:
                process_statement(phi, program_idx)
    
    # Process all statements in both programs
    for stmt in ssa1.statements:
        process_statement(stmt, 1)
    
    for stmt in ssa2.statements:
        process_statement(stmt, 2)
    
    # Find common output variables
    common_outputs = set(output_vars1.keys()).intersection(set(output_vars2.keys()))
    
    # Create equivalence constraints
    equivalence_constraints = []
    for var_name in common_outputs:
        version1 = output_vars1[var_name]
        version2 = output_vars2[var_name]
        
        var1 = variables1[f"{var_name}_{version1}"]
        var2 = variables2[f"p2_{var_name}_{version2}"]
        
        # Create constraint that outputs must be equal
        equivalence_constraints.append(var1 == var2)
    
    # Check if the programs are equivalent
    examples = []
    counterexamples = []
    
    # First check if there's an example where both programs produce the same output
    if solver.check() == sat:
        model = solver.model()
        example = {}
        
        # Extract variable values from the model
        for var_name in common_outputs:
            version1 = output_vars1[var_name]
            var1 = variables1[f"{var_name}_{version1}"]
            
            if model[var1] is not None:
                value = model[var1].as_long() if model[var1].sort().kind() == Z3_INT_SORT else model[var1]
                example[var_name] = value
        
        examples.append(example)
        
        # Now check for counterexamples - cases where the outputs differ
        equivalence_solver = Solver()
        
        # Add program constraints
        for constraint in solver.assertions():
            equivalence_solver.add(constraint)
        
        # Add negation of equivalence constraints
        inequivalence_constraint = False
        for constraint in equivalence_constraints:
            inequivalence_constraint = Or(inequivalence_constraint, Not(constraint))
        
        equivalence_solver.add(inequivalence_constraint)
        
        # Check if there's a counterexample
        if equivalence_solver.check() == sat:
            model = equivalence_solver.model()
            counterexample = {}
            
            # Extract differing outputs
            for var_name in common_outputs:
                version1 = output_vars1[var_name]
                version2 = output_vars2[var_name]
                
                var1 = variables1[f"{var_name}_{version1}"]
                var2 = variables2[f"p2_{var_name}_{version2}"]
                
                if model[var1] is not None and model[var2] is not None:
                    value1 = model[var1].as_long() if model[var1].sort().kind() == Z3_INT_SORT else model[var1]
                    value2 = model[var2].as_long() if model[var2].sort().kind() == Z3_INT_SORT else model[var2]
                    
                    # Only include variables where the values differ
                    if value1 != value2:
                        counterexample[var_name] = (value1, value2)
            
            # Include input variables as well
            for var_name in variables1.keys():
                if '_0' in var_name:  # Initial values (inputs)
                    base_name = var_name.split('_')[0]
                    if base_name in common_outputs and model[variables1[var_name]] is not None:
                        value = model[variables1[var_name]].as_long() if model[variables1[var_name]].sort().kind() == Z3_INT_SORT else model[variables1[var_name]]
                        counterexample[base_name] = (value, value)  # Same input for both programs
            
            counterexamples.append(counterexample)
            
            # Try to get a second counterexample
            if counterexamples:
                # Add a constraint to exclude the first counterexample
                constraint = False
                for var_name, (val1, val2) in counterexamples[0].items():
                    if var_name in output_vars1 and var_name in output_vars2:
                        var1 = variables1[f"{var_name}_{output_vars1[var_name]}"]
                        var2 = variables2[f"p2_{var_name}_{output_vars2[var_name]}"]
                        constraint = Or(constraint, var1 != IntVal(val1), var2 != IntVal(val2))
                
                equivalence_solver.add(constraint)
                
                # Check for a second counterexample
                if equivalence_solver.check() == sat:
                    model = equivalence_solver.model()
                    counterexample = {}
                    
                    # Extract differing outputs
                    for var_name in common_outputs:
                        version1 = output_vars1[var_name]
                        version2 = output_vars2[var_name]
                        
                        var1 = variables1[f"{var_name}_{version1}"]
                        var2 = variables2[f"p2_{var_name}_{version2}"]
                        
                        if model[var1] is not None and model[var2] is not None:
                            value1 = model[var1].as_long() if model[var1].sort().kind() == Z3_INT_SORT else model[var1]
                            value2 = model[var2].as_long() if model[var2].sort().kind() == Z3_INT_SORT else model[var2]
                            
                            # Only include variables where the values differ
                            if value1 != value2:
                                counterexample[var_name] = (value1, value2)
                    
                    # Include input variables as well
                    for var_name in variables1.keys():
                        if '_0' in var_name:  # Initial values (inputs)
                            base_name = var_name.split('_')[0]
                            if base_name in common_outputs and model[variables1[var_name]] is not None:
                                value = model[variables1[var_name]].as_long() if model[variables1[var_name]].sort().kind() == Z3_INT_SORT else model[variables1[var_name]]
                                counterexample[base_name] = (value, value)  # Same input for both programs
                    
                    counterexamples.append(counterexample)
    
    return len(counterexamples) == 0, examples, counterexamples
