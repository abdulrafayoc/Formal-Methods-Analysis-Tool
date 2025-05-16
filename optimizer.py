from typing import Dict, List, Set, Tuple, Any
from ssa import *
import copy

def optimize_ssa(ssa: SSAProgram, optimizations: List[str]) -> SSAProgram:
    """
    Apply various optimizations to an SSA program.
    
    Args:
        ssa: The SSA program to optimize
        optimizations: List of optimization names to apply
        
    Returns:
        An optimized version of the SSA program
    """
    # Make a deep copy to avoid modifying the original
    optimized = copy.deepcopy(ssa)
    
    # Apply requested optimizations
    if "Constant Propagation" in optimizations:
        optimized = constant_propagation(optimized)
    
    if "Dead Code Elimination" in optimizations:
        optimized = dead_code_elimination(optimized)
    
    if "Common Subexpression Elimination" in optimizations:
        optimized = common_subexpression_elimination(optimized)
    
    return optimized

def constant_propagation(ssa: SSAProgram) -> SSAProgram:
    """
    Perform constant propagation on an SSA program.
    
    Args:
        ssa: The SSA program to optimize
        
    Returns:
        An SSA program with constants propagated
    """
    # Create a deep copy to avoid modifying the original
    optimized = copy.deepcopy(ssa)
    
    # Keep track of constant values
    constants = {}  # Maps variable names to their constant values
    
    # Helper function to propagate constants in expressions
    def propagate_in_expr(expr: SSANode) -> SSANode:
        if isinstance(expr, SSAVariable):
            var_name = f"{expr.name}_{expr.version}"
            if var_name in constants:
                return SSAConstant(constants[var_name])
            return expr
        
        elif isinstance(expr, SSAConstant):
            return expr
        
        elif isinstance(expr, SSABinaryOp):
            left = propagate_in_expr(expr.left)
            right = propagate_in_expr(expr.right)
            
            # If both operands are constants, compute the result
            if isinstance(left, SSAConstant) and isinstance(right, SSAConstant):
                if expr.op == '+':
                    return SSAConstant(left.value + right.value)
                elif expr.op == '-':
                    return SSAConstant(left.value - right.value)
                elif expr.op == '*':
                    return SSAConstant(left.value * right.value)
                elif expr.op == '/':
                    # Avoid division by zero
                    if right.value != 0:
                        return SSAConstant(left.value / right.value)
                elif expr.op == '%':
                    # Avoid modulo by zero
                    if right.value != 0:
                        return SSAConstant(left.value % right.value)
                elif expr.op == '==':
                    return SSAConstant(left.value == right.value)
                elif expr.op == '!=':
                    return SSAConstant(left.value != right.value)
                elif expr.op == '<':
                    return SSAConstant(left.value < right.value)
                elif expr.op == '>':
                    return SSAConstant(left.value > right.value)
                elif expr.op == '<=':
                    return SSAConstant(left.value <= right.value)
                elif expr.op == '>=':
                    return SSAConstant(left.value >= right.value)
                elif expr.op == 'and':
                    return SSAConstant(left.value and right.value)
                elif expr.op == 'or':
                    return SSAConstant(left.value or right.value)
            
            # If not both constants, return the binary op with propagated operands
            return SSABinaryOp(left, expr.op, right)
        
        elif isinstance(expr, SSAUnaryOp):
            inner = propagate_in_expr(expr.expr)
            
            # If the operand is a constant, compute the result
            if isinstance(inner, SSAConstant):
                if expr.op == '-':
                    return SSAConstant(-inner.value)
                elif expr.op == 'not':
                    return SSAConstant(not inner.value)
            
            # If not a constant, return the unary op with propagated operand
            return SSAUnaryOp(expr.op, inner)
        
        else:
            return expr
    
    # Helper function to propagate constants in statements
    def propagate_in_stmt(stmt: SSANode) -> SSANode:
        if isinstance(stmt, SSAVarDecl):
            propagated_value = propagate_in_expr(stmt.value)
            
            # If the value is a constant, record it
            if isinstance(propagated_value, SSAConstant):
                var_name = f"{stmt.name}_{stmt.version}"
                constants[var_name] = propagated_value.value
            
            return SSAVarDecl(stmt.name, stmt.version, propagated_value)
        
        elif isinstance(stmt, SSAAssignment):
            propagated_value = propagate_in_expr(stmt.value)
            
            # If the value is a constant, record it
            if isinstance(propagated_value, SSAConstant):
                var_name = f"{stmt.name}_{stmt.version}"
                constants[var_name] = propagated_value.value
            
            return SSAAssignment(stmt.name, stmt.version, propagated_value)
        
        elif isinstance(stmt, SSAPhiFunction):
            # Φ functions are harder to optimize - for now, just return as is
            return stmt
        
        elif isinstance(stmt, SSAAssert):
            return SSAAssert(propagate_in_expr(stmt.condition))
        
        elif isinstance(stmt, SSAIf):
            condition = propagate_in_expr(stmt.condition)
            
            # If condition is a constant, we can eliminate the branch
            if isinstance(condition, SSAConstant):
                if condition.value:
                    # Condition is always true, keep only the true branch
                    return [propagate_in_stmt(s) for s in stmt.true_branch]
                elif stmt.false_branch:
                    # Condition is always false, keep only the false branch
                    return [propagate_in_stmt(s) for s in stmt.false_branch]
                else:
                    # Condition is always false and no false branch, eliminate the if
                    return []
            
            # Otherwise, recursively propagate in both branches
            true_branch = [propagate_in_stmt(s) for s in stmt.true_branch]
            false_branch = [propagate_in_stmt(s) for s in stmt.false_branch] if stmt.false_branch else None
            phi_functions = [propagate_in_stmt(p) for p in stmt.phi_functions]
            
            return SSAIf(condition, true_branch, false_branch, phi_functions)
        
        elif isinstance(stmt, SSAWhile):
            condition = propagate_in_expr(stmt.condition)
            
            # If condition is a constant false, eliminate the loop
            if isinstance(condition, SSAConstant) and not condition.value:
                return []
            
            # Otherwise, recursively propagate in the body
            body = [propagate_in_stmt(s) for s in stmt.body]
            phi_functions = [propagate_in_stmt(p) for p in stmt.phi_functions]
            
            return SSAWhile(condition, body, phi_functions)
        
        else:
            return stmt
    
    # Propagate constants in all statements
    optimized_statements = []
    for stmt in optimized.statements:
        result = propagate_in_stmt(stmt)
        
        # Handle the case where propagate_in_stmt returns a list (from if elimination)
        if isinstance(result, list):
            optimized_statements.extend(result)
        else:
            optimized_statements.append(result)
    
    return SSAProgram(optimized_statements, optimized.var_versions)

def dead_code_elimination(ssa: SSAProgram) -> SSAProgram:
    """
    Eliminate dead code from an SSA program.
    
    Args:
        ssa: The SSA program to optimize
        
    Returns:
        An SSA program with dead code eliminated
    """
    # Create a deep copy to avoid modifying the original
    optimized = copy.deepcopy(ssa)
    
    # First, identify live variables - those that are used after definition
    used_vars = set()  # Set of (name, version) tuples
    
    # Helper function to find variables used in an expression
    def find_used_vars(expr: SSANode):
        if isinstance(expr, SSAVariable):
            used_vars.add((expr.name, expr.version))
        elif isinstance(expr, SSABinaryOp):
            find_used_vars(expr.left)
            find_used_vars(expr.right)
        elif isinstance(expr, SSAUnaryOp):
            find_used_vars(expr.expr)
    
    # First pass: find all used variables
    for stmt in optimized.statements:
        if isinstance(stmt, SSAVarDecl) or isinstance(stmt, SSAAssignment):
            find_used_vars(stmt.value)
        elif isinstance(stmt, SSAPhiFunction):
            for name, version in stmt.sources:
                used_vars.add((name, version))
        elif isinstance(stmt, SSAAssert):
            find_used_vars(stmt.condition)
        elif isinstance(stmt, SSAIf):
            find_used_vars(stmt.condition)
            for true_stmt in stmt.true_branch:
                if isinstance(true_stmt, SSAVarDecl) or isinstance(true_stmt, SSAAssignment):
                    find_used_vars(true_stmt.value)
                elif isinstance(true_stmt, SSAAssert):
                    find_used_vars(true_stmt.condition)
            
            if stmt.false_branch:
                for false_stmt in stmt.false_branch:
                    if isinstance(false_stmt, SSAVarDecl) or isinstance(false_stmt, SSAAssignment):
                        find_used_vars(false_stmt.value)
                    elif isinstance(false_stmt, SSAAssert):
                        find_used_vars(false_stmt.condition)
        
        elif isinstance(stmt, SSAWhile):
            find_used_vars(stmt.condition)
            for body_stmt in stmt.body:
                if isinstance(body_stmt, SSAVarDecl) or isinstance(body_stmt, SSAAssignment):
                    find_used_vars(body_stmt.value)
                elif isinstance(body_stmt, SSAAssert):
                    find_used_vars(body_stmt.condition)
    
    # Second pass: filter out dead code
    live_statements = []
    for stmt in optimized.statements:
        if isinstance(stmt, SSAVarDecl) or isinstance(stmt, SSAAssignment):
            if (stmt.name, stmt.version) in used_vars:
                live_statements.append(stmt)
        else:
            # Keep all other statements (asserts, control flow, etc.)
            live_statements.append(stmt)
    
    return SSAProgram(live_statements, optimized.var_versions)

def common_subexpression_elimination(ssa: SSAProgram) -> SSAProgram:
    """
    Eliminate common subexpressions from an SSA program.
    
    Args:
        ssa: The SSA program to optimize
        
    Returns:
        An SSA program with common subexpressions eliminated
    """
    # Create a deep copy to avoid modifying the original
    optimized = copy.deepcopy(ssa)
    
    # Maps expression representation to existing variable
    expr_to_var = {}  # Maps expression string representation to (name, version) tuple
    
    # Helper function to get a string representation of an expression
    def expr_to_string(expr: SSANode) -> str:
        if isinstance(expr, SSAVariable):
            return f"{expr.name}_{expr.version}"
        elif isinstance(expr, SSAConstant):
            return str(expr.value)
        elif isinstance(expr, SSABinaryOp):
            return f"({expr_to_string(expr.left)} {expr.op} {expr_to_string(expr.right)})"
        elif isinstance(expr, SSAUnaryOp):
            return f"{expr.op}({expr_to_string(expr.expr)})"
        else:
            return str(expr)
    
    # Helper function to eliminate common subexpressions in an expression
    def eliminate_cse_in_expr(expr: SSANode) -> SSANode:
        if isinstance(expr, SSAVariable) or isinstance(expr, SSAConstant):
            return expr
        
        if isinstance(expr, SSABinaryOp):
            expr.left = eliminate_cse_in_expr(expr.left)
            expr.right = eliminate_cse_in_expr(expr.right)
            
            # Check if this expression already exists
            expr_str = expr_to_string(expr)
            if expr_str in expr_to_var:
                name, version = expr_to_var[expr_str]
                return SSAVariable(name, version)
            
            return expr
        
        elif isinstance(expr, SSAUnaryOp):
            expr.expr = eliminate_cse_in_expr(expr.expr)
            
            # Check if this expression already exists
            expr_str = expr_to_string(expr)
            if expr_str in expr_to_var:
                name, version = expr_to_var[expr_str]
                return SSAVariable(name, version)
            
            return expr
        
        else:
            return expr
    
    # Process all statements to eliminate common subexpressions
    optimized_statements = []
    for stmt in optimized.statements:
        if isinstance(stmt, SSAVarDecl) or isinstance(stmt, SSAAssignment):
            # Eliminate CSEs in the right-hand side
            stmt.value = eliminate_cse_in_expr(stmt.value)
            
            # Record this assignment for future CSE
            expr_str = expr_to_string(stmt.value)
            expr_to_var[expr_str] = (stmt.name, stmt.version)
            
            optimized_statements.append(stmt)
        
        elif isinstance(stmt, SSAPhiFunction):
            # Φ functions involve control flow, so we conservatively keep them
            optimized_statements.append(stmt)
            
            # Record this phi for future CSE
            var_name = f"{stmt.name}_{stmt.version}"
            expr_to_var[var_name] = (stmt.name, stmt.version)
        
        elif isinstance(stmt, SSAAssert):
            stmt.condition = eliminate_cse_in_expr(stmt.condition)
            optimized_statements.append(stmt)
        
        elif isinstance(stmt, SSAIf):
            stmt.condition = eliminate_cse_in_expr(stmt.condition)
            
            # Process the true branch
            for i, true_stmt in enumerate(stmt.true_branch):
                if isinstance(true_stmt, SSAVarDecl) or isinstance(true_stmt, SSAAssignment):
                    true_stmt.value = eliminate_cse_in_expr(true_stmt.value)
                    # Don't record statements inside conditionals for global CSE
                elif isinstance(true_stmt, SSAAssert):
                    true_stmt.condition = eliminate_cse_in_expr(true_stmt.condition)
            
            # Process the false branch
            if stmt.false_branch:
                for i, false_stmt in enumerate(stmt.false_branch):
                    if isinstance(false_stmt, SSAVarDecl) or isinstance(false_stmt, SSAAssignment):
                        false_stmt.value = eliminate_cse_in_expr(false_stmt.value)
                        # Don't record statements inside conditionals for global CSE
                    elif isinstance(false_stmt, SSAAssert):
                        false_stmt.condition = eliminate_cse_in_expr(false_stmt.condition)
            
            optimized_statements.append(stmt)
        
        elif isinstance(stmt, SSAWhile):
            stmt.condition = eliminate_cse_in_expr(stmt.condition)
            
            # Process the body
            for i, body_stmt in enumerate(stmt.body):
                if isinstance(body_stmt, SSAVarDecl) or isinstance(body_stmt, SSAAssignment):
                    body_stmt.value = eliminate_cse_in_expr(body_stmt.value)
                    # Don't record statements inside loops for global CSE
                elif isinstance(body_stmt, SSAAssert):
                    body_stmt.condition = eliminate_cse_in_expr(body_stmt.condition)
            
            optimized_statements.append(stmt)
        
        else:
            optimized_statements.append(stmt)
    
    return SSAProgram(optimized_statements, optimized.var_versions)
