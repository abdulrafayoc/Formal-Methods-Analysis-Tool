from typing import Dict, List, Set, Tuple, Any, Optional
from parser import *
import copy

class SSANode(Node):
    def to_string(self) -> str:
        """Convert the SSA node to a string representation."""
        pass

class SSAProgram(SSANode):
    def __init__(self, statements: List[SSANode], var_versions: Dict[str, int]):
        self.statements = statements
        self.var_versions = var_versions  # Maps variable names to their current version
    
    def to_string(self) -> str:
        result = "// SSA Form\n"
        for stmt in self.statements:
            result += stmt.to_string() + "\n"
        return result

class SSAVarDecl(SSANode):
    def __init__(self, name: str, version: int, value: SSANode):
        self.name = name
        self.version = version
        self.value = value
    
    def to_string(self) -> str:
        return f"var {self.name}_{self.version} = {self.value.to_string()};"

class SSAAssignment(SSANode):
    def __init__(self, name: str, version: int, value: SSANode):
        self.name = name
        self.version = version
        self.value = value
    
    def to_string(self) -> str:
        return f"{self.name}_{self.version} = {self.value.to_string()};"

class SSABinaryOp(SSANode):
    def __init__(self, left: SSANode, op: str, right: SSANode):
        self.left = left
        self.op = op
        self.right = right
    
    def to_string(self) -> str:
        return f"({self.left.to_string()} {self.op} {self.right.to_string()})"

class SSAUnaryOp(SSANode):
    def __init__(self, op: str, expr: SSANode):
        self.op = op
        self.expr = expr
    
    def to_string(self) -> str:
        if self.op == "not":
            return f"!{self.expr.to_string()}"
        return f"{self.op}{self.expr.to_string()}"

class SSAVariable(SSANode):
    def __init__(self, name: str, version: int):
        self.name = name
        self.version = version
    
    def to_string(self) -> str:
        return f"{self.name}_{self.version}"

class SSAConstant(SSANode):
    def __init__(self, value: Any):
        self.value = value
    
    def to_string(self) -> str:
        return str(self.value)

class SSAWhile(SSANode):
    def __init__(self, condition: SSANode, body: List[SSANode], phi_functions: List[SSANode]):
        self.condition = condition
        self.body = body
        self.phi_functions = phi_functions  # Φ functions for loop
    
    def to_string(self) -> str:
        result = f"while ({self.condition.to_string()}) {{\n"
        for phi in self.phi_functions:
            result += "  " + phi.to_string() + "\n"
        for stmt in self.body:
            result += "  " + stmt.to_string() + "\n"
        result += "}"
        return result

class SSAIf(SSANode):
    def __init__(self, condition: SSANode, true_branch: List[SSANode], 
                false_branch: Optional[List[SSANode]], phi_functions: List[SSANode]):
        self.condition = condition
        self.true_branch = true_branch
        self.false_branch = false_branch
        self.phi_functions = phi_functions  # Φ functions after if-else
    
    def to_string(self) -> str:
        result = f"if ({self.condition.to_string()}) {{\n"
        for stmt in self.true_branch:
            result += "  " + stmt.to_string() + "\n"
        result += "}"
        
        if self.false_branch:
            result += " else {\n"
            for stmt in self.false_branch:
                result += "  " + stmt.to_string() + "\n"
            result += "}"
        
        if self.phi_functions:
            result += "\n// Φ functions\n"
            for phi in self.phi_functions:
                result += phi.to_string() + "\n"
        
        return result

class SSAPhiFunction(SSANode):
    def __init__(self, name: str, version: int, sources: List[Tuple[str, int]]):
        self.name = name
        self.version = version
        self.sources = sources  # List of (name, version) pairs
    
    def to_string(self) -> str:
        sources_str = ", ".join([f"{name}_{version}" for name, version in self.sources])
        return f"{self.name}_{self.version} = Φ({sources_str});"

class SSAAssert(SSANode):
    def __init__(self, condition: SSANode):
        self.condition = condition
    
    def to_string(self) -> str:
        return f"assert {self.condition.to_string()};"

def convert_to_ssa(ast: Program) -> SSAProgram:
    """
    Convert an AST to SSA form.
    
    Args:
        ast: The AST to convert
        
    Returns:
        An SSA representation of the program
    """
    var_versions = {}  # Maps variable names to their current version
    ssa_statements = []
    
    # Helper function to get the current version of a variable
    def get_version(name: str) -> int:
        if name not in var_versions:
            var_versions[name] = 0
        return var_versions[name]
    
    # Helper function to increment the version of a variable
    def increment_version(name: str) -> int:
        if name not in var_versions:
            var_versions[name] = 0
        else:
            var_versions[name] += 1
        return var_versions[name]
    
    # Convert an expression to SSA form
    def convert_expression(expr: Node) -> SSANode:
        if isinstance(expr, Variable):
            version = get_version(expr.name)
            return SSAVariable(expr.name, version)
        
        elif isinstance(expr, Constant):
            return SSAConstant(expr.value)
        
        elif isinstance(expr, BinaryOp):
            left_ssa = convert_expression(expr.left)
            right_ssa = convert_expression(expr.right)
            return SSABinaryOp(left_ssa, expr.op, right_ssa)
        
        elif isinstance(expr, UnaryOp):
            expr_ssa = convert_expression(expr.expr)
            return SSAUnaryOp(expr.op, expr_ssa)
        
        else:
            raise ValueError(f"Unknown expression type: {type(expr)}")
    
    # Convert a statement to SSA form
    def convert_statement(stmt: Node) -> List[SSANode]:
        if isinstance(stmt, VarDecl):
            version = increment_version(stmt.name)
            value_ssa = convert_expression(stmt.value)
            return [SSAVarDecl(stmt.name, version, value_ssa)]
        
        elif isinstance(stmt, Assignment):
            version = increment_version(stmt.name)
            value_ssa = convert_expression(stmt.value)
            return [SSAAssignment(stmt.name, version, value_ssa)]
        
        elif isinstance(stmt, While):
            # Save variable versions before the loop
            pre_loop_versions = copy.deepcopy(var_versions)
            
            # First, convert the condition
            condition_ssa = convert_expression(stmt.condition)
            
            # Then, convert the body
            body_ssa = []
            for body_stmt in stmt.body:
                body_ssa.extend(convert_statement(body_stmt))
            
            # Create Φ functions for variables modified in the loop
            phi_functions = []
            for var_name, post_version in var_versions.items():
                if var_name in pre_loop_versions and pre_loop_versions[var_name] != post_version:
                    next_version = increment_version(var_name)
                    sources = [(var_name, pre_loop_versions[var_name]), (var_name, post_version)]
                    phi_functions.append(SSAPhiFunction(var_name, next_version, sources))
            
            return [SSAWhile(condition_ssa, body_ssa, phi_functions)]
        
        elif isinstance(stmt, If):
            # Save variable versions before if statement
            pre_if_versions = copy.deepcopy(var_versions)
            
            # Convert the condition
            condition_ssa = convert_expression(stmt.condition)
            
            # Convert the true branch
            true_branch_versions = copy.deepcopy(var_versions)
            true_branch_ssa = []
            for true_stmt in stmt.true_branch:
                true_branch_ssa.extend(convert_statement(true_stmt))
            
            # Save true branch final versions
            post_true_versions = copy.deepcopy(var_versions)
            
            # Restore pre-if versions for false branch
            var_versions.update(pre_if_versions)
            
            # Convert the false branch
            false_branch_ssa = []
            if stmt.false_branch:
                for false_stmt in stmt.false_branch:
                    false_branch_ssa.extend(convert_statement(false_stmt))
            
            # Create Φ functions for variables modified in either branch
            phi_functions = []
            modified_vars = set()
            
            # Check variables modified in true branch
            for var_name, true_version in post_true_versions.items():
                if var_name in pre_if_versions and true_version != pre_if_versions[var_name]:
                    modified_vars.add(var_name)
            
            # Check variables modified in false branch
            for var_name, false_version in var_versions.items():
                if var_name in pre_if_versions and false_version != pre_if_versions[var_name]:
                    modified_vars.add(var_name)
            
            # Create Φ functions
            for var_name in modified_vars:
                true_version = post_true_versions.get(var_name, pre_if_versions.get(var_name, 0))
                false_version = var_versions.get(var_name, pre_if_versions.get(var_name, 0))
                
                if true_version != false_version:
                    next_version = increment_version(var_name)
                    sources = [(var_name, true_version), (var_name, false_version)]
                    phi_functions.append(SSAPhiFunction(var_name, next_version, sources))
            
            return [SSAIf(condition_ssa, true_branch_ssa, false_branch_ssa, phi_functions)]
        
        elif isinstance(stmt, Assert):
            condition_ssa = convert_expression(stmt.condition)
            return [SSAAssert(condition_ssa)]
        
        else:
            raise ValueError(f"Unknown statement type: {type(stmt)}")
    
    # Convert all statements in the program
    for stmt in ast.statements:
        ssa_statements.extend(convert_statement(stmt))
    
    return SSAProgram(ssa_statements, var_versions)

def unroll_loops(ssa_program: SSAProgram, depth: int) -> SSAProgram:
    """
    Unroll loops in the SSA program up to the specified depth.
    
    Args:
        ssa_program: The SSA program to unroll
        depth: The maximum unrolling depth
        
    Returns:
        A new SSA program with unrolled loops
    """
    # Create a deep copy of the program to avoid modifying the original
    ssa_copy = copy.deepcopy(ssa_program)
    var_versions = copy.deepcopy(ssa_program.var_versions)
    
    # Helper function to unroll a list of statements
    def unroll_statements(statements: List[SSANode], depth: int) -> List[SSANode]:
        result = []
        for stmt in statements:
            if isinstance(stmt, SSAWhile):
                if depth <= 0:
                    # Replace the loop with an assertion that the condition is false
                    condition_negated = SSAUnaryOp("not", stmt.condition)
                    result.append(SSAAssert(condition_negated))
                else:
                    # Unroll once and recurse
                    # First add the condition check
                    condition_copy = copy.deepcopy(stmt.condition)
                    
                    # Create an if statement for the first iteration
                    if_body = copy.deepcopy(stmt.body)
                    
                    # Add Φ functions at the beginning
                    if_body = stmt.phi_functions + if_body
                    
                    # Recursively unroll the body
                    unrolled_body = unroll_statements(if_body, depth - 1)
                    
                    # Create a new while loop with reduced depth for the rest
                    reduced_while = copy.deepcopy(stmt)
                    unrolled_rest = unroll_statements([reduced_while], depth - 1)
                    
                    # Build the final if statement
                    result.append(SSAIf(condition_copy, unrolled_body, [], []))
                    result.extend(unrolled_rest)
            
            elif isinstance(stmt, SSAIf):
                # Recursively unroll both branches
                true_branch_unrolled = unroll_statements(stmt.true_branch, depth)
                
                false_branch_unrolled = []
                if stmt.false_branch:
                    false_branch_unrolled = unroll_statements(stmt.false_branch, depth)
                
                # Create a new if statement with unrolled branches
                result.append(SSAIf(
                    copy.deepcopy(stmt.condition),
                    true_branch_unrolled,
                    false_branch_unrolled,
                    copy.deepcopy(stmt.phi_functions)
                ))
            
            else:
                # Other statement types are passed through unchanged
                result.append(copy.deepcopy(stmt))
        
        return result
    
    # Unroll the entire program
    unrolled_statements = unroll_statements(ssa_copy.statements, depth)
    
    return SSAProgram(unrolled_statements, var_versions)

if __name__ == "__main__":
    from parser import parse_program
    
    # Test program
    test_code = """
    var x = 10;
    var y = 0;
    
    while (x > 0) {
        y = y + x;
        x = x - 1;
    }
    
    assert y == 55;
    """
    
    ast = parse_program(test_code)
    ssa = convert_to_ssa(ast)
    print(ssa.to_string())
    
    # Test unrolling
    unrolled = unroll_loops(ssa, 3)
    print("\nUnrolled (depth=3):")
    print(unrolled.to_string())
