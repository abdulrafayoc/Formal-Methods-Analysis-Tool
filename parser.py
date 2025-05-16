import ply.lex as lex
import ply.yacc as yacc
from typing import List, Dict, Any, Optional, Union
import ast

# Node classes for our AST
class Node:
    pass

class Program(Node):
    def __init__(self, statements):
        self.statements = statements

class VarDecl(Node):
    def __init__(self, name, value):
        self.name = name
        self.value = value

class Assignment(Node):
    def __init__(self, name, value):
        self.name = name
        self.value = value

class BinaryOp(Node):
    def __init__(self, left, op, right):
        self.left = left
        self.op = op
        self.right = right

class UnaryOp(Node):
    def __init__(self, op, expr):
        self.op = op
        self.expr = expr

class Variable(Node):
    def __init__(self, name):
        self.name = name

class Constant(Node):
    def __init__(self, value):
        self.value = value

class While(Node):
    def __init__(self, condition, body):
        self.condition = condition
        self.body = body

class For(Node):
    def __init__(self, init, condition, update, body):
        self.init = init
        self.condition = condition
        self.update = update
        self.body = body

class If(Node):
    def __init__(self, condition, true_branch, false_branch=None):
        self.condition = condition
        self.true_branch = true_branch
        self.false_branch = false_branch

class Assert(Node):
    def __init__(self, condition):
        self.condition = condition

# Lexer definition
tokens = (
    'VAR', 'IDENTIFIER', 'NUMBER',
    'PLUS', 'MINUS', 'TIMES', 'DIVIDE', 'MOD',
    'EQ', 'LT', 'GT', 'LE', 'GE', 'NE', 'AND', 'OR', 'NOT',
    'ASSIGN', 'COLON_EQ',
    'LPAREN', 'RPAREN', 'LBRACE', 'RBRACE', 'SEMICOLON',
    'WHILE', 'FOR', 'IF', 'ELSE', 'ASSERT'
)

# Simple token rules
t_PLUS = r'\+'
t_MINUS = r'-'
t_TIMES = r'\*'
t_DIVIDE = r'/'
t_MOD = r'%'
t_ASSIGN = r'='
t_COLON_EQ = r':='
t_LPAREN = r'\('
t_RPAREN = r'\)'
t_LBRACE = r'\{'
t_RBRACE = r'\}'
t_SEMICOLON = r';'
t_EQ = r'=='
t_LT = r'<'
t_GT = r'>'
t_LE = r'<='
t_GE = r'>='
t_NE = r'!='

# Reserved words
reserved = {
    'var': 'VAR',
    'while': 'WHILE',
    'for': 'FOR',
    'if': 'IF',
    'else': 'ELSE',
    'assert': 'ASSERT',
    'and': 'AND',
    'or': 'OR',
    'not': 'NOT',
}

def t_IDENTIFIER(t):
    r'[a-zA-Z_][a-zA-Z0-9_]*'
    t.type = reserved.get(t.value, 'IDENTIFIER')
    return t

def t_NUMBER(t):
    r'\d+(\.\d+)?'
    if '.' in t.value:
        t.value = float(t.value)
    else:
        t.value = int(t.value)
    return t

# Comments
def t_COMMENT(t):
    r'//.*'
    pass  # No return value, token is discarded

# Ignored characters
t_ignore = ' \t\n'

def t_error(t):
    print(f"Illegal character '{t.value[0]}'")
    t.lexer.skip(1)

# Build the lexer
lexer = lex.lex()

# Parsing rules
def p_program(p):
    '''program : statements'''
    p[0] = Program(p[1])

def p_statements(p):
    '''statements : statement
                  | statement statements'''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = [p[1]] + p[2]

def p_statement(p):
    '''statement : var_declaration
                 | assignment
                 | while_loop
                 | for_loop
                 | if_statement
                 | assert_statement'''
    p[0] = p[1]

def p_var_declaration(p):
    '''var_declaration : VAR IDENTIFIER ASSIGN expression SEMICOLON
                       | VAR IDENTIFIER COLON_EQ expression SEMICOLON'''
    p[0] = VarDecl(p[2], p[4])

def p_assignment(p):
    '''assignment : IDENTIFIER ASSIGN expression SEMICOLON
                  | IDENTIFIER COLON_EQ expression SEMICOLON'''
    p[0] = Assignment(p[1], p[3])

def p_while_loop(p):
    '''while_loop : WHILE LPAREN expression RPAREN LBRACE statements RBRACE'''
    p[0] = While(p[3], p[6])

def p_for_loop(p):
    '''for_loop : FOR LPAREN var_declaration expression SEMICOLON assignment RPAREN LBRACE statements RBRACE
                | FOR LPAREN assignment expression SEMICOLON assignment RPAREN LBRACE statements RBRACE'''
    # Remove the semicolon from the assignment in p[6]
    update_assignment = p[6]
    p[0] = For(p[3], p[4], update_assignment, p[9])

def p_if_statement(p):
    '''if_statement : IF LPAREN expression RPAREN LBRACE statements RBRACE
                    | IF LPAREN expression RPAREN LBRACE statements RBRACE ELSE LBRACE statements RBRACE'''
    if len(p) > 8:
        p[0] = If(p[3], p[6], p[10])
    else:
        p[0] = If(p[3], p[6])

def p_assert_statement(p):
    '''assert_statement : ASSERT expression SEMICOLON'''
    p[0] = Assert(p[2])

def p_expression(p):
    '''expression : term
                  | expression PLUS term
                  | expression MINUS term'''
    if len(p) == 2:
        p[0] = p[1]
    elif p[2] == '+':
        p[0] = BinaryOp(p[1], '+', p[3])
    elif p[2] == '-':
        p[0] = BinaryOp(p[1], '-', p[3])

def p_term(p):
    '''term : factor
            | term TIMES factor
            | term DIVIDE factor
            | term MOD factor'''
    if len(p) == 2:
        p[0] = p[1]
    elif p[2] == '*':
        p[0] = BinaryOp(p[1], '*', p[3])
    elif p[2] == '/':
        p[0] = BinaryOp(p[1], '/', p[3])
    elif p[2] == '%':
        p[0] = BinaryOp(p[1], '%', p[3])

def p_factor(p):
    '''factor : primary
              | NOT primary
              | MINUS primary %prec UMINUS'''
    if len(p) == 2:
        p[0] = p[1]
    elif p[1] == 'not':
        p[0] = UnaryOp('not', p[2])
    elif p[1] == '-':
        p[0] = UnaryOp('-', p[2])

def p_comparison(p):
    '''comparison : comparison EQ atomic
                  | comparison NE atomic
                  | comparison LT atomic
                  | comparison GT atomic
                  | comparison LE atomic
                  | comparison GE atomic
                  | comparison AND atomic
                  | comparison OR atomic
                  | atomic'''
    if len(p) == 2:
        p[0] = p[1]
    else:
        p[0] = BinaryOp(p[1], p[2], p[3])

def p_primary(p):
    '''primary : comparison'''
    p[0] = p[1]

def p_atomic(p):
    '''atomic : IDENTIFIER
              | NUMBER
              | LPAREN expression RPAREN'''
    if p[1] == '(':
        p[0] = p[2]
    elif isinstance(p[1], (int, float)):
        p[0] = Constant(p[1])
    else:
        p[0] = Variable(p[1])

# Error rule
def p_error(p):
    if p:
        print(f"Syntax error at '{p.value}'")
    else:
        print("Syntax error at EOF")

# Set precedence to resolve ambiguity
precedence = (
    ('left', 'OR'),
    ('left', 'AND'),
    ('left', 'EQ', 'NE'),
    ('left', 'LT', 'GT', 'LE', 'GE'),
    ('left', 'PLUS', 'MINUS'),
    ('left', 'TIMES', 'DIVIDE', 'MOD'),
    ('right', 'NOT', 'UMINUS'),
)

# Build the parser
parser = yacc.yacc()

def parse_program(code: str) -> Program:
    """
    Parse the given code string into an AST.
    
    Args:
        code: The source code to parse
        
    Returns:
        The AST root node (Program)
    """
    return parser.parse(code, lexer=lexer)

if __name__ == "__main__":
    # Simple test code
    test_code = """
    var x = 10;
    var y = 20;
    
    while (x < y) {
        x = x + 1;
    }
    
    assert x == y;
    """
    
    ast = parse_program(test_code)
    print("Parse successful!")
