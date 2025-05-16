"""
Example programs for verification and equivalence checking
"""

# Example 1: If-Else statement
IF_ELSE_EXAMPLE = """
// Example 1: If-Else Statement
var x := 3;
if (x < 5) {
    var y := x + 1;
} else {
    var y := x - 1;
}
assert y > 0;
"""

# Example 2: Loop
WHILE_LOOP_EXAMPLE = """
// Example 2: While Loop
var x := 0;
while (x < 4) {
    x := x + 1;
}
assert x == 4;
"""

# Example 3: Bubble Sort (simplified without arrays for now)
BUBBLE_SORT_EXAMPLE = """
// Example 3: Simplified Bubble Sort concept
var n := 5;
var i := 0;
var sorted := 0;

while (i < n) {
    var j := 0;
    while (j < n - i - 1) {
        // Simulating comparison and swap logic
        j := j + 1;
    }
    i := i + 1;
    sorted := sorted + 1;
}
assert sorted == n;
"""

# Equivalence examples:
# Example pair 1: Different ways to calculate sum
SUM_LOOP = """
// Sum calculation using loop
var n := 5;
var sum := 0;
var i := 1;

while (i <= n) {
    sum := sum + i;
    i := i + 1;
}
"""

SUM_FORMULA = """
// Sum calculation using formula
var n := 5;
var sum := n * (n + 1) / 2;
"""

# Example pair 2: Different ways to calculate factorial
FACTORIAL_LOOP = """
// Factorial using loop
var n := 5;
var factorial := 1;
var i := 1;

while (i <= n) {
    factorial := factorial * i;
    i := i + 1;
}
"""

FACTORIAL_RECURSIVE = """
// Simulated factorial using recursive formula pattern
var n := 5;
var factorial := 1;

// Simulating 5! calculation directly
factorial := 1 * 2 * 3 * 4 * 5;
"""

# Additional examples for verification
POWER_CALCULATION = """
// Calculate power function
var base := 2;
var exponent := 3;
var result := 1;

while (exponent > 0) {
    result := result * base;
    exponent := exponent - 1;
}
assert result == 8;
"""

FIBONACCI_CALCULATION = """
// Calculate Fibonacci number
var n := 5;
var fib1 := 0;
var fib2 := 1;
var i := 2;
var fibonacci := 0;

if (n == 0) {
    fibonacci := 0;
} else if (n == 1) {
    fibonacci := 1;
} else {
    while (i <= n) {
        fibonacci := fib1 + fib2;
        fib1 := fib2;
        fib2 := fibonacci;
        i := i + 1;
    }
}
assert fibonacci == 5;
"""