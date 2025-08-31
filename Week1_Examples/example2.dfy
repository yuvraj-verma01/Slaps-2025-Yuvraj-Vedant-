// Example 2: Factorial calculation with loop invariant
// This demonstrates invariant synthesis for mathematical computations

method factorial(n: int) returns (fact: int)
    requires n >= 0
    ensures fact == Factorial(n)
{
    var i := 0;
    fact := 1;
    
    while i < n
        invariant 0 <= i <= n
        invariant fact == Factorial(i)
        decreases n - i
    {
        i := i + 1;
        fact := fact * i;
    }
}

// Helper function for factorial
function Factorial(n: int): int
    requires n >= 0
{
    if n == 0 then 1 else n * Factorial(n - 1)
}

