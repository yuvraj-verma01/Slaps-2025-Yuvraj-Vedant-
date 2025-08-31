// Example 3: Fibonacci calculation with loop invariant
// This demonstrates invariant synthesis for iterative algorithms

method fibonacci(n: int) returns (fib: int)
    requires n >= 0
    ensures fib == Fibonacci(n)
{
    if n <= 1 {
        fib := n;
    } else {
        var a := 0;
        var b := 1;
        var i := 2;
        
        while i <= n
            invariant 2 <= i <= n + 1
            invariant a == Fibonacci(i - 2)
            invariant b == Fibonacci(i - 1)
            decreases n - i
        {
            var temp := a + b;
            a := b;
            b := temp;
            i := i + 1;
        }
        
        fib := b;
    }
}

// Helper function for Fibonacci
function Fibonacci(n: int): int
    requires n >= 0
{
    if n <= 1 then n else Fibonacci(n - 1) + Fibonacci(n - 2)
}

