// Example 1: Sum of first n natural numbers
// This demonstrates basic loop invariant usage

method Sum(n: int) returns (sum: int)
    requires n >= 0
    ensures sum == n * (n + 1) / 2
{
    var i := 0;
    sum := 0;
    
    while i <= n
        invariant 0 <= i <= n + 1
        invariant sum == i * (i - 1) / 2
        decreases n - i
    {
        sum := sum + i;
        i := i + 1;
    }
}
