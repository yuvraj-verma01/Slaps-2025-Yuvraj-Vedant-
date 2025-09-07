// Problem 1: Simple Loop with Two Variables
// Write loop invariant(s) for this method

method loop(n: int) returns (j: int)
    requires n >= 0
    ensures j == 2 * n
{
    var i := 0;
    j := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant j == 2 * i
        decreases n - i
    {
        i := i + 1;
        j := j + 2;
    }
}
