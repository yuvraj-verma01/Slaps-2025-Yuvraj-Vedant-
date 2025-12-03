//iterative fibonacci

method Fib(n: int) returns (f: int)
    requires n >= 0
    ensures f == FibRec(n)
{
    if n == 0 { f := 0; return; }
    if n == 1 { f := 1; return; }

    var a := 0;
    var b := 1;
    var i := 2;

    while i <= n
        invariant 0 <= a && 0 <= b
        invariant b == FibRec(i - 1) && a == FibRec(i - 2)
        invariant 2 <= i <= n + 1
        decreases n - i
    {
        var temp := a + b;
        a := b;
        b := temp;
        i := i + 1;
    }

    assert i == n + 1;
    assert b == FibRec(n);
    f := b;
}

function FibRec(n: int): int
    requires n >= 0
{
    if n < 2 then n else FibRec(n - 1) + FibRec(n - 2)
}