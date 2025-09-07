// Problem 3: GCD Calculation
// Write loop invariant(s) for this method

method GCD(a: int, b: int) returns (gcd: int)
    requires a > 0 && b > 0
    ensures gcd > 0
    ensures a % gcd == 0 && b % gcd == 0
    ensures forall d :: d > 0 && a % d == 0 && b % d == 0 ==> d <= gcd
{
    var x := a;
    var y := b;
    
    while y != 0
        invariant x >= 0 && y >= 0
        invariant forall d :: d>0 && x % d == 0 && y % d == 0 <==> a % d == 0 && b % d == 0
        decreases y
    {
        var temp := y;
        y := x % y;
        x := temp;
    }
    
    gcd := x;
}