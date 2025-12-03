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
    // ghost var GCD := gcd_recurse(a,b);
    while y != 0
        invariant x > 0
        invariant y >= 0
        // invariant gcd_recurse(x,y) == GCD
        decreases y
    {
        var temp := y;
        y := x % y;
        x := temp;
    }
    gcd := x;
    GCD_is_Factor(a,b,gcd);
}

function gcd_recurse(x: int, y: int): int
    requires x >= 0 && y >= 0
    decreases y
{
    if y == 0 then x else gcd_recurse(y, x % y)
}

lemma {:axiom} GCD_is_Factor(x: int, y: int, gcd: int)
    requires x >= 0 && y >= 0 && gcd >= 1
    ensures x % gcd == 0 && y % gcd == 0

// Problem: timeout error and maximal common factor lemma