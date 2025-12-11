// GCD

function gcd_recurse(x: int, y: int): int
    requires x >= 0 && y >= 0
    decreases y
{
    if y == 0 then x else gcd_recurse(y, x % y)
}

lemma {:axiom} GCD_is_Factor(x: int, y: int, g: int)
    requires x >= 0 && y >= 0
    requires g > 0                 
    requires g == gcd_recurse(x, y)
    ensures x % g == 0 && y % g == 0


lemma {:axiom} GCD_is_Maximal(x: int, y: int, g: int)
    requires x >= 0 && y >= 0
    requires g > 0
    requires g == gcd_recurse(x, y)
    ensures forall d :: d > 0 && x % d == 0 && y % d == 0 ==> d <= g



method GCD(a: int, b: int) returns (gcd: int)
    requires a > 0 && b > 0
    ensures gcd > 0
    ensures a % gcd == 0 && b % gcd == 0
    ensures forall d :: d > 0 && a % d == 0 && b % d == 0 ==> d <= gcd
{
    var x := a;
    var y := b;


    ghost var G := gcd_recurse(a, b);

    while y != 0
        invariant x > 0
        invariant y >= 0
        invariant gcd_recurse(x, y) == G  
        decreases y
    {
        var temp := y;
        y := x % y;
        x := temp;
    }


    gcd := x;

   
    assert gcd_recurse(x, 0) == x;
    assert gcd == G;

    assert gcd > 0;  

    GCD_is_Factor(a, b, gcd);
    GCD_is_Maximal(a, b, gcd);
}
