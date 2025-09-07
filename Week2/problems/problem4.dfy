// Problem 4: Fast Power (Exponentiation by Squaring)
// Write loop invariant(s) for this method

method FastPower(base: int, exp: int) returns (result: int)
  requires exp >= 0
  ensures result == Power(base, exp)
{
  var x := base;
  var n := exp;
  result := 1;

  while n > 0
    invariant n >= 0
    invariant result * Power(x, n) == Power(base, exp)
    decreases n
  {
    if n % 2 == 1 {
      result := result * x;
    }
    x := x * x;
    n := n / 2;
  }
}

// Helper function
function Power(base: int, exp: int): int
    requires exp >= 0
{
    if exp == 0 then 1 else base * Power(base, exp - 1)
}
