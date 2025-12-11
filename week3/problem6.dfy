//Chinese Remainder Theorem and the Extended Euclidean Algorithm

// gcd function from earlier gcd benchmark
function gcd_recurse(x: int, y: int): int
    requires x >= 0 && y >= 0
    decreases y
{
    if y == 0 then x else gcd_recurse(y, x % y)
}

// Extended Euclidean Algorithm:
// returns g, x, y with g = gcd(a,b) and a*x + b*y = g
method ExtGCD(a: int, b: int) returns (g: int, x: int, y: int)
  requires a >= 0 && b >= 0 && a + b > 0
  ensures g == gcd_recurse(a, b)
  ensures a * x + b * y == g
  decreases b                     
{
  if b == 0 {
    g := a;
    x := 1;
    y := 0;
  } else {
    var g1: int;
    var x1: int;
    var y1: int;

    // Recursive call
    g1, x1, y1 := ExtGCD(b, a % b);

    g := g1;
    x := y1;
    y := x1 - (a / b) * y1;
  }
}

method ChineseRemainder(mods: array<int>, vals: array<int>) returns (f: int)
  requires mods.Length == vals.Length
  requires mods.Length > 0
  requires forall i :: 0 <= i < mods.Length ==> mods[i] > 0
  requires forall i, j :: 0 <= i < j < mods.Length ==> gcd_recurse(mods[i], mods[j]) == 1
{
  var r := mods.Length;

  // Step 1: compute product M
  var M := 1;
  var i := 0;
  while i < r
    invariant 0 <= i <= r
    invariant M > 0
    decreases r - i
  {
    M := M * mods[i];
    i := i + 1;
  }

  // Step 2 & 3: compute combination
  var sum := 0;
  i := 0;
  while i < r
    invariant 0 <= i <= r
    decreases r - i
  {
    var mi := mods[i];
    var vi := vals[i];

    var Mi := M / mi;

    var g: int;
    var s: int;
    var t: int;
    g, s, t := ExtGCD(Mi, mi);

    // c_i = v_i * s (mod m_i)
    var ci := (vi * s) % mi;
    if ci < 0 {
      ci := ci + mi;
    }

    sum := sum + ci * Mi;
    i := i + 1;
  }

  f := sum % M;
  if f < 0 {
    f := f + M;
  }
}

