// Counting combinations
// Using a recurrence:
//   Choose(n, 0) = 1
//   Choose(n, r) = Choose(n, r-1) * (n - (r-1)) / r
function Choose(n: nat, r: nat): nat
  requires r <= n
  decreases r
{
  if r == 0 then
    1
  else
    Choose(n, r - 1) * (n - (r - 1)) / r
}

// Given an array a and a number r, compute nCr where n = a.Length
method CombinationCount(a: array<int>, r: nat) returns (c: nat)
  requires r <= a.Length
  ensures c == Choose(a.Length, r)
{
  var n := a.Length;

  c := 1;
  var i := 0;

  // After i steps, we want c == Choose(n, i)
  while i < r
    invariant 0 <= i <= r
    invariant r <= n
    invariant c == Choose(n, i)
    decreases r - i
  {
    // Update using: Choose(n, i+1) = Choose(n, i) * (n - i) / (i + 1)
    c := c * (n - i) / (i + 1);
    i := i + 1;
  }

  // Now i == r, so c == Choose(n, r)
  assert i == r;
  assert c == Choose(n, r);
  assert n == a.Length;          // so ensures matches
}
