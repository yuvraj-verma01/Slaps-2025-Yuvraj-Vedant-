// Count permutations 
// Uses the recurrence:
//   Perm(n, 0) = 1
//   Perm(n, r) = Perm(n, r-1) * (n - (r-1))

function Perm(n: nat, r: nat): nat
  requires r <= n
  decreases r
{
  if r == 0 then
    1
  else
    Perm(n, r - 1) * (n - (r - 1))
}


method PermutationCount(a: array<int>, r: nat) returns (p: nat)
  requires r <= a.Length
  ensures p == Perm(a.Length, r)
{
  var n := a.Length;

  p := 1;
  var i := 0;

  while i < r
    invariant 0 <= i <= r
    invariant p == Perm(n, i)
    decreases r - i
  {
    
    p := p * (n - i);
    i := i + 1;
  }

  assert i == r;
  assert p == Perm(n, r);
}
