method FibIter(n: nat) returns (f: nat)
  ensures (n == 0 ==> f == 0)
  ensures (n == 1 ==> f == 1)
  ensures (n >= 2 ==> f >= 1) 
{
  if n == 0 {
    f := 0;
    return;
  }
  if n == 1 {
    f := 1;
    return;
  }

  var a := 0;   // F(0)
  var b := 1;   // F(1)
  var i := 1;

  while i < n
    invariant 1 <= i <= n
    invariant a >= 0 && b >= 0
    decreases n - i
  {
    var next := a + b;
    a := b;
    b := next;
    i := i + 1;
  }

  f := b;
}
