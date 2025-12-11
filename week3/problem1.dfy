// Sum of a sequence

function Sum(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else s[0] + Sum(s[1..])
}

lemma SumSnoc(s: seq<int>, x: int)
  ensures Sum(s + [x]) == Sum(s) + x
  decreases |s|
{
  if |s| == 0 {
    assert s == [];
    assert s + [x] == [x];
    assert Sum(s) == 0;
    assert Sum(s + [x]) == x;
  } else {
    var head := s[0];
    var tail := s[1..];
    assert Sum(s) == head + Sum(tail);
    assert (s + [x])[0] == head;
    assert (s + [x])[1..] == tail + [x];
    assert Sum(s + [x]) == head + Sum(tail + [x]);

    SumSnoc(tail, x);
    assert Sum(tail + [x]) == Sum(tail) + x;

    assert Sum(s + [x]) == head + (Sum(tail) + x);
    assert Sum(s + [x]) == (head + Sum(tail)) + x;
    assert Sum(s + [x]) == Sum(s) + x;
  }
}

method ArraySum(a: array<int>) returns (sum: int)
  ensures sum == Sum(a[..])
{
  var i := 0;
  sum := 0;
  ghost var prefix: seq<int> := [];

  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant prefix == a[..i]
    invariant sum == Sum(prefix)
    decreases a.Length - i
  {
    SumSnoc(prefix, a[i]);
    prefix := prefix + [a[i]];
    sum := sum + a[i];
    i := i + 1;
  }

  assert prefix == a[..];
  assert sum == Sum(a[..]);
}
