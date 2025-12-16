//finding maximum element in array

method ArrayMax(a: array<int>) returns (m: int)
    requires a != null && a.Length > 0
    ensures forall k :: 0 <= k < a.Length ==> a[k] <= m
    ensures exists k :: 0 <= k < a.Length && a[k] == m
{
    var i := 1;
    m := a[0];

    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> a[k] <= m
        invariant exists k :: 0 <= k < i && a[k] == m
        decreases a.Length - i
    {
        if a[i] > m {
            m := a[i];
        }
        i := i + 1;
    }
}