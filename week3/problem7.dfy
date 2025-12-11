// Quick Sort

// helper
method Swap(a: array<int>, i: int, j: int)
  requires 0 <= i < a.Length && 0 <= j < a.Length
  modifies a
{
  var t := a[i];
  a[i] := a[j];
  a[j] := t;
}
// pick pivot = a[high]
// move everything <= pivot to the left.
// return final index of the pivot.
method Partition(a: array<int>, low: int, high: int) returns (p: int)
  requires 0 <= low <= high < a.Length
  modifies a
  ensures low <= p <= high
  decreases high - low
{
  var pivot := a[high];
  var i := low;   

  var j := low;
  while j < high
    invariant low <= i <= j <= high
    decreases high - j
  {
    if a[j] <= pivot {
      Swap(a, i, j);
      i := i + 1;
    }
    j := j + 1;
  }

  // put pivot in its correct place
  Swap(a, i, high);
  p := i;
}

// Recursive quicksort on subarray a[low..high]
method QuickSortRange(a: array<int>, low: int, high: int)
  requires 0 <= low <= high < a.Length
  modifies a
  decreases high - low + 1
{
  if low < high {
    var p := Partition(a, low, high);

    // left side strictly smaller: [low..p-1]
    if p > low {
      QuickSortRange(a, low, p - 1);
    }

    // right side strictly smaller: [p+1..high]
    if p < high {
      QuickSortRange(a, p + 1, high);
    }
  }
}

// Wrapper to sort whole array
method QuickSort(a: array<int>)
  modifies a
{
  if a.Length > 1 {
    QuickSortRange(a, 0, a.Length - 1);
  }
}
