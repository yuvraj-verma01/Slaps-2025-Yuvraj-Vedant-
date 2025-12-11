// two sum

method TwoSum(nums: array<int>, target: int) returns (i: int, j: int)
    requires nums.Length >= 2
    ensures 0 <= i < nums.Length
    ensures 0 <= j < nums.Length
{
    i := 0;
    j := 0;

    var n := nums.Length;

    var a := 0;
    while a < n
        invariant 0 <= a <= n
        decreases n - a
    {
        var b := a + 1;
        while b < n
            invariant a + 1 <= b <= n
            decreases n - b
        {
            if nums[a] + nums[b] == target {
                i := a;
                j := b;
                return i, j;
            }
            b := b + 1;
        }
        a := a + 1;
    }
}
