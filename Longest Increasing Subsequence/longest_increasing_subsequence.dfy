method longest_increasing_subsequence(nums: array<int>) returns (result: int)
    requires 1 <= nums.Length <= 2500
    requires forall i :: 0 <= i < nums.Length ==> -10000 <= nums[i] <= 10000
    ensures result >= 1
{
    var length := nums.Length;
    if (length == 1)
    {
        return 1;
    }

    var max := 1;
    var dp := new int[length](_ => 1);

    var i := 1;
    while (i < length)
        modifies dp
        invariant 1 <= i <= length
        invariant max >= 1
    {
        var j := 0;
        while (j < i)
            invariant 0 <= j <= i
        {
            if (nums[j] < nums[i])
            {
                dp[i] := find_max(dp[i], dp[j] + 1);
            }

            j := j + 1;
        }

        max := find_max(max, dp[i]);
        i := i + 1;
    }

    return max;
}


// Function
function method find_max(x: int, y: int): int
{
    if x > y then x
    else y
}
