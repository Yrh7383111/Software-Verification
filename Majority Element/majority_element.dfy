method majority_element(nums: array<int>) returns (majority: int)
    requires nums.Length > 0
    requires exists element :: (count_occurrence(nums, 0, nums.Length - 1, element) > nums.Length / 2)
    // TODO:
    ensures count_occurrence(nums, 0, nums.Length - 1, majority) > nums.Length / 2
{
    var count := 0;
    majority := nums[0];

    var i := 0;
    while (i < nums.Length)
        invariant 0 <= i <= nums.Length
        invariant count >= 0
        invariant forall j :: 0 <= j < i ==> count_occurrence(nums, 0, j, majority) > (j + 1) / 2
        decreases nums.Length - i
    {
        var num := nums[i];

        if (count == 0)
        {
            majority := num;
        }

        if (num == majority)
        {
            count := count + 1;
        }
        else
        {
            count := count - 1;
        }

        i := i + 1;
    }
}

function count_occurrence(arr: array<int>, begin: int, end: int, element: int): int
    requires 0 <= begin <= arr.Length
    requires 0 <= end <= arr.Length - 1
    decreases end - begin
    reads arr
{
    if begin > end then 0
    else if arr[begin] == element then 1 + count_occurrence(arr, begin + 1, end, element)
    else count_occurrence(arr, begin + 1, end, element)
}
