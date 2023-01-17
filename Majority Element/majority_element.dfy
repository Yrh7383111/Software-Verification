method majority_element(nums: array<int>) returns (majorityElement: int)
    requires nums.Length > 0
    ensures count_occurance(nums, 0, nums.Length - 1, majorityElement) > nums.Length / 2
{
    var count := 0;
    var candiate := nums[0];

    var i := 0;
    while (i < nums.Length)
        invariant 0 <= i <= nums.Length
        invariant count >= 0
        invariant forall j :: 0 <= j < i ==> count_occurance(nums, 0, j, candiate) > (j + 1) / 2
        decreases nums.Length - i
    {
        var num := nums[i];

        if (count == 0)
        {
            candiate := num;
        }

        if (num == candiate)
        {
            count := count + 1;
        }
        else
        {
            count := count - 1;
        }

        i := i + 1;
    }

    return candiate;
}

function count_occurance(arr: array<int>, begin: int, end: int, element: int): int
    requires 0 <= begin <= arr.Length
    requires 0 <= end <= arr.Length - 1
    decreases end - begin
    reads arr
{
    if begin > end then 0
    else if arr[begin] == element then 1 + count_occurance(arr, begin + 1, end, element)
    else count_occurance(arr, begin + 1, end, element)
}
