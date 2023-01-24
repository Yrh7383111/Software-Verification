method max_rotate_function(nums: array<int>) returns (result: int)
    requires 1 <= nums.Length <= 100000
    requires forall i :: 0 <= i < nums.Length ==> -100 <= nums[i] <= 100
    ensures forall i :: 0 <= i < nums.Length ==> result >= max_rotate_function_helper(nums, i, 0, nums.Length - 1)
{
    var length := nums.Length;

    var max := 0;
    var counter := 0;
    while (counter < length)
        invariant 0 <= counter <= length
    {
        max := max + counter * nums[counter];

        counter := counter + 1;
    }

    var i := 0;
    while (i < length)
        invariant 0 <= i <= length
        invariant forall k :: 0 <= k < i ==> max >= max_rotate_function_helper(nums, k, 0, length - 1)
    {
        var sum := 0;
        var j := 0;
        while (j < length)
            invariant 0 <= j <= length
        {
            sum := sum + j * nums[(i + j) % length];

            j := j + 1;
        }

        max := find_max(max, sum);
        i := i + 1;
    }


    return max;
}


function method find_max(x: int, y: int): int
{
    if x > y then x
    else y
}

function max_rotate_function_helper(nums: array<int>, position: int, start: int, end: int): int
    requires 0 <= start <= nums.Length
    requires 0 <= end < nums.Length
    reads nums
    decreases end - start
{
    if (start > end) then 0
    else nums[position % nums.Length] * start + max_rotate_function_helper(nums, position + 1, start + 1, end)
}
