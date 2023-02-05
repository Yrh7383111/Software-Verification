method max_rotate_function(nums: array<int>) returns (max: int)
    requires 1 <= nums.Length <= 100000
    requires forall i :: 0 <= i < nums.Length ==> 0 <= nums[i] <= 100
    ensures max_rotate_function_helper(nums, max, nums.Length)
{
    var length := nums.Length;

    max := initialize_max(nums);

    var i := 0;
    while (i < length)
        invariant 0 <= i <= length
        invariant max_rotate_function_helper(nums, max, i)
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
}


// Helper predicates
predicate max_rotate_function_helper(nums: array<int>, max: int, limit: int)
    requires 0 <= limit <= nums.Length
    reads nums
{
    forall i :: 0 <= i < limit ==> max >= calculate_rotate_number(nums, i, 0, nums.Length - 1)
}


// Helper functions
function method find_max(x: int, y: int): int
{
    if x > y then x
    else y
}

function calculate_rotate_number(nums: array<int>, position: int, start: int, end: int): int
    requires 0 <= start <= nums.Length
    requires 0 <= end < nums.Length
    reads nums
    decreases end - start
{
    if (start > end) then 0
    else nums[position % nums.Length] * start + calculate_rotate_number(nums, position + 1, start + 1, end)
}


// Helper methods
method initialize_max(nums: array<int>) returns (max: int)
    requires 1 <= nums.Length <= 100000
    requires forall i :: 0 <= i < nums.Length ==> 0 <= nums[i] <= 100
    ensures max == calculate_rotate_number(nums, 0, 0, nums.Length - 1)
{
    var length := nums.Length;
    max := 0;
    var pre_max := 0;

    var i := 0;
    while (i < length)
        invariant 0 <= i <= length
        // TODO: add an invariant which supports the ensures the clause
    {
        pre_max := max;
        max := max + i * nums[i];

        i := i + 1;
    }
}
