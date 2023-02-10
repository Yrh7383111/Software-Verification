method contains_duplicate(nums: array<int>) returns (s: set<int>)
    requires 1 <= nums.Length <= 100000
    requires forall i :: 0 <= i < nums.Length ==> -1000000000 <= nums[i] <= 1000000000
    ensures |s| == nums.Length ==> is_distinct(nums, 0, nums.Length)
    ensures |s| != nums.Length  ==> exists i :: (0 <= i < nums.Length ==> count_occurrence(nums, 0, nums.Length - 1, nums[i]) >= 2)
{
    s := {nums[0]};
    var length := nums.Length;
    
    var i := 1;
    while (i < length)
        invariant 1 <= i <= length
        invariant |s| <= i
        invariant |s| == i ==> is_distinct(nums, 0, i)
        invariant |s| < i ==> exists j :: (0 <= j < i ==> count_occurrence(nums, 0, j, nums[j]) >= 2)
    {
        s := s + {nums[i]};

        i := i + 1;
    }    
}


// Helper function
function count_occurrence(nums: array<int>, begin: int, end: int, element: int): int
    requires 0 <= begin <= nums.Length
    requires 0 <= end <= nums.Length - 1
    decreases end - begin
    reads nums
{
    if begin > end then 0
    else if nums[begin] == element then 1 + count_occurrence(nums, begin + 1, end, element)
    else count_occurrence(nums, begin + 1, end, element)
}


// Helper predicate
predicate is_distinct(nums: array<int>, begin: int, end: int)
    requires 0 <= begin <= nums.Length
    requires 0 <= end <= nums.Length
    reads nums
{
    forall i, j :: begin <= i < j < end ==> nums[i] != nums[j]
}
