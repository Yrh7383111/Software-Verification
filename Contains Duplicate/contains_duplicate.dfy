method contains_duplicate(nums: array<int>) returns (result: bool)
    requires 1 <= nums.Length <= 100000
    requires forall i :: 0 <= i < nums.Length ==> -1000000000 <= nums[i] <= 1000000000
    ensures result == true ==> (exists i, j :: 0 <= i < j < nums.Length && nums[i] == nums[j])
    ensures result == false ==> forall i, j :: 0 <= i < j < nums.Length ==> nums[i] != nums[j]
{
    var s := create_set_from_array(nums);
    result := nums.Length != |s|;
}

method create_set_from_array(nums: array<int>) returns (s: set<int>)
    ensures forall i :: i in s ==> (exists j :: 0 <= j < nums.Length && nums[j] == i)
    ensures forall i, j :: i in s && j in s ==> i != j
{
    s := {};

    var i := 0;
    while (i < nums.Length)
        invariant 0 <= i <= nums.Length
        invariant forall j :: j in s ==> (exists k :: 0 <= k < i && nums[k] == j)
        invariant forall j, k :: j in s && k in s ==> j != k
    {
        s := s + {nums[i]};

        i := i + 1;
    }
}
