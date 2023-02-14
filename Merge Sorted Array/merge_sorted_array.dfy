method merge(nums1: array<int>, nums2: array<int>) returns (result: array<int>)
    requires 1 <= nums1.Length <= 200
    requires 1 <= nums2.Length <= 200
    requires is_sorted(nums1, nums1.Length)
    requires is_sorted(nums2, nums2.Length)
    ensures result.Length == nums1.Length + nums2.Length
    ensures is_sorted(result, result.Length)
    ensures create_multiset(result, result.Length) == create_multiset(nums1, nums1.Length) + create_multiset(nums2, nums2.Length)
{
    var nums1_length := nums1.Length;
    var nums2_length := nums2.Length;
    result := new int[nums1_length + nums2_length];

    var i := 0;
    var j := 0;

    while (i < nums1_length || j < nums2_length)
        decreases (nums1_length - i) + (nums2_length - j)
        invariant 0 <= i <= nums1_length
        invariant 0 <= j <= nums2_length
        invariant is_sorted(result, i + j)
        invariant forall u, v :: (i <= u < nums1_length && 0 <= v < i + j) ==> nums1[u] >= result[v]
        invariant forall u, v :: (j <= u < nums2_length && 0 <= v < i + j) ==> nums2[u] >= result[v]
        invariant create_multiset(result, i + j) == create_multiset(nums1, i) + create_multiset(nums2, j)
    {
        if (i < nums1_length && (j == nums2_length || nums1[i] <= nums2[j]))
        {
            result[i + j] := nums1[i];
            i := i + 1;
        }
        else {
            result[i + j] := nums2[j];
            j := j + 1;
        }
    } 
}

predicate is_sorted(nums: array<int>, cutoff: int)
    requires 0 <= cutoff <= nums.Length
    reads nums
{
    forall i, j :: 0 <= i < j < cutoff ==> nums[i] <= nums[j]
}

function create_multiset(nums: array<int>, cutoff: int): multiset<int>
    requires 0 <= cutoff <= nums.Length
    reads nums
{
    multiset(nums[..cutoff])
}
