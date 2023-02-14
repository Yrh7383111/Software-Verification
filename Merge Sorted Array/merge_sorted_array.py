def merge(self, nums1: list[int], m: int, nums2: list[int], n: int) -> list[int]:
    i = 0
    j = 0

    result = []
    while i < m or j < n:
        if i < len(nums1) and (j == len(nums2) or nums1[i] <= nums2[j]):
            result[i + j] = nums1[i]
            i += 1
        else:
            result[i + j] = nums2[j]
            j += 1

    return result
