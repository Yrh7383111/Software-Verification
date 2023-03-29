def removeDuplicates(nums: list[int]) -> list[int]:
    i = nums[0]
    result = []

    for num in nums:
        if i != nums:
            result.append(i)
            i = num

    return result
