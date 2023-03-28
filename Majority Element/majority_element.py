def majorityElement(nums: list[int]) -> int:
    count = 0
    candidate = None
    for num in nums:
        if count == 0:
            candidate = num
        count += (1 if num == candidate else -1)
    return candidate


nums = [2, 2, 1, 1, 1, 2, 2]
print(majorityElement(nums))
