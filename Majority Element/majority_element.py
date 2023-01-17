def majority_element(nums):
    count = 0
    candidate = None
    for num in nums:
        if count == 0:
            candidate = num
        count += (1 if num == candidate else -1)
    return candidate


# Example usage:
nums = [2, 2, 1, 1, 1, 2, 2]
print(majority_element(nums)) # Output: 2 (2 appears more than half of the time)
