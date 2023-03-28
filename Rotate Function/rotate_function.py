def maxRotateFunction(nums: list[int]) -> int:
    if not nums:
        return 0
    n = len(nums)
    max_sum = -float('inf')
    for i in range(n):
        sum = 0
        for j in range(n):
            sum += j * nums[(i + j) % n]
        max_sum = max(max_sum, sum)
    return max_sum
