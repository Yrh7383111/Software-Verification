def sortColors(self, nums: list[int]) -> None:
    i = 0
    j = len(nums) - 1
    k = 0
    while k <= j:
        if nums[k] == 0:
            nums[i], nums[k] = nums[k], nums[i]
            i += 1
            k += 1
        elif nums[k] == 2:
            nums[j], nums[k] = nums[k], nums[j]
            j -= 1
        else:
            k += 1
