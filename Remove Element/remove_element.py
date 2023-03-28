def removeElement(nums: list[int], val: int) -> int:
    i = 0
    end = len(nums) - 1

    while i <= end:
        if nums[i] == val:
            if nums[end] == val:
                end -= 1
            else:
                nums[i] = nums[end]
                i += 1
                end -= 1
        else:
            i += 1
    
    return i