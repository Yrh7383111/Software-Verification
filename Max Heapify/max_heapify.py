# Max-heapify Generated by CoPilot

#-------------------------------------------------------------------------------
# Formal Specifications:
#-------------------------------------------------------------------------------
# requires arr is a list of distinct integers
# ensures that the max-heap property is maintained

#-------------------------------------------------------------------------------
# Copilot Code: (starts)
#-------------------------------------------------------------------------------

def maxHeapify(arr: list) -> list:
    for i in range(len(arr)):
        left = 2 * i + 1
        right = 2 * i + 2
        if left < len(arr) and arr[left] > arr[i]:
            largest = left
        else:
            largest = i
        if right < len(arr) and arr[right] > arr[largest]:
            largest = right
        if largest != i:
            arr[i], arr[largest] = arr[largest], arr[i]
            maxHeapify(arr)
    return arr

#-------------------------------------------------------------------------------
# Copilot Code: (ends)
#-------------------------------------------------------------------------------

