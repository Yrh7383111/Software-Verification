def max_heapify(arr: list[int]) -> list[int]:
    n = len(arr)
    for i in range(n - 1, -1, -1):
        swim_up(arr, i)

def swim_up(arr, i):
    while i > 0 and arr[i] > arr[(i - 1) // 2]:
        arr[i], arr[(i - 1) // 2] = arr[(i - 1) // 2], arr[i]
        i = (i - 1) // 2
        
arr = [4, 10, 3, 5, 1]
max_heapify(arr)
print(arr)
