method counting_bits(n: int) returns (arr: array<int>)
    requires 0 <= n <= 100000
    ensures arr.Length == n + 1
    ensures forall i :: 1 <= i < n + 1 ==> arr[i] == arr[i / 2] + i % 2
{
    var result := new int[n + 1](i => 0);

    var i := 1;
    while (i < n + 1)
        invariant 1 <= i <= n + 1
        invariant forall j :: 1 <= j < i ==> result[j] == result[j / 2] + j % 2
    {
        result[i] := result[i / 2] + i % 2;

        i := i + 1;
    }

    return result;
}
