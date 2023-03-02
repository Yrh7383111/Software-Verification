method max_heapify(pq: array<int>)
    requires pq.Length > 0
    ensures multiset(pq[..]) == old(multiset(pq[..]))
    ensures is_max_heap(pq)
    modifies pq
{
    var i := pq.Length - 1;
    while (i >= 0)
        invariant -1 <= i <= pq.Length - 1
        invariant multiset(pq[..]) == old(multiset(pq[..]))
    {
        swim(pq, i);
        i := i - 1;
    }
}

method swim(pq: array<int>, k: nat)
    requires pq.Length > 0
    requires 0 <= k <= pq.Length - 1
    requires is_swimmed(pq, pq.Length - 1)
    ensures multiset(pq[..]) == old(multiset(pq[..]))
    modifies pq
{
    var i := k;
    while (i > 0 && pq[i] > pq[(i - 1) / 2])
        invariant 0 <= i <= k
        invariant multiset(pq[..]) == old(multiset(pq[..]))
        invariant is_swimmed(pq, i)
    {
        pq[i], pq[(i - 1) / 2] := pq[(i - 1) / 2], pq[i];
        i := (i - 1) / 2;
    }
}

predicate is_swimmed(pq: array<int>, k: nat)
    reads pq
{
    (forall i :: 1 <= i < pq.Length && i != k ==> pq[(i - 1) / 2] >= pq[i]) &&
	(k > 0 ==> forall i :: 1 <= i < pq.Length && (i - 1) / 2 == k ==> pq[((i - 1) / 2 - 1) / 2] >= pq[i])
}

predicate is_max_heap(pq: array<int>)
    reads pq
{
    forall i :: 1 <= i < pq.Length ==> pq[(i - 1) / 2] >= pq[i]
}
