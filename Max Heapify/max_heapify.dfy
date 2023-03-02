
predicate is_max_heap(pq: array<int>)
    reads pq;
{
    forall i :: 1 <= i < pq.Length ==> pq[(i - 1) / 2] >= pq[i]
}

method maxHeapify(pq: array<int>)
    requires pq.Length > 0;
    ensures is_max_heap(pq);
    ensures multiset(pq[..]) == multiset(old(pq[..]));
    modifies pq;
{
    var i := 0;
    while (i < pq.Length)
        invariant 0 <= i <= pq.Length;
        invariant multiset(pq[..]) == multiset(old(pq[..]));
        invariant (0 <= i-1 < pq.Length) ==> (  // look after a sift.
            ((i*2 + 1 < pq.Length) ==> (pq[i-1] >= pq[(i-1)*2 + 1])) && 
            ((i*2 + 2 < pq.Length) ==> (pq[i-1] >= pq[(i-1)*2 + 2]))
        );
        decreases pq.Length - i;
    {
        var left := 2 * i + 1;
        var right := 2 * i + 2;

        var largest:int;
        if (left < pq.Length && pq[left] > pq[i]) {
            largest := left;
        } else {
            largest := i;
        }

        if (right < pq.Length && pq[right] > pq[largest]) {
            largest := right;
        }

        if (largest != i) {
            pq[i], pq[largest] := pq[largest], pq[i];
            maxHeapify(pq);
        }

        i := i + 1;
    }
}