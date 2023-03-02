/*
Credit: João Carlos Pascoal Faria
Source: https://github.com/joaopascoalfariafeup/DafnyProjects/blob/main/PriorityQueue.dfy
*/


class {:autocontracts} PriorityQueue {
	// Private variables
  	var pq: array<int>;
  	var size : nat;

  	const smallest_size := 2;

 
	// Public methods
  	constructor ()
  	{
		pq := new int[smallest_size];
		this.size := 0; 
  	}

	predicate method is_empty()
	{
		size == 0
	}

	method insert(x : int)
		ensures multiset(pq[..size]) == old(multiset(pq[..size])) + multiset{x}
	{
		if size == pq.Length {
			resize();
		}

		pq[size] := x;
		size := size + 1;

		swim();
	}

	method max() returns (x: int)
		requires is_empty() == false
	{
		return pq[0];
	}


	// Private helper methods
	method resize()
		requires size == pq.Length
		ensures pq[..size] == old(pq[..size])
		ensures pq.Length > size
	{
		var temp := pq;
		var new_size := 2 * size;
		if (size < smallest_size)
		{
			new_size := smallest_size;
		}
		pq := new int[new_size];
		forall i | 0 <= i < temp.Length {
			pq[i] := temp[i];
		}
	}


	method {:autocontracts false} swim()
		requires size > 0
		requires is_swimmed(size - 1)
		ensures multiset(pq[..size]) == old(multiset(pq[..size]))
		ensures is_max_heap()
		modifies pq
	{
		var k := size - 1;
		while (k > 0 && pq[k] > pq[(k - 1) / 2])
			invariant 0 <= k <= size - 1
			invariant is_swimmed(k)
			invariant multiset(pq[..size]) == old(multiset(pq[..size]))
		{
			pq[k], pq[(k - 1) / 2] := pq[(k - 1) / 2], pq[k];
			k := (k - 1) / 2;
		}
	}
 
	predicate {:autocontracts false} is_swimmed(k: nat)
		reads pq
		reads this
	{
		(size <= pq.Length) &&
		(forall i :: 1 <= i < size && i != k ==> pq[(i - 1) / 2] >= pq[i]) &&
		(k > 0 ==> forall i :: 1 <= i < size && (i - 1) / 2 == k ==> pq[((i - 1) / 2 - 1) / 2] >= pq[i])
	}

	predicate Valid()
	{
		is_max_heap()
	}
 
	predicate {:autocontracts false} is_max_heap()
		reads pq
		reads this
	{
		(size <= pq.Length) &&
		(forall i :: 1 <= i < size ==> pq[(i - 1) / 2] >= pq[i])
	}
}
