method unique(s: seq<int>) returns (result: seq<int>) 
    requires is_sorted(s)
    requires 1 <= |s| <= 30000
    requires forall i :: 0 <= i < |s| ==> -100 <= s[i] <= 100
    ensures is_sorted_and_distinct(result)
    ensures forall i :: i in s <==> i in result
{
        var previous := s[0];
        result := [s[0]];

        var i := 1;
        while i < |s|
            invariant 0 <= i <= |s|
            invariant |result| >= 1;
            invariant previous in s[0..i];   
            invariant previous == result[|result| - 1];
            invariant is_sorted_and_distinct(result)
            invariant forall j :: j in s[0..i] <==> j in result
        {
            if (previous != s[i])
            { 
                result := result + [s[i]];
                previous := s[i];
            }

            i := i + 1;
        }
}


// Helper predicate
predicate is_sorted(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate is_sorted_and_distinct(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
}
