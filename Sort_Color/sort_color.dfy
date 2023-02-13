datatype Color = Red | White | Blue

method sort_colors(nums: array<Color>)
    requires 1 <= nums.Length <= 300
    ensures multiset(nums[..]) == multiset(old(nums[..]))
    ensures forall i, j :: 0 <= i < j < nums.Length ==> nums[i] == Red || nums[i] == nums[j] || nums[j] == Blue
    modifies nums
{
    var red := 0;
    var white := 0;
    var blue := nums.Length;

    while (white < blue)
        invariant 0 <= red <= white <= blue <= nums.Length
        invariant multiset(nums[..]) == multiset(old(nums[..]))
        invariant forall i :: 0 <= i < red ==> nums[i] == Red
        invariant forall i :: red <= i < white ==> nums[i] == White
        invariant forall i :: blue <= i < nums.Length ==> nums[i] == Blue
    {
        if (nums[white] == Red)
        {
            nums[red], nums[white] := nums[white], nums[red];
            red := red + 1;
            white := white + 1;
        }
        else if (nums[white] == White)
        {
            white := white + 1;
        }
        else if (nums[white] == Blue) {
            nums[blue - 1], nums[white] := nums[white], nums[blue - 1];
            blue := blue - 1;
        }
    }
}
