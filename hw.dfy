predicate sorted_slice(a: array<int>, start: int, end: int)
   requires 0 <= start < a.Length
   requires start <= end < a.Length
   reads a
{
   forall i, j :: start <= i <= j < end ==> a[i] <= a[j] 
}
predicate merged(a1: seq<int>,a2 : seq<int>,b: array<int>)

   reads b
{
   forall i,j::exists j1,j2 ::( 0 <= i < |a1| && 0 <= j < |a2|&&0<=j1<b.Length&&0<=j2<b.Length ==> a1[i]==b[j1]&& a2[j]==b[j2] )
   
}
predicate sorted_seq(a: seq<int>)
{
   forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
}
method mergeSimple(a1: seq<int>, a2: seq<int>, start: int, end: int, b: array<int>)
    modifies b
    requires sorted_seq(a1) && sorted_seq(a2);
    requires 0 <= start <= end<b.Length;
    requires (|a1|+|a2|) ==(end-start)==b.Length;
    ensures merged(a1,a2,b);
    ensures sorted_slice(b, start, end);
{
    var i := 0;var j := 0;var k := start;
    while (i < |a1| && j < |a2|)
    {
        if (i<|a1|&&((j>=|a2| || a1[i]<=a2[j])))
        {
            
            b[k]:=a1[i];
            i:=i+1;
        }
        else {
            
            b[k]:=a2[j];
            j:=j+1;
        }
        
        k:=k+1;
    }
      while (i < |a1|)
      invariant k<=end
  {
    b[k] := a1[i];
    i := i + 1;
    k := k + 1;
  }
    while (j < |a2|)
    
  {
    b[k] := a2[j];
    j := j+1;
    k := k + 1;
  }

}