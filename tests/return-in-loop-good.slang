method client (x: Int) : Int
  requires x > 3
  ensures result == x
{
  var i: Int := 0;
  loop
    invariant i <= x
  {
    i == x =>
      return i,
    true =>
      i := i + 1,
  }
}