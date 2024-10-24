method client (x: Int) : Int
  requires x > 3
  // @CheckError
  ensures result == x
{
  var i: Int := 0;
  loop
    invariant i <= x
  {
    i == x =>
      return 2,
    true =>
      i := i + 1,
  }
}