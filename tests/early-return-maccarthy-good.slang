method M(n: Int) : Int
  ensures (n > 100 ==> result == n - 10) && (n <= 100 ==> result == 91)
  decreases 101 < n ? 0 : 101 - n
{
  match {
    n > 100 =>
      return n - 10,
    true =>
      var r: Int;
      r := M(n + 11);
      r := M(r);
      return r
  };
  assert false
}