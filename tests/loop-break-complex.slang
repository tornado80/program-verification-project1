method sumn_iter(n: Int): Int
  requires n >= 0
  ensures result == n * (n + 1) / 2
{
  var acc: Int := 0;
  var i: Int := 0;
  loop
    invariant i >= 0 && i <= n
    invariant acc == i * (i + 1) / 2
    invariant broke ==> i == 5 && n == 5
  {
    n == 5 => i := 5; acc := 15; assert acc == i * (i + 1) / 2; break,
    i < n =>
      i := i + 1;
      acc := acc + i;
      assert acc == i * (i + 1) / 2
  };

  return acc
}