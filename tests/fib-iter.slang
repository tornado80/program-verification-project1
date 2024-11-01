function fib(n: Int): Int
  requires n >= 0
  ensures result >= 1
{
  n <= 1 ? 1 : fib(n - 1) + fib(n - 2)
}

method lemma(j: Int)
requires j >= 1
ensures fib(j - 1) + fib(j) == fib(j + 1)
{
  assert true
}

method fib_iter(n: Int): Int
  requires n >= 2
  ensures result == fib(n + 1)
{
  match {
    n == 0 => return 1,
    n == 1 => return 1,
  };

  var pprev: Int := 1;
  var prev: Int := 1;
  var j: Int := 1;
  for i in 1..(n + 1)
    invariant j >= 1 && j <= n + 2
    invariant j == i
    invariant fib(j - 1) == pprev
    invariant fib(j) == prev
  {

      var tmp: Int;
      tmp := pprev;
      assert fib(j- 1) == tmp;
      pprev := prev;
      assert fib(j) == pprev;
      prev := tmp + pprev;
      //lemma(j);
      assert fib(j + 1) == prev;
      j := j + 1;
      assert fib(j) == prev;
      assert fib(j - 1) == pprev

  };
  return prev
}