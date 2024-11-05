function fib(n: Int): Int
  requires n >= 0
{
  n <= 1 ? 1 : fib(n - 1) + fib(n - 2)
}

method fib_iter(n: Int): Int
  requires n >= 2
  ensures result == fib(n)
{
  match {
    n == 0 => return 1,
    n == 1 => return 1,
  };

  var pprev: Int := 1;
  var prev: Int := 1;
  var i: Int := 1;

  for i in 1..(n) 
    invariant fib(i - 1) == pprev
    invariant fib(i) == prev 
  {
      var tmp: Int;
      tmp := pprev;
      pprev := prev;
      prev := tmp + pprev
  };
  return prev
}