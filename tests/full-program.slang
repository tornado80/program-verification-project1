global counter: Int

domain Pair {
  function pair(x: Int, y: Int): Pair
  function fst(x: Pair): Int
  function snd(x: Pair): Int

  axiom forall x: Int :: forall y: Int :: fst(pair(x,y)) == x
  axiom forall x: Int :: forall y: Int :: snd(pair(x,y)) == y
}

method swap(p: Pair): Pair
  ensures fst(result) == snd(p)
  ensures snd(result) == fst(p)
{
  var f: Int := fst(p);
  var s: Int := snd(p);

  return pair(s,f)
}

method sumn(n: Int): Int
  ensures result == n * (n + 1) / 2
{
  match {
    n == 0 =>
      return 0,
    true =>
      var res: Int;
      res := sumn(n - 1);
      return res + n
  }
}

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
    n == 5 => i := 5; acc := 15; break,
    i < n =>
      i := i + 1;
      acc := acc + i
  };
  return acc
}

function fib(n: Int): Int
  requires n >= 0
{
  n <= 1 ? 1 : fib(n - 1) + fib(n - 2)
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