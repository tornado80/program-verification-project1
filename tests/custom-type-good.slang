domain Pair {
  function pair(x: Int, y: Int): Pair
  function fst(x: Pair): Int
  function snd(x: Pair): Int

  axiom forall x: Int :: forall y: Int :: fst(pair(x,y)) == x
  axiom forall x: Int :: forall y: Int :: snd(pair(x,y)) == y
}

method client(x: Int, y: Int)
{
  var xy: Pair := pair(x,y);
  assert fst(xy) == x;
  assert snd(xy) == y
}

method swap(p: Pair): Pair
  ensures fst(result) == snd(p)
  ensures snd(result) == fst(p)
{
  var f: Int := fst(p);
  var s: Int := snd(p);

  return pair(s,f)
}