method client (x: Int)
  requires x > 3
{
    var y: Int := 4000;

    match {
      x == 2 =>
        y := 1000,
      x == 3 =>
        y := 2000
    };
    assert y != 1000 && y != 2000
}