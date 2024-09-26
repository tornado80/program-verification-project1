method client() {
    var x : Int := 2;
    var y : Int := 3;
    y := y + x;
    x := y - x;
    y := y - x;
    assert y == 2 && x == 3
}