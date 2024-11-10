method main () {
    var x : Int ;
    var y : Int ;
    var z : Int ;
    assume x >= 0 && y >= 0;
    z := x - y ;
    match {
        z < 0 =>
            z := z + y ;
            z := z + 2 * x,
        true =>
            z := z - x ;
            z := z + 4 * y,
    };
    // @CheckError
    assert (z < 0 && z == x - y + 2 * x) || (z >= 0 && z == x - y + 4 * y);
    assert (z < 0 && z == x - y + y + 2 * x) || (z >= 0 && z == x - y - x + 4 * y)
}