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
    assert z <= 3 * x && z <= 3 * y && ( z == 3 * x || z == 3 * y )
}