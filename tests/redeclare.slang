method client() {
    var x: Int := 2;
    assert x == 2;
    var x: Int;
    assume x == 2;
    var x: Int;
    // @CheckError
    assert x == 2
}