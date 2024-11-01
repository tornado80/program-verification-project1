method client() {
    var x: Int := 2;
    assert x == 2;
    // @CheckError
    var x: Int;
    assume x == 2
}