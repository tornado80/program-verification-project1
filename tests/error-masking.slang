method client() {
    var x: Int;
    // @CheckError
    assert x == 2;
    assert x > 0;
    assert x + 2 == 4;
    var y: Int;
    // @CheckError
    assert y > 0;
    // @CheckError
    assert y == 2
}