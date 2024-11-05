method client() {
    var acc: Int := 0;
    for i in -1..5 {
        acc := i
    };
    // @CheckError
    assert acc == 5
}