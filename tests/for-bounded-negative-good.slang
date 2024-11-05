method client() {
    var acc: Int := 0;
    for i in -5..2 {
        acc := acc + i
    };
    assert acc == -14
}