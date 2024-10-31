method main() {
    var x: Int;
    x := 35;
    var y: Int;
    x := y;
    // @CheckError
    assert x == 35
}