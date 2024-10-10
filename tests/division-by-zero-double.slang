method client() {
    var x: Int;
    // @CheckError
    x := x / ((2*x / x) - 1);
    // @CheckError
    x := x / ((x / x) - 1)
}