method client() {
    var x: Int;
    // @CheckError
    x := x / ((x / x) - 1)
}