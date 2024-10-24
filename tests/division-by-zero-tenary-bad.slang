method client() {
    var x : Int;
    // @CheckError
    x := true ? 1 / 0 : 1
}
