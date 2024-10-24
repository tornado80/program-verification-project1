method client() {
    var x : Int;
    x := 0;
    // @CheckError
    assert (forall i : Int :: i / x == i)
}
