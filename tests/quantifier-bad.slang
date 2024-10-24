method client() {
    var x : Int;
    x := 1;
    // @CheckError
    assert (forall i : Int :: i + x == i)
}
