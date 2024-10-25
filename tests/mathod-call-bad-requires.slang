method sum(n: Int) : Int
    // @CheckError
    requires n > 0
    ensures result == 9
{
    var y: Int := 7;
    return y + 2
}

method client() {
    var z: Int;
    z := sum(-1);
    assert z == 9
}