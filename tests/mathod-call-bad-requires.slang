method sum(n: Int) : Int
    // CheckError
    requires n > 0
    requires n > -5
    ensures result == 9
{
    var y: Int := 7;
    return y + 2
}

method client() {
    var z: Int;
    // @CheckError
    z := sum(-1);
    assert z == 9
}