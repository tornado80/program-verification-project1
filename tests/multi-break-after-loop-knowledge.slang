method client(x: Int)
requires x >= 15 && x <= 30
{
    var i: Int := x;
    loop
        invariant i >= 15
        invariant i <= 30
        invariant i <= x
        invariant x < 20 && x > 16 ==> i >= 17
        invariant x >= 20 ==> i >= 20
        invariant broke && x <= 16 ==> i == 15
        invariant broke && x < 20 && x > 16 ==> i == 17
        invariant broke && x >= 20 ==> i == 20
        decreases i
    {
        i == 20 => break,
        true =>
            match {
                i == 15 => break,
                i == 17 => break
            };
            i := i - 1

    };
    var y : Int;
    assume y != 17 && y != 20 && y != 15;
    assert i != y;
    assert i == 17 || i == 20 || i == 15;
    // @CheckError
    assert false
}