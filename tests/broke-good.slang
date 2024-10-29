method client()
{
    var i: Int := 30;
    loop
        invariant i >= 15
        invariant i <= 30
        invariant broke ==> i == 15
        decreases i
    {
        true => 
            match {
                i == 15 => break
            };
            i := i - 1
    };
    assert i == 15;
    // @CheckError
    assert false
}