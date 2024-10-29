method client()
{
    var i: Int := 30;
    loop
        invariant i <= 30
        // @CheckError
        decreases i
    {
        true =>
            i := i - 1
    }
}