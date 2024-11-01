method client(n: Int)
    requires n >= 10
{
    var i: Int := n;
    loop
        invariant i >= 0
        // CheckError
        decreases i
    {
        i > 2 =>
            match {
                i == 6 =>
                    i := i + 1;
                    // @CheckError
                    continue
            };
            i := i - 2
    }
}