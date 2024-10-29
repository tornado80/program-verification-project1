method client(n: Int)
    requires n >= 10
    requires n % 2 == 0
{
    var i: Int := 0;
    loop
        invariant i >= 0
        // @CheckError
        invariant i % 2 == 0
    {
        i < n =>
            match {
                i == 6 =>
                    i := i + 1;
                    continue
            };
            i := i + 2
    }
}