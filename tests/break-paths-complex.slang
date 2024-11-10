method client(n: Int)
{
    var i: Int := 30;
    var j: Int := i;
    loop
        invariant i >= 15
        invariant i <= 30
        decreases i
    {
        i == 15 =>
            match {
                n % 2 == 0 =>
                    j := -1;
                    break,
                n % 2 == 1 =>
                    j := -2;
                    break
            };
            i := i - 1,
        true =>
            i := i - 1
    };

    match {
        n % 2 == 0 =>
            assert j == -1,
        n % 2 == 1 =>
            // This fails because j is actually -2
            // @CheckError
            assert j == -3,
    };

    // this is reachable so should also fail
    // @CheckError
    assert false
}