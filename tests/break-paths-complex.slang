method client(n: Int)
{
    var i: Int := 30;
    var j: Int := i;
    loop
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
        n % 2 == 2 =>
            assert false
    };

    // this is reachable so should also fail
    // @CheckError
    assert false
}