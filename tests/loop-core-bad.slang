method iter(n: Int): Int
    requires n >= 0
{
    var i: Int := 0;
    loop
        // false: when the loop terminates, i == n + 1
        // @CheckError
        invariant i <= n
    {
        i > n + 1 => break,
        i <= n =>
            i := i + 1
    }
}