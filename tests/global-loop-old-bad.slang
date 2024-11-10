global i: Int

method sum(n: Int)
modifies i
requires n >= 0
ensures i == old(i) + n
{
    var j: Int := 0;
    assert j <= n;
    loop
        invariant j >= 0 && j <= n
        // @CheckError
        invariant i == old(i) + j
    {
        j < n =>
            i := i;
            j := j + 1
    }

}


method c()
modifies i
{
    i := 0;
    sum(5);
    assert i == 5
}