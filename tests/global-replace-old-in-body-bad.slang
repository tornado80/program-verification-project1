global x: Int := 2

method c()
modifies x

{
    x := x + 1;
    // @CheckError
    assert x == old(x) + 2
}