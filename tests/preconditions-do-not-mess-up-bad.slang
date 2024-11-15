method a(n: Int)
    requires n >= 0
{
    assert true
}

method b(n: Int)
    requires n < 0
{
    // @CheckError
    assert false
}