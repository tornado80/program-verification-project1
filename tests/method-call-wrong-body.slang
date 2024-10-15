method Sum(n: Int) : Int 
    requires n >= 0
    ensures result == n == 0 ? -1 : n + (n - 1) * (n - 1)
{
    match {
        n == 0 => return -1,
        true => return n + Square(n - 1)
    }
}

method Sqaure(x: Int) : Int 
    // @CheckError
    ensures result == x * x
{
    return 2 * x
}