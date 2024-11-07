method Sum(n: Int) : Int
    requires n >= 0
    ensures result >= -1
    // CheckError
    ensures result == (n == 0 ? -1 : n + (n - 1) * (n - 1))
{
    var sq: Int;
    sq := Square(n - 1);
    match {
        n == 0 => return -1,
        true =>
            // @CheckError
            return n + sq
    }
}

method Square(x: Int) : Int
    ensures result == 2 * x
{
    return 2 * x
}