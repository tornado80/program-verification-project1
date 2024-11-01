function fac(n: Int): Int
    requires n >= 0
    ensures result > 0 // Postcondition may not hold
{
    // @CheckError
    n == 0 ? 0 : n * fac(n + 1) // Precondition not satisfied
}