method sumn(n: Int): Int
    requires n >= 0
    ensures result == n * (n + 1)/2
    decreases n
{
    match {
        n == 0 =>
            return 0,
        true =>
            var res: Int;
            res := sumn(n - 1);
            return res + n
    };
    assert false // not reachable, passes
}