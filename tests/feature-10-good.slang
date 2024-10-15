method sumn(n: Int): Int
    requires n >= 0
    ensures result == 0 || result == n + 5
{
    match {
        n == 0 => 
            return 0,
        true => 
            var res: Int;
            res := 5;
            return res + n
    };
    assert false // not reachable, passes
}