method client(n: Int): Int
    requires n >= 0
    ensures result == n * (n + 1) / 2
{
    var acc: Int := 0;
    var i: Int := -10;
    loop
        invariant i <= n
        invariant i < 0 ==> acc == 0
        invariant i >= 0 ==> acc == i * (i + 1) / 2
    {
        i < n =>
            i := i + 1;
            match {
                i < 0 =>
                    continue,
            };
            acc := acc + i

    };
    assert i == n;
    assert acc == n * (n + 1) / 2
}