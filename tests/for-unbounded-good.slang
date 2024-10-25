method client(n: Int): Int
    requires n >= 0
    ensures result == n * (n + 1) / 2
{
    var acc: Int := 0;
    for i in 1..(n + 1)
        invariant acc == i * (i - 1) / 2
    {
        acc := acc + i
    };
    return acc
}