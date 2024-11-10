method client(j: Int) 
    requires j < 5 && j >= 0
{
    var n: Int := 5;
    var i: Int := 0;
    loop 
        invariant i >= 0 && i <= n
        invariant j >= i
        invariant j <= n
    {
        i == j => break,
        i < n => i := i + 1
    };
    assert i == j
}