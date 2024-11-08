method client(n: Int)
    requires n >= 0
{
    var counter: Int := 0;
    for i in 0..n
        // @CheckError 
        invariant counter == i
    {
        counter := counter + 1;
        match {
            i == 10 => counter := 0
        }
    };
    assert counter == n
}