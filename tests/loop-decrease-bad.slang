method client(n: Int)
    requires n >= 0
{
    var counter: Int := n;
    var i: Int := 0;
    var j: Int := 0;
    loop
        decreases counter + j
    {
        i == 10 && n >= 20 =>
            counter := counter - 10;
            i := i + 10,
        // @CheckError
        i < n && i >= 0 => 
            counter := counter - 1;
            j := j + 1;
            i := i + 1
    }
}