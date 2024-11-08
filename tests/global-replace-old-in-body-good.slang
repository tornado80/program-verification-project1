global x: Int := 2

method c()
modifies x

{
    x := x + 1;
    assert x == old(x) + 1
}