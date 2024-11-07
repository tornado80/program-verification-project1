method find_divisor(product: Int) : Int
    requires product >= 2
    ensures result >= 2 && result <= product
    ensures forall x: Int :: x >= 2 && x < result ==> product % x != 0
{
    var i: Int := 2;
    loop
        invariant i >= 2 && i <= product
        invariant forall x: Int :: x >= 2 && x < i ==> product % x != 0
    {
        i < product =>
            match {
                product % i == 0 =>
                    break
            };
            i := i + 1

    };
    return i
}