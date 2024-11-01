global g: Int

method inc()
    ensures g == old(g) + 1
    modifies g
{
        g := g + 1
}

method c()
{
    // @CheckError
    inc()
}