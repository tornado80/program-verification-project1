global counter : Int

method inc()
    modifies counter
    ensures counter == old(counter) + 1
{
    counter := counter + 1
}

method client6()
    modifies counter
{
    counter := 0;

    assert counter == 0;
    inc(); // modifies counter without returning a value
    assert counter == 1;
    inc();
    assert counter == 2;
    inc();
    assert counter == 3
}