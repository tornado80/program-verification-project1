function square(n: Int) : Int
    ensures result == n * n

method c() {
    var y: Int := 4;
    // @CheckError
    assert 15 == square(y)
}