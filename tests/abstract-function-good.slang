function square(n: Int) : Int
    ensures result == n * n

method c() {
    var y: Int := 4;
    assert 16 == square(y)
}