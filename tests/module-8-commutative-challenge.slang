domain X {
    function X(n: Int, m: Int): Int
    axiom
        forall n: Int :: forall m: Int ::
            (n >= 0 && m >= 0) ==> X(n, m) == (m == 0 ? 0 : n + X(n, m - 1))
}


method lemma1(n: Int)
    requires n >= 0
    ensures X(0, n) == X(n, 0)
    decreases n
{

    match {
        n == 0 => var x: Int,
        true => lemma1(n - 1)
    }
}

method lemma2(m: Int)
    requires m >= 0
    ensures X(1, m) == m
    decreases m
{
    match {
        m == 0 => var x: Int,
        true => lemma2(m - 1)
    }
}

method lemma3(n: Int, m: Int)
    requires n > 0 && m >= 0
    ensures X(n, m) == X(1, m) + X(n - 1, m)
    decreases m
{

    match {
        m == 0 => var x: Int,
        true =>
        lemma3(n, m - 1);
        assert X(n, m - 1) == X(1, m - 1) + X(n - 1, m - 1)
    }

}

method lemma(n: Int, m: Int)
    requires n >= 0 && m >= 0
    ensures X(n, m) == X(m, n)
    decreases n
{
    match {
        n == 0 =>
        lemma1(m),
        true =>
        assert X(m, n) == m + X(m, n - 1);
        lemma(n - 1, m);
        assert X(n - 1, m) == X(m, n - 1);

        assert X(m, n) == m + X(n - 1, m);

        lemma2(m);

        assert X(m, n) == X(1, m) + X(n - 1, m);

        lemma3(n, m);

        assert X(n, m) == X(1, m) + X(n - 1, m);

        assert X(m, n) == X(n, m)
    }

}