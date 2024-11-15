// uninterpreted function (do not change)
function F(x: Int): Int

// TODO: implement
function sumUp(n: Int, m: Int): Int
{
    n >= m ? 0 : (F(n) + sumUp(n + 1, m))
}

// TODO: implement
function sumDown(n: Int, m: Int): Int
{
    n >= m ? 0 : (F(m - 1) + sumUp(n, m - 1))
}

// TODO: implement
method lemmaSameSum(n: Int, m: Int)
   requires n <= m
   ensures sumUp(n,m) == sumDown(n,m)
   decreases m - n
{
    match {
        m == n => assert true,
        m == n + 1 => assert true,
        true =>
            lemmaSameSum(n, m - 1);
            lemmaSameSum(n + 1, m - 1);
            lemmaSameSum(n + 1, m)
    }
}

// TODO: verify this
method client(n: Int, m: Int) : Int
    ensures result == sumUp(n, m)
{
    // you can assert n <= m here although you shouldn't
   var sum: Int := 0;
   var i: Int := m;
   loop
        invariant i <= m
        // @CheckError
        invariant i >= n
        invariant sum == sumDown(i, m)
   {
        i != n =>
            i := i - 1;
            sum := sum + F(i)
   };
   lemmaSameSum(n, m);
   return sum
}