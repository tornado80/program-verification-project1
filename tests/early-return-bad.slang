method M(n: Int) : Int
  ensures n == 1 ==> result == 2
  ensures n != 1 ==> result == 3
{
  match {
    n == 1 =>
        // @CheckError
        return 9
  };
  return 3
}