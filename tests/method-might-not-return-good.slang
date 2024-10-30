method client2(n: Int) : Int {
    return 4
}

method client(n: Int) : Int {
    match {
         n == 1 => return 2,
         true => return 3
    }
}