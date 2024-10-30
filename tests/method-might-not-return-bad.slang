method client2(n: Int) : Int {
    return 4
}

// @CheckError
method client(n: Int) : Int {
    match {
         n == 1 => return 2,
    }
}