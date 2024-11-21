get Nat/Zero     (List/Nil)       = *
get Nat/Zero     (List/Cons x xs) = x
get (Nat/Succ n) (List/Cons x xs) = (get n xs)
get (Nat/Succ n) (List/Nil)       = *

main =
  let a = [
    @x @y @z @w x
    @x @y @z @w y
    @x @y @z @w z
    @x @y @z @w w
  ]
  @p (p
    (get Nat/Zero a)
    (get (Nat/Succ Nat/Zero) a)
    (get (Nat/Succ (Nat/Succ Nat/Zero)) a)
  )
