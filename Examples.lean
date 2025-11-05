import Syb.Syb

#eval (Typeable.cast true : Option Bool)

#eval (Typeable.cast 1 : Option Bool)

#eval mkT Nat.succ true

#eval mkT Nat.succ ()

#eval mkT Nat.succ 1

abbrev miniverse := [List Nat, Nat, List (List Nat)]

#eval everything miniverse (fun {_} => mkT Nat.succ) 1

#eval everything miniverse (fun {_} => mkT Nat.succ) ([1,2,3])

#eval everything miniverse (fun {_} => mkT Nat.succ) ([[1,2],[3]])
