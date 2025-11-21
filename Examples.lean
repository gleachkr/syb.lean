import Syb.Syb

#eval (Typeable.cast true : Option Bool)

#eval (Typeable.cast 1 : Option Bool)

#eval mkT Nat.succ true

#eval mkT Nat.succ ()

#eval mkT Nat.succ 1

abbrev miniverse := [List Nat, Nat, List (List Nat)]

#eval everywhere miniverse (fun {_} => mkT Nat.succ) 1

#eval everywhere miniverse (fun {_} => mkT Nat.succ) ([1,2,3])

#eval everywhere' miniverse (fun {_} => mkT Nat.succ) ([[1,2],[3]])

#eval everything miniverse List.append
  (fun {_} => mkQ [] (λx => if x % 2 == 0 then [x] else []))
  ([[1,2],[3,4]])
