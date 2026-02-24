import Syb.Syb

#eval (Typeable.cast true : Option Bool)

#eval (Typeable.cast 1 : Option Bool)

#eval mkT Nat.succ true

#eval mkT Nat.succ ()

abbrev miniverse : List Type :=
  [List Nat, Nat, List (List Nat), Bool]

/--
A base query that returns `false` for all types.
-/
def qFalse : GenericQ miniverse Bool :=
  fun {α} (_ : Among α miniverse) (_ : TermOf α miniverse) _ =>
    false

/--
A query that is `true` on even `Nat`s, and `false` on everything else.
-/
def qEvenNat : GenericQ miniverse Bool :=
  extQ miniverse qFalse (fun (n : Nat) => n % 2 == 0)

#eval qEvenNat (α := Nat) 2
#eval qEvenNat (α := Bool) true
#eval qEvenNat (α := List Nat) ([1, 2, 3] : List Nat)

/--
A query that counts `Nat`s as 1, counts `Bool`s as 100, and returns 0 for all
other types. This demonstrates multiple `extQ` overrides.
-/
def qWeighted : GenericQ miniverse (Nat : Type) :=
  let q0 : GenericQ miniverse Nat :=
    fun {α} (_ : Among α miniverse) (_ : TermOf α miniverse) _ =>
      0
  let q1 : FullyGenericQ miniverse Nat :=
    extQ miniverse q0 (fun (_ : Nat) => 1)
  extQ miniverse q1 (fun (_ : Bool) => 100)

#eval qWeighted (α := Nat) 3
#eval qWeighted (α := Bool) false
#eval qWeighted (α := List Nat) ([10, 20] : List Nat)

/--
Increment `Nat`s everywhere in a term, leaving everything else untouched.
-/
def incr : GenericT miniverse :=
  fun {α} (_ : Among α miniverse) (_ : TermOf α miniverse) =>
    mkT Nat.succ

#eval everywhere miniverse incr 1
#eval everywhere miniverse incr ([1, 2, 3] : List Nat)

/--
Use `extT` to add a second transformation case: negate `Bool`s.
-/
def incrAndNot : FullyGenericT miniverse :=
  extT miniverse incr (fun (b : Bool) => !b)

#eval incrAndNot (α := Nat) 4
#eval incrAndNot (α := Bool) true
#eval everywhere miniverse incrAndNot ([[1, 2], [3]] : List (List Nat))

#eval everything miniverse Nat.add
  (fun {α} (_ : Among α miniverse) (_ : TermOf α miniverse) =>
    let q0 : GenericQ miniverse Nat :=
      fun {α} (_ : Among α miniverse) (_ : TermOf α miniverse) _ =>
        0
    extQ miniverse q0 (fun (n : Nat) => n))
  ([[1, 2], [3, 4]] : List (List Nat))
