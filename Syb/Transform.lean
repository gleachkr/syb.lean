import Syb.Typeable
import Syb.Instances

unsafe def Typeable._cast [instA : Typeable α] [instB : Typeable β] : α → Option β
  | a => if instA.typeRep == instB.typeRep then .some (unsafeCast a) else .none

@[implemented_by Typeable._cast]
opaque Typeable.cast [Typeable α] [Typeable β] : α → Option β

def mkT [Typeable α] [Typeable β] (f: β → β) : α → α :=
   match Typeable.cast f with
    | .some g => g
    | .none => id

def mkQ [Typeable α] [Typeable β]  (r : γ) (q : β → γ) (a : α) : γ :=
   match Typeable.cast a with
    | .some b => q b
    | .none => r

/-- Bottom up recursion strategy -/
partial def everything (d : List Type)
  [ts : Terms d] [to : TermOf α d] : (∀ {β}, ∀[Among β d], β → β) → α → α
| f, a =>
  f (to.gmap (fun {_} [among : Among _ d] =>
      have := ts.allTerms among.witness; everything d f) a)

/-- Top down recursion strategy -/
def everything' (d : List Type)
  [ts : Terms d] [to : TermOf α d] : (∀ {β}, ∀[Among β d], β → β) → α → α
| f, a =>
  to.gmap (fun {_} [among : Among _ d] =>
      have := ts.allTerms among.witness; everything d f) (f a)
