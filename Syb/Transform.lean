import Syb.Typeable
import Syb.Instances

unsafe def Typeable._cast [instA : Typeable α] [instB : Typeable β] : α → Option β
  | a => if instA.typeRep == instB.typeRep then .some (unsafeCast a) else .none

@[implemented_by Typeable._cast]
opaque Typeable.cast [instA : Typeable α] [instB : Typeable β] : α → Option β

def mkT [Typeable α] [Typeable β] (f: β → β) : α → α :=
   match Typeable.cast f with
    | .some g => g
    | .none => id

partial def everything (d : List Type)
  [ts : Terms d] [to : TermOf α d] [Typeable α]
  : (∀ {β}, ∀[Among β d], ∀ [Typeable β], β → β) → α → α
| f, a =>
  f (to.gmap (fun {β} [Typeable β] [among : Among β d] (p : β)  =>
      let _ := ts.allTerms among.witness; everything d f p) a)

