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

def mkM [Monad μ] [Typeable α] [Typeable β] [Typeable (μ α)] [Typeable (μ β)]  (f : β → μ β) : α → μ α :=
   match Typeable.cast f with
    | .some g => g
    | .none => pure

-- Among is redundant, but lean has a hard time finding the instance otherwise,
-- so this is arguably more convenient.
abbrev GenericT d := (∀{α}, ∀[Among α d], ∀[TermOf α d], α → α)

/-- Bottom up recursion strategy -/
partial def everywhere (d : List Type)
  [ts : Terms d]  : GenericT d → GenericT d
  | f, _, _, to, a =>
  f (to.gmapT (fun {_} [among : Among _ d] =>
      have := ts.allTerms among.witness; everywhere d f) a)

/-- Top down recursion strategy -/
partial def everywhere' (d : List Type)
  [ts : Terms d] : GenericT d → GenericT d
  | f, _, _, to, a =>
  to.gmapT (fun {_} [among : Among _ d] =>
      have := ts.allTerms among.witness; everywhere' d f) (f a)

abbrev GenericQ d ρ := (∀{α}, ∀[Among α d], ∀[TermOf α d], α → ρ)

partial def everything (d : List Type)
  [ts: Terms d] [Inhabited ρ] : 
  (ρ → ρ → ρ) → GenericQ d ρ → GenericQ d ρ
  | k, f, _, _, to, x =>
  (to.gmapQ (fun {_} [among : Among _ d] =>
      have := ts.allTerms among.witness; everything d k f) x).foldl k (f x)
