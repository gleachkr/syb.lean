import Syb.Typeable
import Syb.Instances

universe u v

unsafe def Typeable._cast [instA : Typeable α] [instB : Typeable β] : α → Option β
  | a => if instA.typeRep == instB.typeRep then .some (unsafeCast a) else .none

@[implemented_by Typeable._cast]
opaque Typeable.cast [Typeable α] [Typeable β] : α → Option β

def mkT [Typeable α] [Typeable β] (f: β → β) : α → α :=
   match Typeable.cast f with
    | .some g => g
    | .none => id

def mkQ [Typeable α] [Typeable β]  (default : γ) (q : β → γ) (a : α) : γ :=
   match Typeable.cast a with
    | .some b => q b
    | .none => default

def mkM [Monad μ] [Typeable α] [Typeable β] [Typeable (μ α)]
  [Typeable (μ β)] (f : β → μ β) : α → μ α :=
  match Typeable.cast f with
  | .some g => g
  | .none => pure


-- Among is redundant, but lean has a hard time finding the instance otherwise,
-- so this is arguably more convenient.

abbrev FullyGenericT (d : List (Type u)) :=
  ∀ {α : Type u}, ∀ [Among α d], ∀ [TermOf α d], α → α

abbrev FullyGenericQ (d : List (Type u)) (ρ : Type v) :=
  ∀ {α : Type u}, ∀ [Among α d], ∀ [TermOf α d], α → ρ

abbrev FullyGenericM (d : List (Type u)) (μ : Type u → Type v) :=
  ∀ {α : Type u}, ∀ [Among α d], ∀ [TermOf α d], ∀[Typeable (μ α)], α → μ α

abbrev GenericT := FullyGenericT.{_,0}

abbrev GenericQ := FullyGenericQ.{_,_,0}

abbrev GenericM := FullyGenericM.{_,_,0}

/--
`extQ` adds a type-specific "override" to a generic query.

This mirrors SYB's `extQ`:

  (q `extQ` f) a = case cast a of
    Just b  -> f b
    Nothing -> q a

In Lean terms, `q` is a generic query `∀ {α}, α → ρ` (under the usual SYB
constraints), and `f` is a type-specific case `β → ρ`.
-/
def extQ {β : Type u} {ρ : Type v} (d : List (Type u))
  (q : FullyGenericQ d ρ) [Typeable β] (f : β → ρ) : FullyGenericQ d ρ :=
  fun {α} [Among α d] [TermOf α d] a =>
    match Typeable.cast a with
    | some b => f b
    | none => q a

/--
`extT` adds a type-specific "override" to a generic transformation.

This is the analogous combinator for `mkT`-style generic transforms.
-/
def extT (d : List (Type u))
  (t : FullyGenericT d) [Typeable β] (f : β → β) : FullyGenericT d :=
  fun {α} [Among α d] [TermOf α d] a =>
    match Typeable.cast a with
    | some b => (Typeable.cast (f b)).getD a
    | none => t a

/--
`extM` adds a type-specific "override" to a generic monadic transformation.

This is the monadic analogue of `extT`.
-/
def extM [Monad μ] (d : List (Type u))
  (t : FullyGenericM d μ) [Typeable β] [Typeable (μ β)] (f : β → μ β) : FullyGenericM d μ :=
  fun {α} [Among α d] [TermOf α d] [Typeable (μ α)] a =>
    match Typeable.cast a with
    | some b =>
      match Typeable.cast (f b) with
      | some ma => ma
      | none => t a
    | none => t a

/-- Bottom up recursion strategy -/
partial def everywhere (d : List (Type u))
  [ts : Terms d]  : FullyGenericT d → FullyGenericT d
  | f, _, _, to, a =>
  f (to.gmapT (fun {_} [among : Among _ d] =>
      have := ts.allTerms among.witness; everywhere d f) a)

/-- Top down recursion strategy -/
partial def everywhere' (d : List (Type u))
  [ts : Terms d] : FullyGenericT d → FullyGenericT d
  | f, _, _, to, a =>
  to.gmapT (fun {_} [among : Among _ d] =>
      have := ts.allTerms among.witness; everywhere' d f) (f a)

partial def everything (d : List (Type u))
  [ts : Terms d] [Inhabited ρ] :
  (ρ → ρ → ρ) → FullyGenericQ d ρ → FullyGenericQ d ρ
  | k, f, _, _, to, x =>
  (to.gmapQ (fun {_} [among : Among _ d] =>
      have := ts.allTerms among.witness; everything d k f) x).foldl k (f x)

partial def everywhereBut (d : List (Type u))
  [ts : Terms d]  : FullyGenericQ d Bool → FullyGenericT d → FullyGenericT d
  | q, f, _, _, to, a =>
    if q a 
    then a
    else f (to.gmapT (fun {_} [among : Among _ d] =>
      have := ts.allTerms among.witness; everywhereBut d q f) a)
