import Syb.Typeable

/-!
# SYB-ish generic traversal with Type-valued membership

We avoid eliminating from `Prop` into `Type` by reifying list-membership
as a `Type`-valued witness `Member`.  This lets us do the usual
"closed universe" trick: pattern-match the `Member` witness and
select the appropriate `TermOf` instance.

This file also provides a "full family" dictionary construction so
that every type in the family can refer to every other, without
relying on a particular ordering of the list for writing `gmap`s.
-/

/-- Type-level membership witness for a list of types. -/
inductive Member (α : Type u) : List (Type u) → Type (u + 1) where
| head {d}      : Member α (α :: d)
| tail {β d} (m : Member α d) : Member α (β :: d)

/-- Typeclass search for a membership witness. -/
class Among (β : Type u) (d : List (Type u)) extends Typeable β where
  witness : Member β d

instance [Typeable α] : Among α (α :: d) where
  witness := .head

instance [h : Among α d] : Among α (β :: d) where
  witness := .tail h.witness

-- Classes

class TermOf (α : Type u) (d : List (Type u)) extends Among α d where
  gmap  : (∀ {β}, ∀ [Among β d], β → β) → α → α

class Terms (d : List (Type u)) where
  allTerms : ∀ {β}, Member β d → TermOf β d

/-- Lift a `TermOf` instance along list extension. -/
def TermOf.lift (i : TermOf β d) : TermOf β (γ :: d) where
  typeRep := i.typeRep
  typeOf := i.typeOf
  witness := .tail i.witness
  gmap F b := i.gmap (fun {_} => F) b

/-- Promote a singleton-family instance `TermOf α [α]` to any family `d`
    where `α` is a member. Useful for base types whose `gmap` ignores `F`.
    Prefer more informative instances (like containers) when available. -/
def TermOf.ofSingleton [Among α d] (i : TermOf α [α]) : TermOf α d where
  witness := Among.witness
  gmap F a :=
    i.gmap
      (fun {δ} [m : Among δ [α]] => by
        cases m.witness with
        | head => exact F (β := α)
        | tail m' => contradiction
      )
      a

/-- Low-priority instance: lift `TermOf α [α]` to any `d` where `α ∈ d`.
    More specific instances (e.g. for container shapes) should win. -/
instance (priority := 100) [Among α d]
  [i : TermOf α [α]] : TermOf α d :=
  TermOf.ofSingleton i

/-- A dependent vector of `TermOf` instances aligned with a type list. -/
inductive Dict (full : List (Type u)) : List (Type u) → Type (u + 1) where
| nil  : Dict full []
| cons [Among α full] :
    TermOf α full → Dict full d → Dict full (α :: d)

/-- Lookup a `TermOf` by membership witness in a `Dict`. -/
def Dict.lookup (xs : Dict full d) : Member β d → TermOf β full
| .head   => by
  cases xs with
  | cons h _ => simpa using h
| .tail m => by
  cases xs with
  | cons _ t => exact t.lookup m

/-- Build a `Dict full d` by structural recursion on `d`. -/
class TermsAt (full : List (Type u)) (d : List (Type u)) where
  dict : Dict full d

instance : TermsAt full [] where
  dict := Dict.nil

instance [head : TermOf α full] [tail : TermsAt full d]
  : TermsAt full (α :: d) where
  dict := Dict.cons head tail.dict

/-- A "full family" dictionary: for each β ∈ d, we have `TermOf β d`. -/
class TermsFull (d : List (Type u)) where
  dict : Dict d d

/-- Build `TermsFull` from `TermsAt d d`. -/
instance [ta : TermsAt d d] : TermsFull d where
  dict := ta.dict

/-- Use a `TermsFull` dictionary to supply `Terms`. -/
instance [tf : TermsFull d] : Terms d where
  allTerms 
  | m => tf.dict.lookup m
