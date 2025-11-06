import Syb.Typeable
import Syb.Term

deriving instance Typeable for Nat
deriving instance Typeable for Int
deriving instance Typeable for Bool
deriving instance Typeable for Float
deriving instance Typeable for Float32
deriving instance Typeable for PUnit
deriving instance Typeable for Sum
deriving instance Typeable for Stream
deriving instance Typeable for Option
deriving instance Typeable for List
deriving instance Typeable for Prod
deriving instance Typeable for Array
deriving instance Typeable for Char
deriving instance Typeable for String
deriving instance Typeable for ByteArray
deriving instance Typeable for Dyadic
deriving instance Typeable for Rat
deriving instance Typeable for UInt8
deriving instance Typeable for UInt16
deriving instance Typeable for UInt32
deriving instance Typeable for UInt64
deriving instance Typeable for Fin
deriving instance Typeable for Vector
deriving instance Typeable for BitVec

#eval Typeable.typeOf (Fin.mk 1 (by simp) : Fin 2)
#eval Typeable.typeOf (Vector.mk #[1,2,3] (by simp) : Vector Nat 3)

instance [instA : Typeable α] [instB : Typeable β] : Typeable (α → β) where
  typeOf _ := .app (.app (.typeRep "→") instA.typeRep) instB.typeRep
  typeRep := .app (.app (.typeRep "→") instA.typeRep) instB.typeRep

instance [Among (List α) d] [Among α d] : TermOf (List α) d where
  witness := Among.witness
  gmap
  | _, []      => []
  | f, x :: xs => f x :: f xs

instance : TermOf Nat [Nat] where
  witness := Among.witness
  gmap _ n := n
