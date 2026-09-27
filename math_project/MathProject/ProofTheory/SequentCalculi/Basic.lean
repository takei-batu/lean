-- import Mathlib.Data.Multiset.Basic
import MathProject.ProofTheory.FirstOrder.formula

-- inductive MIC where
-- | m -- minimal
-- | i -- intuitionistic
-- | c -- clasical

-- inductive CtxKind where
-- | list
-- | multiset
-- | set

-- def Antecedent (kind : CtxKind) :=
--   match kind with
--   | .list => List (Formula 𝒮)
--   | .multiset => Multiset (Formula 𝒮)

-- def Succedent (mic : MIC) :=
--   match mic with
--   | .c => List (Formula 𝒮)
--   | _ => Formula 𝒮

-- def Sequent (mic : MIC) :=
--   match mic with
--   | .c => List (Formula 𝒮) → List (Formula 𝒮) -> Type
--   | _ => List (Formula 𝒮) → Formula 𝒮 -> Type

-- class Sequent (mic : MIC) where
--   Provable :
--   match mic with
--   | .c => List (Formula 𝒮) → List (Formula 𝒮) -> Type
--   | _ => List (Formula 𝒮) → Formula 𝒮 -> Type

namespace List

def swap : List α → Nat → Nat → List α
| [], _, _ => [] | a :: xs, 0, 0 => a :: xs
| a :: xs, 0, i + 1 | a :: xs, i + 1, 0 => xs[i]?.getD a :: xs.set i a
| a :: xs, i + 1, j + 1 => a :: swap xs i j

end List
