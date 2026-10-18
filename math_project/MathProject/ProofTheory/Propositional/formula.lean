inductive Formula where
  | atom : String → Formula -- atomic formula
  | bot : Formula
  | top : Formula
  | imp : Formula → Formula → Formula
  -- | not : Formula → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
deriving Repr, DecidableEq


namespace Formula

def not (A : Formula) : Formula := A.imp bot
def iff (A B : Formula) : Formula := .not (.and (.imp A B) (.imp B A))

@[simp]
def size : Formula → Nat
  | atom _ => 0
  | bot => 0
  | top => 0
  | imp A B => size A + size B + 1
  | and A B => size A + size B + 1
  | or A B => size A + size B + 1

theorem and_eq : A = A' ∧ B = B' ↔ and A B = and A' B' := by
  constructor
  · intro ⟨hA, hB⟩
    rw[hA, hB]
  · intro h
    injection h with hA hB
    exact ⟨hA, hB⟩

theorem or_eq : A = A' ∧ B = B' ↔ or A B = or A' B' := by
  constructor
  · intro ⟨hA, hB⟩
    rw[hA, hB]
  · intro h
    injection h with hA hB
    exact ⟨hA, hB⟩

theorem imp_eq : A = A' ∧ B = B' ↔ imp A B = imp A' B' := by
  constructor
  · intro ⟨hA, hB⟩
    rw[hA, hB]
  · intro h
    injection h with hA hB
    exact ⟨hA, hB⟩

end Formula

local notation "⊤"   => Formula.top
local notation "⊥"   => Formula.bot

open Formula
example : 0 = top.size := by simp
example {φ : Formula} : φ.size = φ.size := by simp
