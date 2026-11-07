import Mathlib.Order.Defs.PartialOrder
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Hom.Basic

/-!
# Structural Label and Mode
-/

/- Structural Label W and C -/
inductive StLabel where
  | W -- Weakening
  | C -- Contraction
deriving DecidableEq, Repr

notation "𝒲" => StLabel.W
notation "𝒞" => StLabel.C

/- σ : M → {{}, {W}, {C}, {W,C}} -/
class HasSigma (M : Type) [Preorder M] where
  sigma : M →o Finset StLabel
abbrev σ {M : Type} [Preorder M] [HasSigma M] : M →o Finset StLabel := HasSigma.sigma

/- LNL Mode
  - `L`: Linear mode
  - `U`: Unrestricted / Non-linear mode
  with the preorder `L ≤ U`.
-/
inductive LNLMode where
  | L : LNLMode
  | U : LNLMode
deriving DecidableEq, Repr

namespace LNLMode

def LNLOrder : LNLMode → LNLMode → Prop := fun m k =>
  match m, k with
  | L, L => True
  | L, U => True
  | U, L => False
  | U, U => True

instance : LE LNLMode where
  le := LNLOrder

instance : Preorder LNLMode where
  le_refl := by
    intro x
    cases x <;> trivial
  le_trans := by
    intro a b c hab hbc
    cases a <;> cases b <;> cases c <;> trivial

theorem L_le_U : LNLMode.L ≤ LNLMode.U := by trivial

instance : HasSigma LNLMode where
  sigma := {
    toFun
      | .L => ∅
      | .U => {𝒲, 𝒞}
    monotone' := by
      intro a b h
      cases a <;> cases b
      · exact Finset.Subset.refl ∅
      · exact Finset.empty_subset {𝒲, 𝒞}
      · contradiction
      · exact Finset.Subset.refl {𝒲, 𝒞}
  }

instance : ToString LNLMode where
  toString
    | .L => "L"
    | .U => "U"

end LNLMode

/- test -/
section Test

open LNLMode StLabel

#eval W

#check σ L
#check σ U

#eval W ∈ σ L
#eval C ∈ σ L
#eval W ∈ σ U
#eval C ∈ σ U

example : σ L ⊆ σ U := σ.monotone LNLMode.L_le_U

example {M : Type} [Preorder M] [HasSigma M] {m k : M} (h : m ≤ k) :
  σ m ⊆ σ k :=
  σ.monotone h

end Test
