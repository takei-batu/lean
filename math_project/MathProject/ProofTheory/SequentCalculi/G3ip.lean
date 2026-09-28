import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Data.Multiset.AddSub
import MathProject.ProofTheory.Propositional.formula

namespace G3ip

open Formula

/-- G3ip for base of inversion system -/
inductive Derivation : Multiset (Formula) → Formula -> Type where
| Id :
  (h : atom p ∈ Γ := by aesop) →
  Derivation Γ (atom p)
| BotL (C : Formula) :
  (h : bot ∈ Γ := by aesop) →
  Derivation Γ C
| TopR :
  Derivation Γ top
| TopL :
  Derivation Γ A →
  Derivation (top ::ₘ Γ) A
-- | AndL₀ :  Derivation (A₀ ::ₘ Γ) C → Derivation (and A₀ A₁ ::ₘ Γ) C
-- | AndL₁ :  Derivation (A₁ ::ₘ Γ) C → Derivation (and A₀ A₁ ::ₘ Γ) C
| AndL :
  Derivation (A₀ ::ₘ A₁ ::ₘ Γ) C →
  Derivation (and A₀ A₁ ::ₘ Γ) C
| AndR :
  (fst : Derivation Γ A) →
  (snd : Derivation Γ B) →
  Derivation Γ (and A B)
| OrL :
  (fst : Derivation (A ::ₘ Γ) C) →
  (snd : Derivation (B ::ₘ Γ) C) →
  Derivation (or A B ::ₘ Γ) C
| OrR₀ :
  Derivation Γ (A₀) →
  Derivation Γ (or A₀ A₁)
| OrR₁ :
  Derivation Γ (A₁) →
  Derivation Γ (or A₀ A₁)
| ImpL :
  (fst : Derivation (imp A B ::ₘ Γ) A) →
  (snd : Derivation (B ::ₘ Γ) C) →
  Derivation (imp A B ::ₘ Γ) C
| ImpR :
  Derivation (A ::ₘ Γ) B →
  Derivation Γ (imp A B)

def Provable (Γ : Multiset Formula) (C : Formula) : Prop :=
  Nonempty (Derivation Γ C)

infix:50 " ⊢ " => Provable
infix:50 " ⊢ᴳ³ⁱᵖ " => Provable

end G3ip

open G3ip
open Formula
open Derivation

section Admissible

namespace Derivation

def Identity (A : Formula) :
  (h : A ∈ Γ := by aesop) →
  Derivation Γ A := by
  sorry

def Contraction :
  Derivation  (A ::ₘ A ::ₘ Γ) B →
  Derivation  (A ::ₘ Γ) B := by
  sorry

def Weakening :
  Derivation  Γ B →
  Derivation  (A ::ₘ Γ) B := by
  sorry

def TopL_inversion :
  Derivation (top ::ₘ Γ) A →
  Derivation Γ A := by
  sorry

def AndR_inversion :
  Derivation Γ (and A B) →
  Derivation Γ A × Derivation Γ B := by
  intro h
  constructor
  · sorry
  · sorry

def Cut (A : Formula) :
  (fst : Derivation Γ A) →
  (snd : Derivation (A ::ₘ Γ) B) →
  Derivation Γ B := by
  sorry
  -- intro h₀ h1
  -- induction A with
  -- | atom p =>
    -- | Identity _ h =>
    -- | BotL _ h =>
    -- | TopR =>
    -- | TopL D =>
    -- | .AndL =>
    -- | .AndR =>
    -- | .OrL =>
    -- | .OrR₀ =>
    -- | .OrR₁ =>
    -- | .ImpL =>
    -- | .ImpR =>

theorem Cut_adm : Γ ⊢ A → (A ::ₘ Γ) ⊢ B → Γ ⊢ B := by
  intro ⟨h₀P⟩ ⟨h₁P⟩
  have P : Derivation Γ B := by
    apply Cut A h₀P h₁P
  use P

end Derivation

end Admissible

section test

open Derivation

example : [A, B] ⊢ and A B := by
  have P : Derivation [A, B] (and A B) := by
    apply AndR
    · apply Identity A
    · apply Identity B
  use P

example : Γ ⊢ and A B → Γ ⊢ A ∧ Γ ⊢ B := by
  intro ⟨hP⟩
  have PA : Derivation Γ A := by
    apply Cut (and A B)
    · trivial
    · apply AndL
      apply Identity A
  have PB : Derivation Γ B := by
    apply Cut (and A B)
    · trivial
    · apply AndL
      apply Identity B
  constructor
  · use PA
  · use PB

end test
