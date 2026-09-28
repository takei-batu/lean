import Mathlib.Data.Multiset.Basic
import MathProject.ProofTheory.Propositional.formula

open Formula

/-- LJT / G4ip by Roy Dyckhoff 1992 -/
inductive Derivation : Multiset (Formula) → Formula -> Type where
| Axiom (A : Formula) :
  (h : A ∈ Γ := by aesop) →
  Derivation Γ A
| BotL (C : Formula) :
  (h : bot ∈ Γ := by aesop) →
  Derivation Γ C
-- | TopR : Derivation Γ top
-- | TopL :
--   Derivation Γ A →
--   Derivation (top ::ₘ Γ) A
-- | AndL₀ :  Derivation (A₀ ::ₘ Γ) Δ → Derivation (and A₀ A₁ ::ₘ Γ) C
-- | AndL₁ :  Derivation (A₁ ::ₘ Γ) Δ → Derivation (and A₀ A₁ ::ₘ Γ) C
| AndL :
  Derivation (A₀ ::ₘ A₁ ::ₘ Γ) Δ →
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
-- | ImpL :
--   (fst : Derivation (imp A B ::ₘ Γ) A) →
--   (snd : Derivation (B ::ₘ Γ) C) →
--   Derivation (imp A B ::ₘ Γ) C
| ImpL_atom :
  Derivation (B ::ₘ atom p ::ₘ Γ) C →
  Derivation (imp (atom p) B ::ₘ atom p ::ₘ Γ) C
| ImpL_and :
  Derivation (imp A₀ (imp A₁ B) ::ₘ Γ) C →
  Derivation (imp (and A₀ A₁) B ::ₘ atom p ::ₘ Γ) C
| ImpL_or :
  Derivation ((or A₀ B) ::ₘ (imp A₁ B) ::ₘ Γ) C →
  Derivation (imp (or A₀ A₁) B ::ₘ atom p ::ₘ Γ) C
| ImpL_imp :
  (fst : Derivation ((imp A₁ B) ::ₘ Γ) (imp A₀ A₁)) →
  (snd : Derivation (B ::ₘ Γ) C) →
  Derivation (imp (imp A₀ A₁) B ::ₘ atom p ::ₘ Γ) C
| ImpR :
  Derivation (A ::ₘ Γ) B →
  Derivation Γ (imp A B)

def Provable (Γ : Multiset Formula) (C : Formula) : Prop :=
  Nonempty (Derivation Γ C)

infix:50 " ⊢ " => Provable
infix:50 " ⊢ᴳ⁴ⁱᵖ " => Provable

section test

open Derivation

example : [A, B] ⊢ and A B := by
  have P : Derivation [A, B] (and A B) := by
    apply AndR
    · apply Axiom A
    · apply Axiom B
  use P

end test
