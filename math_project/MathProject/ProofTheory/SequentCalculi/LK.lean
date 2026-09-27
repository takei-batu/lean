import MathProject.ProofTheory.SequentCalculi.Basic
import MathProject.ProofTheory.FirstOrder.formula

-- namespace LK

open Formula

variable {𝒮 : Signature}

inductive Derivation : List (Formula 𝒮) → List (Formula 𝒮) -> Type where
| Axiom (A : Formula 𝒮) : Derivation [A] [A]
| BotL : Derivation [.bot] []
| WkL  : Derivation Γ Δ → Derivation (A :: Γ) Δ
| WkR : Derivation Γ Δ → Derivation Γ (A :: Δ)
| CL : Derivation  (A :: A :: Γ) Δ → Derivation  (A :: Γ) Δ
| CR : Derivation Γ (A :: A :: Δ) → Derivation Γ (A :: Δ)
| ExL (i j : Nat) : Derivation (Γ.swap i j) Δ → Derivation Γ Δ
| ExR (i j : Nat) : Derivation Γ (Δ.swap i j) → Derivation Γ Δ
| AndL₀ :  Derivation (A₀ :: Γ) Δ → Derivation (and A₀ A₁ :: Γ) Δ
| AndL₁ :  Derivation (A₁ :: Γ) Δ → Derivation (and A₀ A₁ :: Γ) Δ
| AndR :
  (fst : Derivation Γ (A :: Δ)) →
  (snd : Derivation Γ (B :: Δ)) →
  Derivation Γ (and A B :: Δ)
| OrL :
  (fst : Derivation (A :: Γ) Δ) →
  (snd : Derivation (B :: Γ) Δ) →
  Derivation (or A B :: Γ) Δ
| OrR₀ :  Derivation Γ (A₀ :: Δ) → Derivation Γ (or A₀ A₁ :: Δ)
| OrR₁ :  Derivation Γ (A₁ :: Δ) → Derivation Γ (or A₀ A₁ :: Δ)
| ImpL :
  (fst : Derivation Γ (A :: Δ)) →
  (snd : Derivation (B :: Γ) Δ) →
  Derivation (imp A B :: Γ) Δ
| ImpR : Derivation (A :: Γ) (B :: Δ) → Derivation Γ (imp A B :: Δ)
| AllL : Derivation (inst 0 t A :: Γ) Δ → Derivation (forall_ A :: Γ) Δ
| AllR :
  ∀ x : String, (x ∉ FV A ∧ x ∉ FV_Ant Γ) →
  Derivation Γ (inst 0 (Term.fvar x) A :: Δ) →
  Derivation Γ (forall_ A :: Δ)
| ExtL :
  ∀ x : String, (x ∉ FV A ∧ x ∉ FV_Ant Γ) →
  Derivation (inst 0 (Term.fvar x) A :: Γ) Δ →
  Derivation (exists_ A :: Γ) Δ
| ExtR : Derivation Γ (inst 0 t A :: Δ) → Derivation Γ (exists_ A :: Δ)


def Provable {𝒮 : Signature} (Γ Δ : List (Formula 𝒮)) : Prop :=
  Nonempty (Derivation Γ Δ)

infix:50 " ⊢ " => Provable

namespace Derivation

def Cut :
  (fst : Derivation Γ (A :: Δ)) →
  (snd : Derivation (A :: Γ) Δ) →
  Derivation Γ Δ := by
  sorry

theorem Cut_adm : Γ ⊢ (A :: Δ) → (A :: Γ) ⊢ Δ → Γ ⊢ Δ := by
  sorry

def Axiom_alt (A : Formula 𝒮) : Derivation (A :: Γ) [A] := by
  induction Γ with
  | nil => apply Axiom A
  | cons B Δ ih =>
    apply ExL 0 1
    apply WkL
    apply ih

end Derivation

-- end LK

open Formula
-- open LK
open Derivation
-- variable {𝒮 : Signature}

example : [A, B] ⊢ [and A B] := by
  have P : Derivation [A, B] [and A B] := by
    apply AndR
    · apply ExL 0 1
      apply WkL
      apply Axiom A
    · apply WkL
      apply Axiom B
  use P

example : Γ ⊢ [A] ∧ Γ ⊢ [B] → Γ ⊢ [.and A B] := by
  intro ⟨⟨Pa⟩, ⟨Pb⟩⟩
  have P : Derivation Γ [and A B] := by
    apply AndR
    · trivial
    · trivial
  use P

example : Γ ⊢ [.and A B] → Γ ⊢ [A] ∧ Γ ⊢ [B] := by
  intro ⟨P⟩
  constructor
  · have PA : Derivation (.and A B :: Γ) [A] := by
      apply AndL₀
      apply Axiom_alt A
    have P_wk : Derivation Γ (.and A B :: [A]) := by
      apply ExR 0 1
      apply WkR
      exact P
    exact ⟨Cut P_wk PA⟩
  · have PB : Derivation (.and A B :: Γ) [B] := by
      apply AndL₁
      apply Axiom_alt B
    have P_wk : Derivation Γ (.and A B :: [B]) := by
      apply ExR 0 1
      apply WkR
      exact P
    exact ⟨Cut P_wk PB⟩
