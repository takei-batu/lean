import MathProject.ProofTheory.SequentCalculi.Basic
import MathProject.ProofTheory.FirstOrder.formula

namespace LJ

open Formula

variable {𝒮 : Signature}

instance : Coe (Formula 𝒮) (Option (Formula 𝒮)) := ⟨some⟩

inductive Derivation : List (Formula 𝒮) → Option (Formula 𝒮) -> Type where
| Axiom (A : Formula 𝒮) : Derivation [A] A
| BotL : Derivation [.bot] none
| WkL  :
  Derivation Γ Δ →
  Derivation (A :: Γ) Δ
-- | WkR :
--   Derivation Γ Δ →
--   Derivation Γ (A :: Δ)
| CL :
  Derivation  (A :: A :: Γ) Δ →
  Derivation  (A :: Γ) Δ
-- | CR :
--   Derivation Γ (A :: A :: Δ) →
--   Derivation Γ (A :: Δ)
| ExL (i j : Nat) :
  Derivation (Γ.swap i j) Δ →
  Derivation Γ Δ
-- | ExR (i j : Nat) :
--   Derivation Γ (Δ.swap i j) →
--   Derivation Γ Δ
| AndL₀ :
  Derivation (A₀ :: Γ) Δ →
  Derivation (and A₀ A₁ :: Γ) Δ
| AndL₁ :  Derivation (A₁ :: Γ) Δ → Derivation (and A₀ A₁ :: Γ) Δ
| AndR {A B : Formula 𝒮} :
  (fst : Derivation Γ A) →
  (snd : Derivation Γ B) →
  Derivation Γ (and A B)
| OrL :
  (fst : Derivation (A :: Γ) Δ) →
  (snd : Derivation (B :: Γ) Δ) →
  Derivation (or A B :: Γ) Δ
| OrR₀ {A B : Formula 𝒮} :
  Derivation Γ A →
  Derivation Γ (or A B)
| OrR₁ {A B : Formula 𝒮} :
  Derivation Γ B →
  Derivation Γ (or A B)
| ImpL {A B : Formula 𝒮} :
  (fst : Derivation Γ A) →
  (snd : Derivation (B :: Γ) Δ) →
  Derivation (imp A B :: Γ) Δ
| ImpR :
  Derivation (A :: Γ) (B : Formula 𝒮) →
  Derivation Γ (imp A B)
| AllL :
  Derivation (inst 0 t A :: Γ) Δ →
  Derivation (forall_ A :: Γ) Δ
| AllR {A : Formula 𝒮} :
  ∀ x : String, (x ∉ FV A ∧ x ∉ FV_Ant Γ) →
  Derivation Γ (inst 0 (Term.fvar x) A) →
  Derivation Γ (forall_ A)
| ExtL :
  ∀ x : String, (x ∉ FV A ∧ x ∉ FV_Ant Γ) →
  Derivation (inst 0 (Term.fvar x) A :: Γ) Δ →
  Derivation (exists_ A :: Γ) Δ
| ExtR {A : Formula 𝒮} :
  Derivation Γ (inst 0 t A) →
  Derivation Γ (exists_ A)


def Provable {𝒮 : Signature} (Γ : List (Formula 𝒮)) (Δ : Option (Formula 𝒮)) : Prop :=
  Nonempty (Derivation Γ Δ)

infix:50 " ⊢ " => Provable
infix:50 " ⊢ᴸᴶ " => Provable

end LJ

open LJ
open Formula
open Derivation

namespace Derivation

-- variable {𝒮 : Signature}

def Cut {A : Formula 𝒮} :
  (fst : Derivation Γ A) →
  (snd : Derivation (A :: Γ) Δ) →
  Derivation Γ Δ := by
  sorry

theorem Cut_adm {A : Formula 𝒮} : Γ ⊢ A → (A :: Γ) ⊢ Δ → Γ ⊢ Δ := by
  sorry

def Axiom_alt (A : Formula 𝒮) : Derivation (A :: Γ) A := by
  induction Γ with
  | nil => apply Axiom A
  | cons B Δ ih =>
    apply ExL 0 1
    apply WkL
    apply ih

end Derivation

section test

open Derivation

-- example : [A, B] ⊢ [and A B] := by
--   have P : Derivation [A, B] [and A B] := by
--     apply AndR
--     · apply ExL 0 1
--       apply WkL
--       apply Axiom A
--     · apply WkL
--       apply Axiom B
--   use P

-- example : Γ ⊢ [A] ∧ Γ ⊢ [B] → Γ ⊢ [.and A B] := by
--   intro ⟨⟨Pa⟩, ⟨Pb⟩⟩
--   have P : Derivation Γ [and A B] := by
--     apply AndR
--     · trivial
--     · trivial
--   use P

-- example : Γ ⊢ [.and A B] → Γ ⊢ [A] ∧ Γ ⊢ [B] := by
--   intro ⟨P⟩
--   constructor
--   · have PA : Derivation (.and A B :: Γ) [A] := by
--       apply AndL₀
--       apply Axiom_alt A
--     have P_wk : Derivation Γ (.and A B :: [A]) := by
--       apply ExR 0 1
--       apply WkR
--       exact P
--     exact ⟨Cut P_wk PA⟩
--   · have PB : Derivation (.and A B :: Γ) [B] := by
--       apply AndL₁
--       apply Axiom_alt B
--     have P_wk : Derivation Γ (.and A B :: [B]) := by
--       apply ExR 0 1
--       apply WkR
--       exact P
--     exact ⟨Cut P_wk PB⟩

end test
