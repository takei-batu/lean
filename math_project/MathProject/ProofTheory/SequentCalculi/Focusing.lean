import Mathlib.Data.Multiset.Basic
-- import MathProject.ProofTheory.Propositional.formula

namespace Focusing

inductive Phase where
| right : Phase
| left : Phase
| choice : Phase
| focusR : Phase
| focusL : Phase

inductive Polarity where
| pos : Polarity
| neg : Polarity
deriving DecidableEq, Repr

inductive Formula where
  | atom : String → Polarity → Formula -- atomic with polarity
  | bot : Formula
  | top : Formula
  | imp : Formula → Formula → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
deriving Repr, DecidableEq

def is_pos : Formula → Bool
| .atom _ .pos => true
| .bot => true
| .top => true
| .or _ _ => true
| .and _ _ => true
| _ => false

def is_neg : Formula → Bool
| .atom _ .neg => true
| .imp _ _ => true
| .and _ _ => true
| .top => true
| _ => false

open Formula
open Phase

inductive Derivation : Phase → Multiset (Formula) → List Formula → Formula -> Type where
/- Right Inversion -/
| AndR :
  (fst : Derivation right Γ Ω A) →
  (snd : Derivation right Γ Ω B) →
  Derivation right Γ Ω (and A B)
| ImpR :
  Derivation right Γ (A :: Ω) B →
  Derivation right Γ Ω (imp A B)
| TopR :
  Derivation right Γ Ω top
/- Right to Left -/
| LR_or :
  Derivation left Γ Ω (or A B) →
  Derivation right Γ Ω (or A B)
| LR_bot :
  Derivation left Γ Ω bot →
  Derivation right Γ Ω bot
| LR_atom :
  Derivation left Γ Ω (atom p P) →
  Derivation right Γ Ω (atom p P)
/- Left Inversion -/
| AndL :
  Derivation left Γ (A₀ :: A₁ :: Ω) C →
  Derivation left Γ (and A₀ A₁ :: Ω) C
| OrL :
  (fst : Derivation left Γ (A :: Ω) C) →
  (snd : Derivation left Γ (B :: Ω) C) →
  Derivation left Γ (or A B :: Ω) C
| BotL (C : Formula) :
  Derivation left Γ (bot :: Ω) C
| TopL :
  Derivation left Γ Ω C →
  Derivation left Γ (top :: Ω) C
/- Left to Left -/
| LL_imp :
  Derivation left (imp A B ::ₘ Γ) Ω C →
  Derivation left Γ (imp A B :: Ω) C
| LL_atom :
  Derivation left (atom p P ::ₘ Γ) Ω C →
  Derivation left Γ (atom p P :: Ω) C
/- Choice to Left -/
| CL :
  Derivation choice Γ [] C →
  Derivation left Γ [] C
/- Choice -/
| FRC :
  (hP : is_pos C == true := by decide) →
  Derivation focusR Γ [] C →
  Derivation choice Γ [] C
| FLC :
  (hA : A ∈ Γ := by aesop) →
  (hP : is_neg A == true := by decide) →
  Derivation focusL Γ [A] C →
  Derivation choice Γ [] C
/- Right Focus -/
| Id_pos :
  (h : atom p .pos ∈ Γ := by aesop) →
  Derivation focusR Γ [] (atom p .pos)
| OrR₀ :
  Derivation focusR Γ [] A₀ →
  Derivation focusR Γ [] (or A₀ A₁)
| OrR₁ :
  Derivation focusR Γ [] A₁ →
  Derivation focusR Γ [] (or A₀ A₁)
| AndRF :
  (fst : Derivation focusR Γ [] A) →
  (snd : Derivation focusR Γ [] B) →
  Derivation focusR Γ [] (and A B)
| TopRF :
  Derivation focusR Γ [] top
| RFR :
  Derivation right Γ [] (imp A B) →
  Derivation focusR Γ [] (imp A B)
| CFR :
  Derivation choice Γ [] (atom p .neg) →
  Derivation focusR Γ [] (atom p .neg)
/- Left Focus -/
| Id_neg :
  -- (h : atom p .neg ∈ Γ := by aesop) →
  Derivation focusL Γ [atom p .neg] (atom p .neg)
| ImpL :
  (fst : Derivation focusR Γ [] A) →
  (snd : Derivation focusL Γ [B] C) →
  Derivation focusL Γ [imp A B] C
| AndL₀ :
  Derivation focusL Γ [A₀] C →
  Derivation focusL Γ [and A₀ A₁] C
| AndL₁ :
  Derivation focusL Γ [A₁] C →
  Derivation focusL Γ [and A₀ A₁] C
| LFL_or :
  Derivation left Γ [or A B] C →
  Derivation focusL Γ [or A B] C
| LFL_bot :
  Derivation left Γ [bot] C →
  Derivation focusL Γ [bot] C
| CFL :
  Derivation choice Γ [] C →
  Derivation focusL Γ [atom p .pos] C

end Focusing
