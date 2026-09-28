import Mathlib.Data.Multiset.Basic
import MathProject.ProofTheory.Propositional.formula

namespace Inversion

inductive Phase where
| right : Phase
| left : Phase
| choice : Phase

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
/- Left to Right -/
| LR_or :
  Derivation left Γ Ω (or A B) →
  Derivation right Γ Ω (or A B)
| LR_bot :
  Derivation left Γ Ω bot →
  Derivation right Γ Ω bot
| LR_atom :
  Derivation left Γ Ω (atom p) →
  Derivation right Γ Ω (atom p)
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
  Derivation left (atom p ::ₘ Γ) Ω C →
  Derivation left Γ (atom p :: Ω) C
/- Choice to Left -/
| CL :
  Derivation choice Γ [] C →
  Derivation left Γ [] C
/- Choice to Right -/
| OrR₀ :
  Derivation right Γ [] A₀ →
  Derivation choice Γ [] (or A₀ A₁)
| OrR₁ :
  Derivation right Γ [] A₁ →
  Derivation choice Γ [] (or A₀ A₁)
| Id :
  (h : atom p ∈ Γ := by aesop) →
  Derivation choice Γ [] (atom p)
| ImpL :
  (fst : Derivation right (imp A B ::ₘ Γ) [] A) →
  (snd : Derivation right Γ [B] C) →
  Derivation choice (imp A B ::ₘ Γ) [] C

end Inversion
