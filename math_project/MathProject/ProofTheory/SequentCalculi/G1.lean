-- import MathProject.ProofTheory.SequentCalculi.Basic
import MathProject.ProofTheory.FirstOrder.formula

namespace G1c

open Formula

variable {𝒮 : Signature}

inductive Derivation : List (Formula 𝒮) → List (Formula 𝒮) -> Prop where
| Axiom (A : Formula 𝒮) : Derivation [A] [A]
| BotL : Derivation [.bot] []
-- | WkL  : Derivation Γ Δ → Derivation (A :: Γ) Δ
-- | WR : Derivation Γ Δ → Derivation Γ (Δ ++ [A])
-- | CL : Derivation  (A :: A :: Γ) Δ → Derivation  (A :: Γ) Δ
-- | CR : Derivation Γ (Δ ++ [A] ++ [A]) → Derivation Γ (Δ ++ [A])
-- | AndL₀ :  Derivation (A₀ :: Γ) Δ → Derivation (.and A₀ A₁ :: Γ) Δ
-- | AndL₁ :  Derivation (A₁ :: Γ) Δ → Derivation (.and A₀ A₁ :: Γ) Δ
-- | AndR :  Derivation Γ (Δ ++ [A]) → Derivation Γ (Δ ++ [B]) → Derivation Γ (Δ ++ [.and A B])
-- | OrL :  Derivation (A :: Γ) Δ → Derivation (B :: Γ) Δ → Derivation (.or A B :: Γ) Δ
-- | OrR₀ :  Derivation Γ (Δ ++ [A₀]) → Derivation Γ (Δ ++ [.or A₀ A₁])
-- | OrR₁ :  Derivation Γ (Δ ++ [A₁]) → Derivation Γ (Δ ++ [.or A₀ A₁])
-- | ImpL : Derivation Γ (Δ ++ [A]) → Derivation (B :: Γ) Δ → Derivation (.imp A B :: Γ) Δ
-- | ImpR : Derivation (A :: Γ) (Δ ++ [B]) → Derivation (B :: Γ) Δ → Derivation Γ (Δ ++ [.imp A B])
-- | AllL : Derivation (.inst 0 t A :: Γ) Δ → Derivation (.forall_ A :: Γ) Δ
-- | AllR : ∀ x : String, (x ∉ FV A ∧ x ∉ FV_Ant Γ) →
--     Derivation Γ (Δ ++ [.inst 0 (.fvar x) A]) → Derivation Γ (Δ ++ [.forall_ A])
-- | ExtL : ∀ x : String, (x ∉ FV A ∧ x ∉ FV_Ant Γ) →
--     Derivation (.inst 0 (.fvar x) A :: Γ) Δ → Derivation (.exists_ A :: Γ) Δ
-- | ExtR : Derivation Γ (Δ ++ [.inst 0 t A]) → Derivation Γ (Δ ++ [.exists_ A])

end G1c

namespace G1i

inductive Derivation : List (Formula 𝒮) → Option (Formula 𝒮) -> Prop where
| Axiom (A : Formula 𝒮) : Derivation [A] A
| BotL : Derivation [.bot] none

end G1i

namespace G1m

inductive Derivation : List (Formula 𝒮) → Formula 𝒮 -> Prop where
| Axiom (A : Formula 𝒮) : Derivation [A] A

end G1m
