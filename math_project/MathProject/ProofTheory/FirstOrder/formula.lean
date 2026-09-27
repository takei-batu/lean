import MathProject.ProofTheory.FirstOrder.language
import Mathlib.Data.Set.Basic

inductive Formula (𝒮 : Signature) where
  | atom (p : 𝒮.Rel n) (args : Fin n → Term 𝒮) : Formula 𝒮
  | bot : Formula 𝒮
  -- | top : Formula 𝒮
  | imp : Formula 𝒮 → Formula 𝒮 → Formula 𝒮
  | and : Formula 𝒮 → Formula 𝒮 → Formula 𝒮
  | or : Formula 𝒮 → Formula 𝒮 → Formula 𝒮
  | forall_ : Formula 𝒮 → Formula 𝒮
  | exists_ : Formula 𝒮 → Formula 𝒮
-- deriving Repr, DecidableEq

local notation "⊥"   => Formula.bot

namespace Formula

def not (A : Formula 𝒮) : Formula 𝒮 := .imp A ⊥
def top : Formula 𝒮 := .not ⊥
-- def or (A B : Formula 𝒮) : Formula 𝒮 := .imp (.not A) B
-- def and (A B : Formula 𝒮) : Formula 𝒮 := .not (.or (.not A) (.not B))
-- def iff (A B : Formula 𝒮) : Formula 𝒮 := .not (.and (.imp A B) (.imp B A))
-- def exist_ (A : Formula 𝒮) : Formula 𝒮 := .not (.forall_ (.not A))

def lift {𝒮 : Signature} (cutoff : Nat) (delta : Nat) : Formula 𝒮 → Formula 𝒮
  | atom p args => atom p (fun i => Term.lift cutoff delta (args i))
  | bot => bot
  | imp A B => imp (lift cutoff delta A) (lift cutoff delta B)
  | and A B => and (lift cutoff delta A) (lift cutoff delta B)
  | or A B => or (lift cutoff delta A) (lift cutoff delta B)
  | forall_ A => forall_ (lift cutoff delta A)
  | exists_ A => exists_ (lift cutoff delta A)

def inst {𝒮 : Signature} (idx : Nat) (t : Term 𝒮) : Formula 𝒮 → Formula 𝒮
  | atom p args => atom p (fun i => Term.inst idx t (args i))
  | bot => bot
  | imp A B => imp (inst idx t A) (inst idx t B)
  | and A B => and (inst idx t A) (inst idx t B)
  | or A B => or (inst idx t A) (inst idx t B)
  | forall_ A => forall_ (inst (idx + 1) t A)
  | exists_ A => exists_ (inst (idx + 1) t A)

/-- free variable $x apears in A. -/
def has_fvar {𝒮 : Signature} (x : String) : Formula 𝒮 → Bool
  | atom (n := n) _ args => (List.finRange n).any (fun i => Term.has_fvar x (args i))
  | bot => false
  | imp A B => has_fvar x A || has_fvar x B
  | and A B => has_fvar x A || has_fvar x B
  | or A B => has_fvar x A || has_fvar x B
  | forall_ A => has_fvar x A
  | exists_ A => has_fvar x A

def FV {𝒮 : Signature} (A : Formula 𝒮) : Set String := fun x => has_fvar x A == true

def FV_Ant {𝒮 : Signature} (Γ : List (Formula 𝒮)) : Set String := fun x => Γ.any (has_fvar x) = true

end Formula
