import Mathlib.Order.Defs.LinearOrder
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Data.Multiset.AddSub
import MathProject.ProofTheory.Propositional.formula

/-! G3ip for base of inv system -/
namespace G3ip

open Formula

/-- Derivation n Γ A is a prooftree whose conclusion of form Γ ⇒ A and depth is "at most" n -/
inductive Derivation : Nat → Multiset (Formula) → Formula -> Type where
| Id :
  (h : atom p ∈ Γ := by aesop) →
  Derivation n Γ (atom p)
| BotL (A : Formula) :
  (h : bot ∈ Γ := by aesop) →
  Derivation n Γ A
| TopR :
  Derivation n Γ top
| AndL :
  Derivation n (A ::ₘ B ::ₘ Γ) C →
  Derivation (n + 1) (and A B ::ₘ Γ) C
| AndR :
  (fst : Derivation n Γ A) →
  (snd : Derivation n Γ B) →
  Derivation (n + 1) Γ (and A B)
| OrL :
  (fst : Derivation n (A ::ₘ Γ) C) →
  (snd : Derivation n (B ::ₘ Γ) C) →
  Derivation (n + 1) (or A B ::ₘ Γ) C
| OrR₀ :
  Derivation n Γ A →
  Derivation (n + 1) Γ (or A B)
| OrR₁ :
  Derivation n Γ B →
  Derivation (n + 1) Γ (or A B)
| ImpL :
  (fst : Derivation n (imp A B ::ₘ Γ) A) →
  (snd : Derivation n (imp A B ::ₘ B ::ₘ Γ) C) →
  Derivation (n + 1) (imp A B ::ₘ Γ) C
| ImpR :
  Derivation n (A ::ₘ Γ) B →
  Derivation (n + 1) Γ (imp A B)

def Provable (Γ : Multiset Formula) (C : Formula) : Prop :=
  ∃ n, Nonempty (Derivation n Γ C)

infix:50 " ⊢ " => Provable
infix:50 " ⊢ᴳ³ⁱᵖ " => Provable

open G3ip
open Derivation
open Formula
open Multiset
open LinearOrder

attribute [simp] Multiset.cons_swap mem_cons_self
theorem cons_swap_rotate (a b c : α) (s : Multiset α) :
  a ::ₘ b ::ₘ c ::ₘ s = c ::ₘ a ::ₘ b ::ₘ s := by simp

theorem cons_swap_pair (a b c d : α) (s : Multiset α) :
  a ::ₘ b ::ₘ c ::ₘ d ::ₘ s = c ::ₘ d ::ₘ a ::ₘ b ::ₘ s := by simp

theorem erase_cons_tail_of_mem_2x [DecidableEq α] {a x y : α} {s : Multiset α} (h_mem : a ∈ s) :
  (x ::ₘ y ::ₘ s).erase a = x ::ₘ y ::ₘ s.erase a := by
  nth_rw 1 [← cons_erase h_mem, cons_swap_rotate, erase_cons_head]

theorem men_cons_neq (h_neq : a ≠ b := by simp) : a ∈ b ::ₘ s ↔ a ∈ s := by
  constructor
  · intro h
    rw[mem_cons] at h
    exact Or.resolve_left h h_neq
  · intro h; exact mem_cons_of_mem h

namespace Derivation

  -- match D with
  -- | .Id h => sorry
  -- | .BotL C h => sorry
  -- | .TopR => sorry
  -- | .AndR fst snd => sorry
  -- | .OrR₀ D' => sorry
  -- | .OrR₁ D' => sorry
  -- | .ImpR (Γ := Γ') (A := A') (B := B') D' => sorry
  -- | .AndL (Γ := Γ') (A := A') (B := B') D' => sorry
  -- | .OrL (Γ := Γ') (A := A') (B := B') fst snd => sorry
  -- | .ImpL (Γ := Γ') (A := A') (B := B') fst snd => sorry

  -- induction n with
  -- | zero =>
  --   sorry
  -- | succ n ih =>
  --   sorry

@[simp]
def height : Derivation n Γ A → Nat
  | .Id _ => 0
  | .BotL C _ => 0
  | .TopR => 0
  | .AndL D => height D + 1
  | .AndR D₀ D₁ => max (height D₀) (height D₁) + 1
  | .OrL D₀ D₁ => max (height D₀) (height D₁) + 1
  | .OrR₀ D => height D + 1
  | .OrR₁ D => height D + 1
  | .ImpL D₀ D₁ => max (height D₀) (height D₁) + 1
  | .ImpR D => height D + 1

theorem height_at_least (D : Derivation n Γ A) : 0 ≤ height D := by
  cases D <;> simp

theorem height_at_most (D : Derivation n Γ A) : height D <= n := by
  induction D <;> simp [max_le_iff, *]

def height_succ {n Γ A} :
  Derivation n Γ A → Derivation (n + 1) Γ A
  | .Id h => Id h
  | .BotL _ h => BotL _ h
  | .TopR => TopR
  | .AndR fst snd => AndR (height_succ fst) (height_succ snd)
  | .OrR₀ D => OrR₀ (height_succ D)
  | .OrR₁ D => OrR₁ (height_succ D)
  | .ImpR D => ImpR (height_succ D)
  | .AndL D => AndL (height_succ D)
  | .OrL fst snd => OrL (height_succ fst) (height_succ snd)
  | .ImpL fst snd => ImpL (height_succ fst) (height_succ snd)

section Admissible

def Exchange {n Γ₁ Γ₂ B} (h : Γ₁ = Γ₂ := by repeat simp only [cons_swap]) (D : Derivation n Γ₁ B) :
  Derivation n Γ₂ B := h ▸ D

def Weakening {n Γ A B} :
  Derivation n Γ B → Derivation n (A ::ₘ Γ) B
  | .Id h => by exact Id (mem_cons_of_mem h)
  | .BotL _ h => by exact BotL _ (mem_cons_of_mem h)
  | .TopR => by exact TopR
  | .AndR fst snd => by exact AndR (fst.Weakening) (snd.Weakening)
  | .OrR₀ D' => by exact OrR₀ (D'.Weakening)
  | .OrR₁ D' => by exact OrR₁ (D'.Weakening)
  | .ImpR D' => by exact ImpR (D'.Weakening (A := A)).Exchange
  | .AndL D' => by
    have D'' := Weakening (A := A) D'
    rw[←cons_swap_rotate] at D''
    exact (AndL D'').Exchange
  | .OrL fst snd => by
    have fst' := Weakening (A := A) fst
    have snd' := Weakening (A := A) snd
    rw[cons_swap] at fst' snd'
    exact (OrL fst' snd').Exchange
  | .ImpL fst snd => by
    have fst' := Weakening (A := A) fst
    have snd' := Weakening (A := A) snd
    rw[cons_swap] at fst'
    rw[←cons_swap_rotate] at snd'
    exact (ImpL fst' snd').Exchange

def AndR_inv {n Γ A B} :
  Derivation n Γ (A.and B) → Derivation n Γ A × Derivation n Γ B
  | .BotL _ h => by exact (BotL A h, BotL B h)
  | .AndR fst snd => by exact (fst.height_succ, snd.height_succ)
  | .AndL D' => by
    exact (AndL (AndR_inv D').1, AndL (AndR_inv D').2)
  | .OrL fst snd => by
    exact (OrL (AndR_inv fst).1 (AndR_inv snd).1, OrL (AndR_inv fst).2 (AndR_inv snd).2)
  | .ImpL fst snd => by
    exact (ImpL fst (AndR_inv snd).1, ImpL fst (AndR_inv snd).2)

def ImpR_inv {Γ A B} :
  Derivation n Γ (A.imp B) → Derivation n (A ::ₘ Γ) B
  | .BotL _ h => .BotL B (mem_cons_of_mem h)
  | .ImpR D' => D'.height_succ
  | .AndL D' => by
    have D'' := ImpR_inv D'
    rw [←cons_swap_rotate] at D''
    exact (AndL D'').Exchange
  | .OrL fst snd => by
    have fst' := ImpR_inv fst
    have snd' := ImpR_inv snd
    rw [cons_swap] at fst' snd'
    exact (OrL fst' snd').Exchange
  | .ImpL fst snd => by
    have fst' := Weakening (A := A) fst
    have snd' := ImpR_inv snd
    rw [cons_swap] at fst'
    rw [←cons_swap_rotate] at snd'
    exact (ImpL fst' snd').Exchange

def AndL_inv_mem {n Γ A B C} (h_mem : A.and B ∈ Γ) :
  Derivation n Γ C → Derivation n (A ::ₘ B ::ₘ Γ.erase (A.and B)) C
  | .TopR => by exact TopR
  | .Id (p := p) h => by
    rw[← mem_erase_of_ne (b := A.and B) (by simp)] at h
    exact .Id (mem_cons_of_mem (mem_cons_of_mem h))
  | .BotL φ h => by
    rw[← mem_erase_of_ne (b := A.and B) (by simp)] at h
    exact BotL φ (mem_cons_of_mem (mem_cons_of_mem h))
  | .AndR fst snd => by exact AndR (AndL_inv_mem h_mem fst) (AndL_inv_mem h_mem snd)
  | .OrR₀ D => by exact OrR₀ (AndL_inv_mem h_mem D)
  | .OrR₁ D => by exact OrR₁ (AndL_inv_mem h_mem D)
  | .ImpR D => by
    have := AndL_inv_mem (mem_cons_of_mem h_mem) D
    rw[erase_cons_tail_of_mem h_mem, cons_swap_rotate] at this
    exact ImpR this
  | .AndL (A := A') (B := B') D => by
    rw[mem_cons] at h_mem
    if h : A.and B = A'.and B' then
      rw[←and_eq] at h
      rw[h.1, h.2, erase_cons_head]
      exact D.height_succ
    else
      replace h_mem := Or.resolve_left h_mem h
      rw[erase_cons_tail_of_mem h_mem, cons_swap_rotate]
      have D' := AndL_inv_mem (mem_cons_of_mem (mem_cons_of_mem h_mem)) D
      rw[erase_cons_tail_of_mem_2x h_mem, cons_swap_pair] at D'
      exact AndL D'
  | .OrL fst snd => by
    rw[men_cons_neq] at h_mem
    have fst' := AndL_inv_mem (mem_cons_of_mem h_mem) fst
    have snd' := AndL_inv_mem (mem_cons_of_mem h_mem) snd
    rw[erase_cons_tail_of_mem h_mem, cons_swap_rotate] at fst' snd' ⊢
    exact OrL fst' snd'
  | .ImpL fst snd => by
    rw[men_cons_neq] at h_mem
    have fst' := AndL_inv_mem (mem_cons_of_mem h_mem) fst
    have snd' := AndL_inv_mem (mem_cons_of_mem (mem_cons_of_mem h_mem)) snd
    rw[erase_cons_tail_of_mem h_mem, cons_swap_rotate] at fst' ⊢
    rw[erase_cons_tail_of_mem_2x h_mem, cons_swap_pair] at snd'
    exact ImpL fst' snd'

def AndL_inv {n Γ C A B} :
  Derivation n (A.and B ::ₘ Γ) C → Derivation n (A ::ₘ B ::ₘ Γ) C := by
  intro D
  rw[←erase_cons_head (a := A.and B) (s := Γ)]
  exact AndL_inv_mem (mem_cons_self (A.and B) Γ) D

def OrL_inv_mem {n Γ A B C} (h_mem : A.or B ∈ Γ) :
  Derivation n Γ C →
    Derivation n (A ::ₘ Γ.erase (A.or B)) C × Derivation n (B ::ₘ Γ.erase (A.or B)) C
  | .TopR => by exact ⟨TopR, TopR⟩
  | .Id (p := p) h => by
    rw [← mem_erase_of_ne (b := A.or B) (by simp)] at h
    exact ⟨.Id (mem_cons_of_mem h), .Id (mem_cons_of_mem h)⟩
  | .BotL φ h => by
    rw [← mem_erase_of_ne (b := A.or B) (by simp)] at h
    exact ⟨BotL φ (mem_cons_of_mem h), BotL φ (mem_cons_of_mem h)⟩
  | .AndR fst snd => by
    have fst' := OrL_inv_mem h_mem fst
    have snd' := OrL_inv_mem h_mem snd
    exact ⟨AndR fst'.1 snd'.1, AndR fst'.2 snd'.2⟩
  | .OrR₀ D => by
    have ⟨fst, snd⟩ := OrL_inv_mem h_mem D
    exact ⟨OrR₀ fst, OrR₀ snd⟩
  | .OrR₁ D => by
    have ⟨fst, snd⟩ := OrL_inv_mem h_mem D
    exact ⟨OrR₁ fst, OrR₁ snd⟩
  | .ImpR (A := A') D => by
    have ⟨fst, snd⟩ := OrL_inv_mem (mem_cons_of_mem h_mem) D
    rw [erase_cons_tail_of_mem h_mem, cons_swap] at fst snd
    exact ⟨ImpR fst, ImpR snd⟩
  | .AndL D => by
    rw [men_cons_neq] at h_mem
    have ⟨fst, snd⟩ := OrL_inv_mem (mem_cons_of_mem (mem_cons_of_mem h_mem)) D
    rw [erase_cons_tail_of_mem_2x h_mem, ←cons_swap_rotate] at fst snd
    rw [erase_cons_tail_of_mem h_mem, cons_swap A, cons_swap B]
    exact ⟨AndL fst, AndL snd⟩
  | .OrL (A := A') (B := B') fst snd => by
    rw [mem_cons] at h_mem
    if h : A.or B = A'.or B' then
      rw[←or_eq] at h
      rw [h.1, h.2, erase_cons_head]
      exact ⟨fst.height_succ, snd.height_succ⟩
    else
      replace h_mem := Or.resolve_left h_mem h
      have fst' := OrL_inv_mem (mem_cons_of_mem (b := A') h_mem) fst
      have snd' := OrL_inv_mem (mem_cons_of_mem (b := B') h_mem) snd
      rw [erase_cons_tail_of_mem h_mem, cons_swap A, cons_swap B] at fst' snd' ⊢
      exact ⟨OrL fst'.1 snd'.1, OrL fst'.2 snd'.2⟩
  | .ImpL fst snd => by
    rw [men_cons_neq] at h_mem
    have fst' := OrL_inv_mem (mem_cons_of_mem h_mem) fst
    have snd' := OrL_inv_mem (mem_cons_of_mem (mem_cons_of_mem h_mem)) snd
    rw [erase_cons_tail_of_mem h_mem, cons_swap A, cons_swap B] at fst' ⊢
    rw [erase_cons_tail_of_mem_2x h_mem, ← cons_swap_rotate _ _ A, ← cons_swap_rotate _ _ B] at snd'
    exact ⟨ImpL fst'.1 snd'.1, ImpL fst'.2 snd'.2⟩

def OrL_inv {n Γ C A B} :
  Derivation n (A.or B ::ₘ Γ) C → Derivation n (A ::ₘ Γ) C × Derivation n (B ::ₘ Γ) C := by
  intro D
  rw [← erase_cons_head (a := A.or B) (s := Γ)]
  exact OrL_inv_mem (mem_cons_self (A.or B) Γ) D

def Contraction :
  Derivation n (A ::ₘ A ::ₘ Γ) B → Derivation n (A ::ₘ Γ) B := by
  induction n generalizing Γ A B with
  | zero =>
    intro D
    match D with
    | .Id _ => exact Id
    | .BotL _ _ => exact BotL _
    | .TopR => exact TopR
  | succ n ih =>
    intro D
    -- apply height_succ
    -- apply ih
    generalize ctx : (A ::ₘ A ::ₘ Γ) = Δ at D
    match D with
    | .Id _ => exact Id
    | .BotL _ _ => exact BotL _
    | .TopR => exact TopR
    | .AndR fst snd =>
      rw[←ctx] at fst snd
      exact AndR (ih fst) (ih snd)
      --exact AndR (Contraction_mem h fst) (Contraction_mem h snd)
    | .OrR₀ D' =>
      rw[←ctx] at D'
      exact OrR₀ (ih D')
      -- exact OrR₀ (Contraction_mem h D')
    | .OrR₁ D' =>
      rw[←ctx] at D'
      exact OrR₁ (ih D')
      -- exact OrR₁ (Contraction_mem h D')
    | .ImpR (A := A') (B := B') D' =>
      rw[←ctx, ←cons_swap_rotate] at D'
      apply ImpR (ih D').Exchange
    | .AndL (Γ := Γ') (A := A') (B := B') D' =>
      if h_eq : A = A'.and B' then
        subst h_eq
        rw[cons_inj_right] at ctx
        rw[←ctx, cons_swap_rotate] at D'
        have DAABB := AndL_inv D'
        rw [cons_swap B' A'] at DAABB
        have DABB := ih DAABB
        rw[←cons_swap_rotate] at DABB
        have DBA := ih DABB
        rw[cons_swap] at DBA
        exact AndL DBA
      else
        let Γ'' := Γ.erase (A'.and B')
        have eq_1: Γ = A'.and B' ::ₘ Γ'' := by
          have := mem_cons_self (A'.and B') Γ'
          rw[←ctx, mem_cons, mem_cons, ←or_assoc, or_self] at this
          replace := Or.resolve_left this (Ne.symm h_eq)
          rw[cons_erase this]
        have eq_2 : Γ' = A ::ₘ A ::ₘ Γ'' := by
          rw[eq_1, cons_swap_rotate, cons_inj_right] at ctx
          exact ctx.symm
        rw[eq_1]
        rw[eq_2, cons_swap_pair] at D'
        have := ih D'
        rw[←cons_swap_rotate] at this
        have := AndL this
        exact this.Exchange
    | .OrL (Γ := Γ') (A := A') (B := B') fst snd =>
      if h_eq : A = A'.or B' then
        subst h_eq
        rw[cons_inj_right] at ctx
        rw[←ctx, cons_swap] at fst snd
        have ⟨fst', _⟩ := OrL_inv fst
        have ⟨_, snd'⟩ := OrL_inv snd
        exact OrL (ih fst') (ih snd')
      else
        let Γ'' := Γ.erase (A'.or B')
        have eq_1: Γ = A'.or B' ::ₘ Γ'' := by
          have := mem_cons_self (A'.or B') Γ'
          rw[←ctx, mem_cons, mem_cons, ←or_assoc, or_self] at this
          replace := Or.resolve_left this (Ne.symm h_eq)
          rw[cons_erase this]
        have eq_2 : Γ' = A ::ₘ A ::ₘ Γ'' := by
          rw[eq_1, cons_swap_rotate, cons_inj_right] at ctx
          exact ctx.symm
        rw[eq_1]
        rw[eq_2, ←cons_swap_rotate] at fst snd
        have fst' := ih fst
        have snd' := ih snd
        rw[←cons_swap] at fst' snd'
        have := OrL fst' snd'
        exact this.Exchange
    | .ImpL (Γ := Γ') (A := A') (B := B') fst snd =>
      if h_eq : A = A'.imp B' then
        subst h_eq
        rw[cons_inj_right] at ctx
        rw[←ctx, cons_swap] at fst
        rw[←ctx, cons_swap_rotate] at snd
        exact ImpL (ih fst) (ih snd)
      else
        let Γ'' := Γ.erase (A'.imp B')
        have eq_1: Γ = A'.imp B' ::ₘ Γ'' := by
          have := mem_cons_self (A'.imp B') Γ'
          rw[←ctx, mem_cons, mem_cons, ←or_assoc, or_self] at this
          replace := Or.resolve_left this (Ne.symm h_eq)
          rw[cons_erase this]
        have eq_2 : Γ' = A ::ₘ A ::ₘ Γ'' := by
          rw[eq_1, cons_swap_rotate, cons_inj_right] at ctx
          exact ctx.symm
        rw[eq_1]
        rw[eq_2, ←cons_swap_rotate] at fst
        rw[eq_2, ←cons_swap_pair] at snd
        have fst' := ih fst
        have snd' := ih snd
        rw[cons_swap] at fst'
        rw[←cons_swap_rotate] at snd'
        have := ImpL fst' snd'
        exact this.Exchange

end Admissible

end Derivation

end G3ip
