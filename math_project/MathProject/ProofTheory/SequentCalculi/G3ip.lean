import Mathlib.Order.Defs.LinearOrder
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Data.Multiset.AddSub
import MathProject.ProofTheory.Propositional.formula

/-! G3ip for base of inv system -/
namespace G3ip

open Formula

/-- Derivation Γ A is a prooftree whose conclusion of form Γ ⇒ A -/
inductive Derivation : Multiset (Formula) → Formula -> Type where
| Id :
  (h : atom p ∈ Γ := by aesop) →
  Derivation Γ (atom p)
| BotL (A : Formula) :
  (h : bot ∈ Γ := by aesop) →
  Derivation Γ A
| TopR :
  Derivation Γ top
| AndL :
  Derivation (A ::ₘ B ::ₘ Γ) C →
  Derivation (and A B ::ₘ Γ) C
| AndR :
  (fst : Derivation Γ A) →
  (snd : Derivation Γ B) →
  Derivation Γ (and A B)
| OrL :
  (fst : Derivation (A ::ₘ Γ) C) →
  (snd : Derivation (B ::ₘ Γ) C) →
  Derivation (or A B ::ₘ Γ) C
| OrR₀ :
  Derivation Γ A →
  Derivation Γ (or A B)
| OrR₁ :
  Derivation Γ B →
  Derivation Γ (or A B)
| ImpL :
  (fst : Derivation (imp A B ::ₘ Γ) A) →
  (snd : Derivation (imp A B ::ₘ B ::ₘ Γ) C) →
  Derivation (imp A B ::ₘ Γ) C
| ImpR :
  Derivation (A ::ₘ Γ) B →
  Derivation Γ (imp A B)

namespace Derivation
@[simp]
def size : Derivation Γ A → Nat
  | .Id _ => 1
  | .BotL C _ => 1
  | .TopR => 1
  | .AndL D => size D + 1
  | .AndR D₀ D₁ => size D₀ + size D₁ + 1
  | .OrL D₀ D₁ => size D₀ + size D₁ + 1
  | .OrR₀ D => size D + 1
  | .OrR₁ D => size D + 1
  | .ImpL D₀ D₁ => size D₀ + size D₁ + 1
  | .ImpR D => size D + 1
end Derivation

def Provable (Γ : Multiset Formula) (A : Formula) : Prop :=
  Nonempty (Derivation Γ A)

infix:50 " ⊢ " => Provable
infix:50 " ⊢ᴳ³ⁱᵖ " => Provable

/-- Derivation' n Γ A is a prooftree whose conclusion of form Γ ⇒ A and depth is "at most" n -/
inductive Derivation' : Nat → Multiset (Formula) → Formula -> Type where
| Id :
  (h : atom p ∈ Γ := by aesop) →
  Derivation' n Γ (atom p)
| BotL (A : Formula) :
  (h : bot ∈ Γ := by aesop) →
  Derivation' n Γ A
| TopR :
  Derivation' n Γ top
| AndL :
  Derivation' n (A ::ₘ B ::ₘ Γ) C →
  Derivation' (n + 1) (and A B ::ₘ Γ) C
| AndR :
  (fst : Derivation' n Γ A) →
  (snd : Derivation' n Γ B) →
  Derivation' (n + 1) Γ (and A B)
| OrL :
  (fst : Derivation' n (A ::ₘ Γ) C) →
  (snd : Derivation' n (B ::ₘ Γ) C) →
  Derivation' (n + 1) (or A B ::ₘ Γ) C
| OrR₀ :
  Derivation' n Γ A →
  Derivation' (n + 1) Γ (or A B)
| OrR₁ :
  Derivation' n Γ B →
  Derivation' (n + 1) Γ (or A B)
| ImpL :
  (fst : Derivation' n (imp A B ::ₘ Γ) A) →
  (snd : Derivation' n (imp A B ::ₘ B ::ₘ Γ) C) →
  Derivation' (n + 1) (imp A B ::ₘ Γ) C
| ImpR :
  Derivation' n (A ::ₘ Γ) B →
  Derivation' (n + 1) Γ (imp A B)

namespace Derivation'
@[simp]
def depth : Derivation' n Γ A → Nat
  | .Id _ => 0
  | .BotL _ _ => 0
  | .TopR => 0
  | .AndL D => depth D + 1
  | .AndR D₀ D₁ => max (depth D₀) (depth D₁) + 1
  | .OrL D₀ D₁ => max (depth D₀) (depth D₁) + 1
  | .OrR₀ D => depth D + 1
  | .OrR₁ D => depth D + 1
  | .ImpL D₀ D₁ => max (depth D₀) (depth D₁) + 1
  | .ImpR D => depth D + 1

theorem depth_at_least (D : Derivation' n Γ A) : 0 ≤ depth D := by
  cases D <;> simp

theorem depth_at_most (D : Derivation' n Γ A) : depth D <= n := by
  induction D <;> simp [max_le_iff, *]

def depth_succ {n Γ A} :
  Derivation' n Γ A → Derivation' (n + 1) Γ A
  | .Id _ => Id
  | .BotL _ _ => BotL _
  | .TopR => TopR
  | .AndR fst snd => AndR (depth_succ fst) (depth_succ snd)
  | .OrR₀ D => OrR₀ (depth_succ D)
  | .OrR₁ D => OrR₁ (depth_succ D)
  | .ImpR D => ImpR (depth_succ D)
  | .AndL D => AndL (depth_succ D)
  | .OrL fst snd => OrL (depth_succ fst) (depth_succ snd)
  | .ImpL fst snd => ImpL (depth_succ fst) (depth_succ snd)

def depth_succ_k {n k Γ A} : Derivation' n Γ A → Derivation' (n + k) Γ A := by
  intro D
  induction k with
  | zero =>
    rw[Nat.add_zero]
    exact D
  | succ k iD =>
    rw[←Nat.add_assoc]
    exact depth_succ iD

def depth_le {m n Γ A} (h : m <= n) : Derivation' m Γ A → Derivation' n Γ A := by
  rw[←Nat.add_sub_cancel' h]
  exact depth_succ_k
end Derivation'

section Convert

-- open Derivation
open Derivation'
def with_depth {Γ A} : (D : Derivation Γ A) → Derivation' (D.size) Γ A
  | .Id _ => .Id
  | .BotL _ _ => .BotL _
  | .TopR => .TopR
  | .OrR₀ D' => .OrR₀ (with_depth D')
  | .OrR₁ D' => .OrR₁ (with_depth D')
  | .ImpR D' => .ImpR (with_depth D')
  | .AndL D' => .AndL (with_depth D')
  | .AndR fst snd => by
    apply AndR
    · apply depth_le (m := fst.size) (by omega)
      exact with_depth fst
    · apply depth_le (m := snd.size) (by omega)
      exact with_depth snd
  | .OrL fst snd => by
      apply OrL
      · apply depth_le (m := fst.size) (by omega)
        exact with_depth fst
      · apply depth_le (m := snd.size) (by omega)
        exact with_depth snd
  | .ImpL fst snd => by
      apply ImpL
      · apply depth_le (m := fst.size) (by omega)
        exact with_depth fst
      · apply depth_le (m := snd.size) (by omega)
        exact with_depth snd

def without_depth : Derivation' n Γ A → Derivation Γ A
  | .Id _ => .Id
  | .BotL _ _ => .BotL _
  | .TopR => .TopR
  | .AndL D' => .AndL (without_depth D')
  | .OrR₀ D' => .OrR₀ (without_depth D')
  | .OrR₁ D' => .OrR₁ (without_depth D')
  | .ImpR D' => .ImpR (without_depth D')
  | .AndR fst snd => .AndR (without_depth fst) (without_depth snd)
  | .OrL fst snd => .OrL (without_depth fst) (without_depth snd)
  | .ImpL fst snd => .ImpL (without_depth fst) (without_depth snd)

end Convert

-- open G3ip
-- open Derivation'
-- open Formula
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

theorem for_commutative {φ A : Formula} (ctx : φ ::ₘ Γ = A ::ₘ Γ') (h_neq : φ ≠ A) :
  A ∈ Γ ∧ Γ' = φ ::ₘ Γ.erase A := by
  have := mem_cons_self A Γ'
  rw [←ctx, mem_cons] at this
  replace : A ∈ Γ := Or.resolve_left this h_neq.symm
  constructor
  · exact this
  · rw [←cons_erase this, cons_swap, cons_inj_right] at ctx
    exact ctx.symm

theorem cons_erase_eq_of_exists {Γ Γ' : Multiset Formula} {φ ψ : Formula}
  (h : ∃ cs, Γ = φ ::ₘ cs ∧ Γ' = ψ ::ₘ cs) :
  Γ = φ ::ₘ Γ.erase φ ∧ Γ' = ψ ::ₘ Γ.erase φ := by
  obtain ⟨cs, hcs₀, hcs₁⟩ := h
  -- 1つ目の等式の証明
  have h_mem : φ ∈ Γ := by
    rw [hcs₀]
    simp only[mem_cons_self]
  have h₀ : Γ = φ ::ₘ Γ.erase φ := (Multiset.cons_erase h_mem).symm
  -- 2つ目の等式の証明
  have h₁ : Γ' = ψ ::ₘ Γ.erase φ := by
    have h_cs : Γ.erase φ = cs := by
      rw [hcs₀, erase_cons_head]
    rw [h_cs]
    exact hcs₁
  exact ⟨h₀, h₁⟩

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

  --   match φ with
  -- | .atom p => sorry
  -- | .bot => sorry
  -- | .top => sorry
  -- | .imp A B => sorry
  -- | .and A B => sorry
  -- | .or A B => sorry

  -- induction n with
  -- | zero =>
  --   sorry
  -- | succ n ih =>
  --   sorry

section Admissible

namespace Derivation'

def Exchange {n Γ₁ Γ₂ B} (h : Γ₁ = Γ₂ := by repeat simp only [cons_swap]) (D : Derivation' n Γ₁ B) :
  Derivation' n Γ₂ B := h ▸ D

def Weakening {n Γ A B} :
  Derivation' n Γ B → Derivation' n (A ::ₘ Γ) B
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
  Derivation' n Γ (A.and B) → Derivation' n Γ A × Derivation' n Γ B
  | .BotL _ h => by exact (BotL A h, BotL B h)
  | .AndR fst snd => by exact (fst.depth_succ, snd.depth_succ)
  | .AndL D' => by
    exact (AndL (AndR_inv D').1, AndL (AndR_inv D').2)
  | .OrL fst snd => by
    exact (OrL (AndR_inv fst).1 (AndR_inv snd).1, OrL (AndR_inv fst).2 (AndR_inv snd).2)
  | .ImpL fst snd => by
    exact (ImpL fst (AndR_inv snd).1, ImpL fst (AndR_inv snd).2)

def ImpR_inv {Γ A B} :
  Derivation' n Γ (A.imp B) → Derivation' n (A ::ₘ Γ) B
  | .BotL _ h => .BotL B (mem_cons_of_mem h)
  | .ImpR D' => D'.depth_succ
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
  Derivation' n Γ C → Derivation' n (A ::ₘ B ::ₘ Γ.erase (A.and B)) C
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
      exact D.depth_succ
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
  Derivation' n (A.and B ::ₘ Γ) C → Derivation' n (A ::ₘ B ::ₘ Γ) C := by
  intro D
  rw[←erase_cons_head (a := A.and B) (s := Γ)]
  exact AndL_inv_mem (mem_cons_self (A.and B) Γ) D

def OrL_inv_mem {n Γ A B C} (h_mem : A.or B ∈ Γ) :
  Derivation' n Γ C →
    Derivation' n (A ::ₘ Γ.erase (A.or B)) C × Derivation' n (B ::ₘ Γ.erase (A.or B)) C
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
      exact ⟨fst.depth_succ, snd.depth_succ⟩
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
  Derivation' n (A.or B ::ₘ Γ) C → Derivation' n (A ::ₘ Γ) C × Derivation' n (B ::ₘ Γ) C := by
  intro D
  rw [← erase_cons_head (a := A.or B) (s := Γ)]
  exact OrL_inv_mem (mem_cons_self (A.or B) Γ) D

def Contraction :
  Derivation' n (A ::ₘ A ::ₘ Γ) B → Derivation' n (A ::ₘ Γ) B := by
  induction n generalizing Γ A B with
  | zero =>
    intro D
    match D with
    | .Id _ => exact Id
    | .BotL _ _ => exact BotL _
    | .TopR => exact TopR
  | succ n ih =>
    intro D
    -- apply depth_succ
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
        have eq₁: Γ = A'.and B' ::ₘ Γ'' := by
          have := mem_cons_self (A'.and B') Γ'
          rw[←ctx, mem_cons, mem_cons, ←or_assoc, or_self] at this
          replace := Or.resolve_left this (Ne.symm h_eq)
          rw[cons_erase this]
        have eq₂ : Γ' = A ::ₘ A ::ₘ Γ'' := by
          rw[eq₁, cons_swap_rotate, cons_inj_right] at ctx
          exact ctx.symm
        rw[eq₁]
        rw[eq₂, cons_swap_pair] at D'
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
        have eq₁: Γ = A'.or B' ::ₘ Γ'' := by
          have := mem_cons_self (A'.or B') Γ'
          rw[←ctx, mem_cons, mem_cons, ←or_assoc, or_self] at this
          replace := Or.resolve_left this (Ne.symm h_eq)
          rw[cons_erase this]
        have eq₂ : Γ' = A ::ₘ A ::ₘ Γ'' := by
          rw[eq₁, cons_swap_rotate, cons_inj_right] at ctx
          exact ctx.symm
        rw[eq₁]
        rw[eq₂, ←cons_swap_rotate] at fst snd
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
        have eq₁: Γ = A'.imp B' ::ₘ Γ'' := by
          have := mem_cons_self (A'.imp B') Γ'
          rw[←ctx, mem_cons, mem_cons, ←or_assoc, or_self] at this
          replace := Or.resolve_left this (Ne.symm h_eq)
          rw[cons_erase this]
        have eq₂ : Γ' = A ::ₘ A ::ₘ Γ'' := by
          rw[eq₁, cons_swap_rotate, cons_inj_right] at ctx
          exact ctx.symm
        rw[eq₁]
        rw[eq₂, ←cons_swap_rotate] at fst
        rw[eq₂, ←cons_swap_pair] at snd
        have fst' := ih fst
        have snd' := ih snd
        rw[cons_swap] at fst'
        rw[←cons_swap_rotate] at snd'
        have := ImpL fst' snd'
        exact this.Exchange

set_option maxHeartbeats 1000000 in
-- Relaxed maxHeartbeats to verify massive pattern matching and termination proofs.
def Cut (D₁ : Derivation' n₁ Γ φ) (D₂ : Derivation' n₂ (φ ::ₘ Γ) ψ) :
  Σ k, Derivation' k Γ ψ := by
  generalize ctx : (φ ::ₘ Γ) = Δ at D₂
  match h₁ : D₁, h₂ : D₂ with
  -- axiom cases for D₁
  | .Id (p := p) h, D₂ =>
    rw[← ctx] at D₂
    rw[←erase_cons_head (atom p) Γ, erase_cons_tail_of_mem h] at D₂ ⊢
    exact ⟨n₂, Contraction D₂⟩
  | .BotL _ _, _ =>
    exact ⟨max n₁ n₂, BotL ψ⟩
  -- axiom cases for D₂
  | D₁, .Id (p := p) h =>
    rw[←ctx, mem_cons] at h
    if h_eq : atom p = φ then
      rw[h_eq]
      exact ⟨n₁, D₁⟩
    else
      exact ⟨max n₁ n₂, Id⟩
  | D₁, .TopR =>
    exact ⟨max n₁ n₂, TopR⟩
  -- D₂ = BotL
  | .AndR L₀ L₁, .BotL A h =>
    rw[←ctx, mem_cons] at h
    replace h := Or.resolve_left h (by simp)
    exact ⟨max n₁ n₂, BotL A h⟩
  | .OrR₀ L, .BotL A h =>
    rw[←ctx, mem_cons] at h
    replace h := Or.resolve_left h (by simp)
    exact ⟨max n₁ n₂, BotL A h⟩
  | .OrR₁ L, .BotL A h =>
    rw[←ctx, mem_cons] at h
    replace h := Or.resolve_left h (by simp)
    exact ⟨max n₁ n₂, BotL A h⟩
  | .ImpR L, .BotL A h =>
    rw[←ctx, mem_cons] at h
    replace h := Or.resolve_left h (by simp)
    exact ⟨max n₁ n₂, BotL A h⟩
  -- D₁ = TopR
  | .TopR, .BotL A h =>
    rw[←ctx, men_cons_neq] at h
    exact ⟨max n₁ n₂, BotL A⟩
  | .TopR, .AndL (Γ := Γ') (A := A') (B := B') R =>
    rename_i hΓ _ _ _ _ hφ
    subst hΓ hφ
    have ⟨h, eq⟩ := for_commutative ctx (by simp)
    rw[←cons_erase h] at D₁ ⊢
    rw[eq, cons_swap_rotate] at R
    have ⟨k, cut⟩ := Cut (AndL_inv D₁) R
    exact ⟨k + 1, AndL cut⟩
  | .TopR, .OrL fst snd =>
    rename_i hΓ _ _ _ _ hφ
    subst hΓ hφ
    have ⟨h, eq⟩ := for_commutative ctx (by simp)
    rw [←cons_erase h] at D₁ ⊢
    rw [eq, cons_swap] at fst snd
    have ⟨k₁, cut₁⟩ := Cut ((OrL_inv D₁).1) fst
    have ⟨k₂, cut₂⟩ := Cut ((OrL_inv D₁).2) snd
    have cut₁' := depth_le (n := max k₁ k₂) (by omega) cut₁
    have cut₂' := depth_le (n := max k₁ k₂) (by omega) cut₂
    exact ⟨max k₁ k₂ + 1, OrL cut₁' cut₂'⟩
  | .TopR, .ImpL (B := B') fst snd =>
    rename_i hΓ _ _ _ _ hφ
    subst hΓ hφ
    have ⟨h, eq⟩ := for_commutative ctx (by simp)
    rw [←cons_erase h] at D₁ ⊢
    rw [eq, cons_swap] at fst
    rw [eq, cons_swap_rotate] at snd
    have ⟨k₁, cut₁⟩ := Cut D₁ fst
    have D₁' := Weakening (A := B') D₁
    have ⟨k₂, cut₂⟩ := Cut D₁'.Exchange snd
    let cut₁' := depth_le (Nat.le_max_left k₁ k₂) cut₁
    let cut₂' := depth_le (Nat.le_max_right k₁ k₂) cut₂
    exact ⟨max k₁ k₂ + 1, ImpL cut₁' cut₂'⟩
  -- left commutative cases
  | .AndL L, D₂ =>
    rw[←ctx, cons_swap] at D₂
    have D₂' := AndL_inv D₂
    rw[cons_swap_rotate] at D₂'
    have ⟨k, cut⟩ := Cut L D₂'
    exact ⟨k + 1, AndL cut⟩
  | .OrL fst snd, D₂ =>
    rw[←ctx, cons_swap] at D₂
    have ⟨fst', snd'⟩ := OrL_inv D₂
    rw[cons_swap] at fst' snd'
    have ⟨k₁, cut₁⟩ := Cut fst fst'
    have ⟨k₂, cut₂⟩ := Cut snd snd'
    have cut₁' := depth_le (n := max k₁ k₂) (by omega) cut₁
    have cut₂' := depth_le (n := max k₁ k₂) (by omega) cut₂
    exact ⟨max k₁ k₂ + 1, OrL cut₁' cut₂'⟩
  | .ImpL (n := n) (Γ := Γ) (A := A) (B := B) fst snd, D₂ =>
    rw[←ctx] at D₂
    have D₂' := Weakening (A := B) D₂
    rw[←cons_swap_rotate] at D₂'
    have ⟨n', cut⟩ := Cut snd D₂'
    have fst' := depth_le (n := max n n') (by omega) fst
    have cut' := depth_le (n := max n n') (by omega) cut
    exact ⟨max n n' + 1, ImpL fst' cut'⟩
  -- harmony-cases
  | AndR (Γ := Γ) (A := A) (B := B) fst snd, .AndL (Γ := Γ') (A := A') (B := B') D₂' =>
    if h_eq : A.and B = A'.and B' then
      rw[←h_eq, cons_inj_right] at ctx
      rw[←and_eq] at h_eq
      rw[←h_eq.1, ←h_eq.2, ←ctx] at D₂'
      have ⟨_, cut⟩ := Cut (Weakening (A := B) fst) D₂'
      exact Cut snd cut
    else
      have ⟨h, eq⟩ := for_commutative ctx h_eq
      rw[←cons_erase h] at fst snd ⊢
      have fst' := AndL_inv fst
      have snd' := AndL_inv snd
      have D₁' := AndR (AndL_inv fst) (AndL_inv snd)
      rw[eq, cons_swap_rotate] at D₂'
      have ⟨k, cut⟩ := Cut D₁' D₂'
      exact ⟨k + 1, AndL cut⟩
  | .OrR₀ (Γ := Γ) (A := A) (B := B) D₁', .OrL (Γ := Γ') (A := A') (B := B') fst snd =>
    if h_eq : A.or B = A'.or B' then
      rw[←h_eq, cons_inj_right] at ctx
      rw[←or_eq] at h_eq
      rw[←h_eq.1, ←ctx] at fst
      exact Cut D₁' fst
    else
      have ⟨h, eq⟩ := for_commutative ctx h_eq
      rw[←cons_erase h] at D₁' ⊢
      rw[eq, cons_swap] at fst snd
      have ⟨fst', snd'⟩ := OrL_inv D₁'
      have ⟨k₁, cut₁⟩ := Cut (OrR₀ fst') fst
      have ⟨k₂, cut₂⟩ := Cut (OrR₀ snd') snd
      have cut₁' := depth_le (n := max k₁ k₂) (by omega) cut₁
      have cut₂' := depth_le (n := max k₁ k₂) (by omega) cut₂
      exact ⟨max k₁ k₂ + 1, OrL cut₁' cut₂'⟩
  | .OrR₁ (Γ := Γ) (A := A) (B := B) D₁', .OrL (Γ := Γ') (A := A') (B := B') fst snd =>
    if h_eq : A.or B = A'.or B' then
      rw[←h_eq, cons_inj_right] at ctx
      rw[←or_eq] at h_eq
      rw[←h_eq.2, ←ctx] at snd
      exact Cut D₁' snd
    else
      have ⟨h, eq⟩ := for_commutative ctx h_eq
      rw[←cons_erase h] at D₁' ⊢
      rw[eq, cons_swap] at fst snd
      have ⟨fst', snd'⟩ := OrL_inv D₁'
      have ⟨k₁, cut₁⟩ := Cut (OrR₁ fst') fst
      have ⟨k₂, cut₂⟩ := Cut (OrR₁ snd') snd
      have cut₁' := depth_le (n := max k₁ k₂) (by omega) cut₁
      have cut₂' := depth_le (n := max k₁ k₂) (by omega) cut₂
      exact ⟨max k₁ k₂ + 1, OrL cut₁' cut₂'⟩
  | .ImpR (Γ := Γ) (A := A) (B := B) D₁', .ImpL (Γ := Γ') (A := A') (B := B') fst snd =>
    rename_i hΓ _ _ _ _ hφ
    subst hΓ hφ
    if h_eq : A.imp B = A'.imp B' then
      rw[←h_eq, cons_inj_right] at ctx
      rw[←imp_eq] at h_eq
      rw[←h_eq.1, ←h_eq.2, ←ctx] at fst snd
      have ⟨k₁, cut₁⟩ := Cut D₁ fst
      have ⟨k₂, cut₂⟩ := Cut cut₁ D₁'
      have ⟨k₃, cut₃⟩ := Cut (Weakening D₁) snd
      exact Cut cut₂ cut₃
    else
      have ⟨h, eq⟩ := for_commutative ctx h_eq
      rw[←cons_erase h] at D₁ D₁' ⊢
      rw[eq, cons_swap] at fst
      rw[eq, cons_swap_rotate] at snd
      have ⟨k₁, cut₁⟩ := Cut D₁ fst
      have ⟨k₂, cut₂⟩ := Cut (Weakening (A := B') D₁).Exchange snd
      have cut₁' := depth_le (n := max k₁ k₂) (by omega) cut₁
      have cut₂' := depth_le (n := max k₁ k₂) (by omega) cut₂
      exact ⟨max k₁ k₂ + 1, ImpL cut₁' cut₂'⟩
  -- right commutative cases with Right rule
  | D₁, .AndR fst snd =>
    rw[←ctx] at fst snd
    have ⟨k₁, cut₁⟩ := Cut D₁ fst
    have ⟨k₂, cut₂⟩ := Cut D₁ snd
    have cut₁' := depth_le (n := max k₁ k₂) (by omega) cut₁
    have cut₂' := depth_le (n := max k₁ k₂) (by omega) cut₂
    exact ⟨max k₁ k₂ + 1, AndR cut₁' cut₂'⟩
  | D₁, .OrR₀ D₂' =>
    rw[←ctx] at D₂'
    have ⟨k, cut⟩ := Cut D₁ D₂'
    exact ⟨k + 1, OrR₀ cut⟩
  | D₁, .OrR₁ D₂' =>
    rw[←ctx] at D₂'
    have ⟨k, cut⟩ := Cut D₁ D₂'
    exact ⟨k + 1, OrR₁ cut⟩
  | D₁, .ImpR (A := A) D₂' =>
    rw[←ctx, cons_swap] at D₂'
    have ⟨k, cut⟩ := Cut (Weakening D₁) D₂'
    exact ⟨k + 1, ImpR cut⟩
  -- right commutative cases with Left rule
  | .OrR₀ (A := A) (B := B) D₁', .AndL (Γ := Γ') (A := A') (B := B') D₂' =>
    have ⟨h, eq⟩ := for_commutative ctx (by simp)
    rw[←cons_erase h] at D₁' ⊢
    rw[eq, cons_swap_rotate] at D₂'
    have ⟨k, cut⟩ := Cut (OrR₀ (AndL_inv D₁')) D₂'
    exact ⟨k + 1, AndL cut⟩
  | .OrR₁ (A := A) (B := B) D₁', .AndL (Γ := Γ') (A := A') (B := B') D₂' =>
    have ⟨h, eq⟩ := for_commutative ctx (by simp)
    rw[←cons_erase h] at D₁' ⊢
    rw[eq, cons_swap_rotate] at D₂'
    have ⟨k, cut⟩ := Cut (OrR₁ (AndL_inv D₁')) D₂'
    exact ⟨k + 1, AndL cut⟩
  | .ImpR (A := A) (B := B) D₁', .AndL (Γ := Γ') (A := A') (B := B') D₂' =>
    have ⟨h, eq⟩ := for_commutative ctx (by simp)
    rw[←cons_erase h] at D₁' ⊢
    rw[eq, cons_swap_rotate] at D₂'
    rw[cons_swap] at D₁'
    have D₁'' := AndL_inv D₁'
    rw[cons_swap_rotate] at D₁''
    have ⟨k, cut⟩ := Cut (ImpR D₁'') D₂'
    exact ⟨k + 1, AndL cut⟩
  | .AndR (A := A) (B := B) fst snd, .OrL (Γ := Γ') (A := A') (B := B') fst' snd' =>
    have ⟨h, eq⟩ := for_commutative ctx (by simp)
    rw[←cons_erase h] at fst snd ⊢
    rw[eq, cons_swap] at fst' snd'
    have fst'' := AndL_inv fst'
    have snd'' := AndL_inv snd'
    rw[cons_swap_rotate] at fst'' snd''
    have D₂' := OrL fst'' snd''
    rw[←cons_swap_rotate] at D₂'
    have ⟨_, cut⟩ := Cut (Weakening fst) D₂'
    exact Cut snd cut
  | .ImpR (A := A) (B := B) D₁', .OrL (Γ := Γ') (A := A') (B := B') fst' snd' =>
    rename_i hΓ _ _ _ _ hφ
    subst hΓ hφ
    have ⟨h, eq⟩ := for_commutative ctx (by simp)
    rw[←cons_erase h] at D₁ ⊢
    rw[eq, cons_swap] at fst' snd'
    have ⟨k₁, cut₁⟩ := Cut (OrL_inv D₁).1 fst'
    have ⟨k₂, cut₂⟩ := Cut (OrL_inv D₁).2 snd'
    have cut₁' := depth_le (n := max k₁ k₂) (by omega) cut₁
    have cut₂' := depth_le (n := max k₁ k₂) (by omega) cut₂
    exact ⟨max k₁ k₂ + 1, OrL cut₁' cut₂'⟩
  | .AndR (A := A) (B := B) fst snd, .ImpL (Γ := Γ') (A := A') (B := B') fst' snd' =>
    rename_i hΓ _ _ _ _ hφ
    subst hΓ hφ
    have ⟨h, eq⟩ := for_commutative ctx (by simp)
    rw[←cons_erase h] at D₁ ⊢
    rw[eq, cons_swap] at fst'
    rw[eq, cons_swap_rotate] at snd'
    have ⟨k₁, cut₁⟩ := Cut D₁ fst'
    have ⟨k₂, cut₂⟩ := Cut (Weakening (A := B') D₁).Exchange snd'
    have cut₁' := depth_le (n := max k₁ k₂) (by omega) cut₁
    have cut₂' := depth_le (n := max k₁ k₂) (by omega) cut₂
    exact ⟨max k₁ k₂ + 1, ImpL cut₁' cut₂'⟩
  | .OrR₀ (A := A) (B := B) D₁', .ImpL (Γ := Γ') (A := A') (B := B') fst' snd' =>
    rename_i hΓ _ _ _ _ hφ
    subst hΓ hφ
    have ⟨h, eq⟩ := for_commutative ctx (by simp)
    rw[←cons_erase h] at D₁ D₁' ⊢
    rw[eq, cons_swap] at fst'
    rw[eq, cons_swap_rotate] at snd'
    have ⟨k₁, cut₁⟩ := Cut D₁ fst'
    have ⟨k₂, cut₂⟩ := Cut (Weakening (A := B') D₁).Exchange snd'
    have cut₁' := depth_le (n := max k₁ k₂) (by omega) cut₁
    have cut₂' := depth_le (n := max k₁ k₂) (by omega) cut₂
    exact ⟨max k₁ k₂ + 1, ImpL cut₁' cut₂'⟩
  | .OrR₁ (A := A) (B := B) D₁', .ImpL (Γ := Γ') (A := A') (B := B') fst' snd' =>
    rename_i hΓ _ _ _ _ hφ
    subst hΓ hφ
    have ⟨h, eq⟩ := for_commutative ctx (by simp)
    rw[←cons_erase h] at D₁ D₁' ⊢
    rw[eq, cons_swap] at fst'
    rw[eq, cons_swap_rotate] at snd'
    have ⟨k₁, cut₁⟩ := Cut D₁ fst'
    have ⟨k₂, cut₂⟩ := Cut (Weakening (A := B') D₁).Exchange snd'
    have cut₁' := depth_le (n := max k₁ k₂) (by omega) cut₁
    have cut₂' := depth_le (n := max k₁ k₂) (by omega) cut₂
    exact ⟨max k₁ k₂ + 1, ImpL cut₁' cut₂'⟩
  termination_by (φ.size, n₁ + n₂)
  decreasing_by
  all_goals
    simp only [Prod.lex_def]
    subst_vars
    -- simp? [Formula.size]
    simp only [
      Formula.size, lt_self_iff_false, Nat.add_lt_add_iff_left,
      Nat.add_lt_add_iff_right, Nat.lt_add_one, and_self, or_true]
    all_goals
      left
      omega

end Derivation'

namespace Derivation

def Identity {Γ A} (h : A ∈ Γ := by aesop) : Derivation Γ A :=
  match A with
  | .atom p => Id h
  | .bot => BotL _ h
  | .top => TopR
  | .and A B => by
    rw[←cons_erase h]
    apply AndR
    · apply AndL
      exact Identity (by simp only [mem_cons, true_or])
    · apply AndL
      exact Identity (by simp only [mem_cons, true_or, or_true])
  | .or A B => by
    rw[←cons_erase h]
    apply OrL
    · apply OrR₀
      exact Identity (by simp only [mem_cons, true_or])
    · apply OrR₁
      exact Identity (by simp only [mem_cons, true_or])
  | .imp A B => by
    rw[←cons_erase h]
    apply ImpR
    rw[cons_swap]
    apply ImpL
    · exact Identity (by simp only [mem_cons, true_or, or_true])
    · exact Identity (by simp only [mem_cons, true_or, or_true])

def Weakening {Γ A B} :
  Derivation Γ B → Derivation (A ::ₘ Γ) B :=
  fun D => without_depth ((with_depth D).Weakening)

def AndR_inv {Γ A B} :
  Derivation Γ (A.and B) → Derivation Γ A × Derivation Γ B :=
  fun D => ⟨without_depth (with_depth D).AndR_inv.1 , without_depth (with_depth D).AndR_inv.2⟩

def ImpR_inv {Γ A B} :
  Derivation Γ (A.imp B) → Derivation (A ::ₘ Γ) B :=
  fun D => without_depth ((with_depth D).ImpR_inv)

def AndL_inv {Γ A B C} :
  Derivation (A.and B ::ₘ Γ) C → Derivation (A ::ₘ B ::ₘ Γ) C :=
  fun D => without_depth ((with_depth D).AndL_inv)

def OrL_inv {Γ A B C} :
  Derivation (A.or B ::ₘ Γ) C → Derivation (A ::ₘ Γ) C × Derivation (B ::ₘ Γ) C :=
  fun D => ⟨without_depth (with_depth D).OrL_inv.1 , without_depth (with_depth D).OrL_inv.2⟩

def Contraction {Γ A B} :
  Derivation (A ::ₘ A ::ₘ Γ) B → Derivation (A ::ₘ Γ) B :=
  fun D => without_depth ((with_depth D).Contraction)

def Cut {Γ φ ψ} :
  Derivation Γ φ → Derivation (φ ::ₘ Γ) ψ → Derivation Γ ψ :=
  fun D₁ D₂ => without_depth (((with_depth D₁).Cut (with_depth D₂)).2)

end Derivation

end Admissible

section test

open Derivation

example : {A, B} ⊢ A.and B := by
  have P : Derivation {A, B} (A.and B) := by
    apply AndR
    · exact Identity
    · exact Identity
  use P

example : Γ ⊢ A.and B → Γ ⊢ A ∧ Γ ⊢ B := by
  intro ⟨hP⟩
  have PA : Derivation Γ A := by
    apply Cut (φ := A.and B)
    · trivial
    · apply AndL
      exact Identity
  have PB : Derivation Γ B := by
    apply Cut (φ := A.and B)
    · trivial
    · apply AndL
      exact Identity
  constructor
  · use PA
  · use PB

example : Γ ⊢ A.and B → Γ ⊢ A ∧ Γ ⊢ B := by
  intro ⟨hP⟩
  have PA : Derivation Γ A := (AndR_inv hP).1
  have PB : Derivation Γ B := (AndR_inv hP).2
  constructor
  · use PA
  · use PB

end test

section Cut_Elimination

/-- Derivation Γ A is a prooftree whose conclusion of form Γ ⇒ A with Cut -/
inductive Derivation_Cut : Multiset (Formula) → Formula -> Type where
| Id :
  (h : atom p ∈ Γ := by aesop) →
  Derivation_Cut Γ (atom p)
| BotL (A : Formula) :
  (h : bot ∈ Γ := by aesop) →
  Derivation_Cut Γ A
| TopR :
  Derivation_Cut Γ top
| AndL :
  Derivation_Cut (A ::ₘ B ::ₘ Γ) C →
  Derivation_Cut (and A B ::ₘ Γ) C
| AndR :
  (fst : Derivation_Cut Γ A) →
  (snd : Derivation_Cut Γ B) →
  Derivation_Cut Γ (and A B)
| OrL :
  (fst : Derivation_Cut (A ::ₘ Γ) C) →
  (snd : Derivation_Cut (B ::ₘ Γ) C) →
  Derivation_Cut (or A B ::ₘ Γ) C
| OrR₀ :
  Derivation_Cut Γ A →
  Derivation_Cut Γ (or A B)
| OrR₁ :
  Derivation_Cut Γ B →
  Derivation_Cut Γ (or A B)
| ImpL :
  (fst : Derivation_Cut (imp A B ::ₘ Γ) A) →
  (snd : Derivation_Cut (imp A B ::ₘ B ::ₘ Γ) C) →
  Derivation_Cut (imp A B ::ₘ Γ) C
| ImpR :
  Derivation_Cut (A ::ₘ Γ) B →
  Derivation_Cut Γ (imp A B)
| Cut :
  (fst : Derivation_Cut Γ φ) →
  (snd : Derivation_Cut (φ ::ₘ Γ) ψ) →
  Derivation_Cut Γ ψ

def Provable_Cut (Γ : Multiset Formula) (A : Formula) : Prop :=
  Nonempty (Derivation_Cut Γ A)

infix:50 " ⊢ᶜᵘᵗ " => Provable_Cut

def cut_with {Γ A} : Derivation Γ A → Derivation_Cut Γ A
  | .Id h => .Id h
  | .BotL A h => .BotL A h
  | .TopR => .TopR
  | .AndL D => .AndL (cut_with D)
  | .AndR D₁ D₂ => .AndR (cut_with D₁) (cut_with D₂)
  | .OrL D₁ D₂ => .OrL (cut_with D₁) (cut_with D₂)
  | .OrR₀ D => .OrR₀ (cut_with D)
  | .OrR₁ D => .OrR₁ (cut_with D)
  | .ImpL D₁ D₂ => .ImpL (cut_with D₁) (cut_with D₂)
  | .ImpR D => .ImpR (cut_with D)

def cut_free {Γ A} : Derivation_Cut Γ A → Derivation Γ A
  | .Id h => .Id h
  | .BotL A h => .BotL A h
  | .TopR => .TopR
  | .AndL D => .AndL (cut_free D)
  | .AndR D₁ D₂ => .AndR (cut_free D₁) (cut_free D₂)
  | .OrL D₁ D₂ => .OrL (cut_free D₁) (cut_free D₂)
  | .OrR₀ D => .OrR₀ (cut_free D)
  | .OrR₁ D => .OrR₁ (cut_free D)
  | .ImpL D₁ D₂ => .ImpL (cut_free D₁) (cut_free D₂)
  | .ImpR D => .ImpR (cut_free D)
  | .Cut D₁ D₂ => Derivation.Cut (cut_free D₁) (cut_free D₂)

theorem Cut_Elimination : Γ ⊢ A ↔ Γ ⊢ᶜᵘᵗ A := by
  constructor
  · intro ⟨D⟩
    exact ⟨cut_with D⟩
  · intro ⟨D⟩
    exact ⟨cut_free D⟩

end Cut_Elimination

end G3ip
