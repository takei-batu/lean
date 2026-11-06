import Mathlib.Order.Defs.LinearOrder
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Data.Multiset.AddSub
import AI_SANDBOX.Propositional.formula

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
    match hΔ : A ::ₘ A ::ₘ Γ, D with
    | _, .Id h =>
      subst hΔ
      exact .Id (by simp only [mem_cons] at h ⊢; tauto)
    | _, .BotL _ h =>
      subst hΔ
      exact .BotL _ (by simp only [mem_cons] at h ⊢; tauto)
    | _, .TopR => exact .TopR
  | succ m ih =>
    intro D
    match hΔ : A ::ₘ A ::ₘ Γ, D with
    | _, .Id h =>
      subst hΔ
      exact .Id (by simp only [mem_cons] at h ⊢; tauto)
    | _, .BotL _ h =>
      subst hΔ
      exact .BotL _ (by simp only [mem_cons] at h ⊢; tauto)
    | _, .TopR => exact .TopR
    | _, .AndR fst snd =>
      subst hΔ
      exact .AndR (ih fst) (ih snd)
    | _, .OrR₀ D' =>
      subst hΔ
      exact .OrR₀ (ih D')
    | _, .OrR₁ D' =>
      subst hΔ
      exact .OrR₁ (ih D')
    | _, .ImpR (A := C) D' =>
      subst hΔ
      have D₁ : Derivation' m (A ::ₘ A ::ₘ C ::ₘ Γ) _ := D'.Exchange
      have D₂ : Derivation' m (C ::ₘ A ::ₘ Γ) _ := (ih D₁).Exchange
      exact .ImpR D₂
    | _, .AndL (A := C) (B := E) (Γ := Γ') D' =>
      if h : A = C.and E then
        subst h
        rw [cons_inj_right] at hΔ
        subst hΔ
        have D₁ : Derivation' m (C.and E ::ₘ C ::ₘ E ::ₘ Γ) _ := D'.Exchange
        have D₂ : Derivation' m (C ::ₘ C ::ₘ E ::ₘ E ::ₘ Γ) _ := (AndL_inv D₁).Exchange
        have D₃ : Derivation' m (E ::ₘ E ::ₘ C ::ₘ Γ) _ := (ih D₂).Exchange
        have D₄ : Derivation' m (C ::ₘ E ::ₘ Γ) _ := (ih D₃).Exchange
        exact .AndL D₄
      else
        obtain ⟨h_mem, rfl⟩ := for_commutative hΔ h
        have h_mem' : C.and E ∈ Γ := (men_cons_neq (Ne.symm h)).mp h_mem
        rw [erase_cons_tail_of_mem h_mem'] at D'
        have D₁ : Derivation' m (A ::ₘ A ::ₘ C ::ₘ E ::ₘ Γ.erase (C.and E)) _ := D'.Exchange
        have D₂ : Derivation' m (C ::ₘ E ::ₘ A ::ₘ Γ.erase (C.and E)) _ := (ih D₁).Exchange
        rw [← cons_erase h_mem']
        exact (AndL D₂).Exchange
    | _, .OrL (A := C) (B := E) (Γ := Γ') fst snd =>
      if h : A = C.or E then
        subst h
        rw [cons_inj_right] at hΔ
        subst hΔ
        have fst₁ : Derivation' m (C.or E ::ₘ C ::ₘ Γ) _ := fst.Exchange
        have snd₁ : Derivation' m (C.or E ::ₘ E ::ₘ Γ) _ := snd.Exchange
        exact .OrL (ih (OrL_inv fst₁).1) (ih (OrL_inv snd₁).2)
      else
        obtain ⟨h_mem, rfl⟩ := for_commutative hΔ h
        have h_mem' : C.or E ∈ Γ := (men_cons_neq (Ne.symm h)).mp h_mem
        rw [erase_cons_tail_of_mem h_mem'] at fst snd
        have fst₁ : Derivation' m (A ::ₘ A ::ₘ C ::ₘ Γ.erase (C.or E)) _ := fst.Exchange
        have snd₁ : Derivation' m (A ::ₘ A ::ₘ E ::ₘ Γ.erase (C.or E)) _ := snd.Exchange
        have fst₂ : Derivation' m (C ::ₘ A ::ₘ Γ.erase (C.or E)) _ := (ih fst₁).Exchange
        have snd₂ : Derivation' m (E ::ₘ A ::ₘ Γ.erase (C.or E)) _ := (ih snd₁).Exchange
        rw [← cons_erase h_mem']
        exact (OrL fst₂ snd₂).Exchange
    | _, .ImpL (A := C) (B := E) (Γ := Γ') fst snd =>
      if h : A = C.imp E then
        subst h
        rw [cons_inj_right] at hΔ
        subst hΔ
        have snd₁ : Derivation' m (C.imp E ::ₘ C.imp E ::ₘ E ::ₘ Γ) _ := snd.Exchange
        exact .ImpL (ih fst) (ih snd₁)
      else
        obtain ⟨h_mem, rfl⟩ := for_commutative hΔ h
        have h_mem' : C.imp E ∈ Γ := (men_cons_neq (Ne.symm h)).mp h_mem
        rw [erase_cons_tail_of_mem h_mem'] at fst snd
        have fst₁ : Derivation' m (A ::ₘ A ::ₘ C.imp E ::ₘ Γ.erase (C.imp E)) _ := fst.Exchange
        have snd₁ : Derivation' m (A ::ₘ A ::ₘ C.imp E ::ₘ E ::ₘ Γ.erase (C.imp E)) _ :=
          snd.Exchange
        have fst₂ : Derivation' m (C.imp E ::ₘ A ::ₘ Γ.erase (C.imp E)) _ := (ih fst₁).Exchange
        have snd₂ : Derivation' m (C.imp E ::ₘ E ::ₘ A ::ₘ Γ.erase (C.imp E)) _ :=
          (ih snd₁).Exchange
        rw [← cons_erase h_mem']
        exact (ImpL fst₂ snd₂).Exchange

set_option maxHeartbeats 1000000 in
-- Relaxed maxHeartbeats to verify massive pattern matching and termination proofs.
-- set_option trace.profiler true in
-- set_option diagnostics true in
def Cut (D₁ : Derivation' n₁ Γ φ) (D₂ : Derivation' n₂ (φ ::ₘ Γ) ψ) :
  Σ k, Derivation' k Γ ψ := by
  generalize ctx : (φ ::ₘ Γ) = Δ at D₂
  match h₁ : D₁, h₂ : D₂ with
  | .Id h, D₂ =>
    subst ctx
    rw [← cons_erase h] at D₂ ⊢
    exact ⟨_, Contraction D₂⟩
  | .BotL _ h, _ => exact ⟨0, BotL _ h⟩
  | .AndL (A := A) (B := B) (Γ := Γ') D, D₂ =>
    subst ctx
    have D₂' : Derivation' n₂ (φ ::ₘ A ::ₘ B ::ₘ Γ') ψ :=
      (AndL_inv (D₂.Exchange : Derivation' n₂ (A.and B ::ₘ φ ::ₘ Γ') ψ)).Exchange
    exact ⟨_, AndL (Cut D D₂').2⟩
  | .OrL (A := A) (B := B) (Γ := Γ') fst snd, D₂ =>
    subst ctx
    have D₂' := OrL_inv (D₂.Exchange : Derivation' n₂ (A.or B ::ₘ φ ::ₘ Γ') ψ)
    have E₁ := Cut fst (D₂'.1.Exchange : Derivation' n₂ (φ ::ₘ A ::ₘ Γ') ψ)
    have E₂ := Cut snd (D₂'.2.Exchange : Derivation' n₂ (φ ::ₘ B ::ₘ Γ') ψ)
    exact ⟨max E₁.1 E₂.1 + 1,
      OrL (depth_le (Nat.le_max_left _ _) E₁.2) (depth_le (Nat.le_max_right _ _) E₂.2)⟩
  | .ImpL (n := m) (A := A) (B := B) (Γ := Γ') fst snd, D₂ =>
    subst ctx
    have D₂' : Derivation' n₂ (φ ::ₘ A.imp B ::ₘ B ::ₘ Γ') ψ := (Weakening (A := B) D₂).Exchange
    have E := Cut snd D₂'
    exact ⟨max m E.1 + 1,
      ImpL (depth_le (Nat.le_max_left _ _) fst) (depth_le (Nat.le_max_right _ _) E.2)⟩
  | D₁, .Id (p := p) h =>
    subst ctx
    if hp : φ = atom p then
      subst hp
      exact ⟨_, D₁⟩
    else
      exact ⟨0, Id ((men_cons_neq (Ne.symm hp)).mp h)⟩
  | .TopR, .BotL _ h | .AndR _ _, .BotL _ h | .OrR₀ _, .BotL _ h | .OrR₁ _, .BotL _ h
  | .ImpR _, .BotL _ h =>
    subst ctx
    exact ⟨0, BotL _ (by simpa using h)⟩
  | _, .TopR => exact ⟨0, TopR⟩
  | D₁, .AndR fst snd =>
    subst ctx
    have E₁ := Cut D₁ fst
    have E₂ := Cut D₁ snd
    exact ⟨max E₁.1 E₂.1 + 1,
      AndR (depth_le (Nat.le_max_left _ _) E₁.2) (depth_le (Nat.le_max_right _ _) E₂.2)⟩
  | D₁, .OrR₀ D =>
    subst ctx
    exact ⟨_, OrR₀ (Cut D₁ D).2⟩
  | D₁, .OrR₁ D =>
    subst ctx
    exact ⟨_, OrR₁ (Cut D₁ D).2⟩
  | D₁, .ImpR (n := m) (A := A) (B := B) D =>
    subst ctx
    have D' : Derivation' m (φ ::ₘ A ::ₘ Γ) B := D.Exchange
    exact ⟨_, ImpR (Cut (Weakening (A := A) D₁) D').2⟩
  | D₁, .AndL (n := m) (A := A) (B := B) (Γ := Δ') D =>
    if h : φ = A.and B then
      subst h
      rw [cons_inj_right] at ctx
      subst ctx
      have D' : Derivation' m (B ::ₘ A ::ₘ Γ) ψ := D.Exchange
      have E := Cut (Weakening (A := A) (AndR_inv D₁).2) D'
      exact Cut (AndR_inv D₁).1 E.2
    else
      obtain ⟨h_mem, rfl⟩ := for_commutative ctx h
      have D' : Derivation' m (φ ::ₘ A ::ₘ B ::ₘ Γ.erase (A.and B)) ψ := D.Exchange
      have E := Cut (AndL_inv_mem h_mem D₁) D'
      rw [← cons_erase h_mem]
      exact ⟨_, AndL E.2⟩
  | .OrR₀ (A := A) (B := B) d, .OrL (A := C) (B := E) (Γ := Δ') fst snd =>
    if h : A.or B = C.or E then
      rw [← or_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [cons_inj_right] at ctx
      subst ctx
      exact Cut d fst
    else
      obtain ⟨h_mem, rfl⟩ := for_commutative ctx h
      rw [cons_swap] at fst snd
      have D' := OrL_inv_mem h_mem (OrR₀ (B := B) d)
      have E₁ := Cut D'.1 fst
      have E₂ := Cut D'.2 snd
      rw [← cons_erase h_mem]
      exact ⟨max E₁.1 E₂.1 + 1,
        OrL (depth_le (Nat.le_max_left _ _) E₁.2) (depth_le (Nat.le_max_right _ _) E₂.2)⟩
  | .OrR₁ (A := A) (B := B) d, .OrL (A := C) (B := E) (Γ := Δ') fst snd =>
    if h : A.or B = C.or E then
      rw [← or_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [cons_inj_right] at ctx
      subst ctx
      exact Cut d snd
    else
      obtain ⟨h_mem, rfl⟩ := for_commutative ctx h
      rw [cons_swap] at fst snd
      have D' := OrL_inv_mem h_mem (OrR₁ (A := A) d)
      have E₁ := Cut D'.1 fst
      have E₂ := Cut D'.2 snd
      rw [← cons_erase h_mem]
      exact ⟨max E₁.1 E₂.1 + 1,
        OrL (depth_le (Nat.le_max_left _ _) E₁.2) (depth_le (Nat.le_max_right _ _) E₂.2)⟩
  | .TopR (n := k), .OrL (A := C) (B := E) (Γ := Δ') fst snd =>
    obtain ⟨h_mem, rfl⟩ := for_commutative ctx (by simp)
    rw [cons_swap] at fst snd
    have D' := OrL_inv_mem h_mem (TopR (n := k))
    have E₁ := Cut D'.1 fst
    have E₂ := Cut D'.2 snd
    rw [← cons_erase h_mem]
    exact ⟨max E₁.1 E₂.1 + 1,
      OrL (depth_le (Nat.le_max_left _ _) E₁.2) (depth_le (Nat.le_max_right _ _) E₂.2)⟩
  | .AndR a b, .OrL (A := C) (B := E) (Γ := Δ') fst snd =>
    obtain ⟨h_mem, rfl⟩ := for_commutative ctx (by simp)
    rw [cons_swap] at fst snd
    have D' := OrL_inv_mem h_mem (AndR a b)
    have E₁ := Cut D'.1 fst
    have E₂ := Cut D'.2 snd
    rw [← cons_erase h_mem]
    exact ⟨max E₁.1 E₂.1 + 1,
      OrL (depth_le (Nat.le_max_left _ _) E₁.2) (depth_le (Nat.le_max_right _ _) E₂.2)⟩
  | .ImpR a, .OrL (A := C) (B := E) (Γ := Δ') fst snd =>
    obtain ⟨h_mem, rfl⟩ := for_commutative ctx (by simp)
    rw [cons_swap] at fst snd
    have D' := OrL_inv_mem h_mem (ImpR a)
    have E₁ := Cut D'.1 fst
    have E₂ := Cut D'.2 snd
    rw [← cons_erase h_mem]
    exact ⟨max E₁.1 E₂.1 + 1,
      OrL (depth_le (Nat.le_max_left _ _) E₁.2) (depth_le (Nat.le_max_right _ _) E₂.2)⟩
  | D₁, .ImpL (n := m) (A := C) (B := E) (Γ := Δ') fst snd =>
    if h : φ = C.imp E then
      subst h
      rw [cons_inj_right] at ctx
      subst ctx
      have E₁ := Cut D₁ fst
      have E₂ := Cut (Weakening (A := E) D₁) snd
      have E₃ := Cut E₁.2 (ImpR_inv D₁)
      exact Cut E₃.2 E₂.2
    else
      obtain ⟨h_mem, rfl⟩ := for_commutative ctx h
      have fst' : Derivation' m (φ ::ₘ C.imp E ::ₘ Γ.erase (C.imp E)) C := fst.Exchange
      have snd' : Derivation' m (φ ::ₘ C.imp E ::ₘ E ::ₘ Γ.erase (C.imp E)) ψ := snd.Exchange
      have D₁' : Derivation' n₁ (C.imp E ::ₘ Γ.erase (C.imp E)) φ := by
        rw [cons_erase h_mem]; exact D₁
      have D₁'' : Derivation' n₁ (C.imp E ::ₘ E ::ₘ Γ.erase (C.imp E)) φ :=
        (Weakening (A := E) D₁').Exchange
      have E₁ := Cut D₁' fst'
      have E₂ := Cut D₁'' snd'
      rw [← cons_erase h_mem]
      exact ⟨max E₁.1 E₂.1 + 1,
        ImpL (depth_le (Nat.le_max_left _ _) E₁.2) (depth_le (Nat.le_max_right _ _) E₂.2)⟩
  termination_by (φ.size, n₁ + n₂)
  decreasing_by
    all_goals
      subst_vars
      first
        | (apply Prod.Lex.right; omega)
        | (apply Prod.Lex.left; simp only [Formula.size]; omega)

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
