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
  | .AndL (n := n) (A := A') (B := B') D => by
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
  | .OrL (n := n) (A := A') (B := B') fst snd => by
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

abbrev CtrP (A : Formula) : Prop :=
  ∀ {n Γ B}, Derivation' n (A ::ₘ A ::ₘ Γ) B → Nonempty (Derivation' n (A ::ₘ Γ) B)

theorem ctr_mem_dup {x A : Formula} {Δ : Multiset Formula} (h : x ∈ A ::ₘ A ::ₘ Δ) :
    x ∈ A ::ₘ Δ := by
  simp only [mem_cons] at h ⊢; tauto

theorem ctr_ex {n Γ Γ' B} (h : Γ = Γ') (D : Nonempty (Derivation' n Γ B)) :
    Nonempty (Derivation' n Γ' B) := h ▸ D

theorem ctr_to {X : Formula} {Γ1 Γ2 Γ3 : Multiset Formula} {n B} (hA : CtrP X)
    (h1 : Γ1 = X ::ₘ X ::ₘ Γ2) (h2 : X ::ₘ Γ2 = Γ3) (D : Derivation' n Γ1 B) :
    Nonempty (Derivation' n Γ3 B) := by
  subst h1 h2; exact hA D

theorem ctr_split {φ A : Formula} {Γ' Δ : Multiset Formula}
    (h : φ ::ₘ Γ' = A ::ₘ A ::ₘ Δ) (hne : φ ≠ A) :
    ∃ Δ0, Γ' = A ::ₘ A ::ₘ Δ0 ∧ Δ = φ ::ₘ Δ0 := by
  obtain ⟨h1, h2⟩ := for_commutative h hne
  obtain ⟨h3, h4⟩ := for_commutative h2.symm hne
  refine ⟨(Γ'.erase A).erase A, ?_, h4⟩
  rw [cons_erase h3, cons_erase h1]

theorem invimp_mem (X Y : Formula) (hD : CtrP Y) {n Γ C} :
    Derivation' n Γ C → imp X Y ∈ Γ → Nonempty (Derivation' n (Y ::ₘ Γ.erase (imp X Y)) C)
  | .Id h, _ => by
    rw [← mem_erase_of_ne (b := imp X Y) (by simp)] at h
    exact ⟨.Id (mem_cons_of_mem h)⟩
  | .BotL φ h, _ => by
    rw [← mem_erase_of_ne (b := imp X Y) (by simp)] at h
    exact ⟨.BotL φ (mem_cons_of_mem h)⟩
  | .TopR, _ => ⟨.TopR⟩
  | .AndR fst snd, hm => by
    obtain ⟨f⟩ := invimp_mem X Y hD fst hm
    obtain ⟨s⟩ := invimp_mem X Y hD snd hm
    exact ⟨.AndR f s⟩
  | .OrR₀ D, hm => by
    obtain ⟨f⟩ := invimp_mem X Y hD D hm
    exact ⟨.OrR₀ f⟩
  | .OrR₁ D, hm => by
    obtain ⟨f⟩ := invimp_mem X Y hD D hm
    exact ⟨.OrR₁ f⟩
  | .ImpR (A := A') D, hm => by
    obtain ⟨f⟩ := invimp_mem X Y hD D (mem_cons_of_mem hm)
    rw [erase_cons_tail_of_mem hm, cons_swap] at f
    exact ⟨.ImpR f⟩
  | .AndL (n := n) (A := A') (B := B') (C := C') (Γ := Γ') D, hm => by
    rw [men_cons_neq] at hm
    obtain ⟨f⟩ := invimp_mem X Y hD D (mem_cons_of_mem (mem_cons_of_mem hm))
    rw [erase_cons_tail_of_mem_2x hm] at f
    rw [erase_cons_tail_of_mem hm]
    obtain ⟨g⟩ : Nonempty (Derivation' n (A' ::ₘ B' ::ₘ Y ::ₘ Γ'.erase (imp X Y)) C') :=
      ctr_ex (by simp) ⟨f⟩
    exact ctr_ex (by simp) ⟨Derivation'.AndL g⟩
  | .OrL (n := n) (A := A') (B := B') (C := C') (Γ := Γ') fst snd, hm => by
    rw [men_cons_neq] at hm
    obtain ⟨f⟩ := invimp_mem X Y hD fst (mem_cons_of_mem hm)
    obtain ⟨s⟩ := invimp_mem X Y hD snd (mem_cons_of_mem hm)
    rw [erase_cons_tail_of_mem hm] at f s
    rw [erase_cons_tail_of_mem hm]
    obtain ⟨f'⟩ : Nonempty (Derivation' n (A' ::ₘ Y ::ₘ Γ'.erase (imp X Y)) C') :=
      ctr_ex (by simp) ⟨f⟩
    obtain ⟨s'⟩ : Nonempty (Derivation' n (B' ::ₘ Y ::ₘ Γ'.erase (imp X Y)) C') :=
      ctr_ex (by simp) ⟨s⟩
    exact ctr_ex (by simp) ⟨Derivation'.OrL f' s'⟩
  | .ImpL (n := n) (A := A') (B := B') (C := C') (Γ := Γ') fst snd, hm => by
    by_cases h : imp X Y = imp A' B'
    · obtain ⟨rfl, rfl⟩ := imp_eq.2 h
      obtain ⟨s⟩ := invimp_mem X Y hD snd (mem_cons_self _ _)
      rw [erase_cons_head] at s
      obtain ⟨s'⟩ := hD s
      rw [erase_cons_head]
      exact ⟨s'.depth_succ⟩
    · have hm' := Or.resolve_left (mem_cons.1 hm) h
      obtain ⟨f⟩ := invimp_mem X Y hD fst (mem_cons_of_mem hm')
      obtain ⟨s⟩ := invimp_mem X Y hD snd (mem_cons_of_mem (mem_cons_of_mem hm'))
      rw [erase_cons_tail_of_mem hm'] at f
      rw [erase_cons_tail_of_mem_2x hm'] at s
      rw [erase_cons_tail_of_mem hm']
      obtain ⟨f'⟩ : Nonempty (Derivation' n (imp A' B' ::ₘ Y ::ₘ Γ'.erase (imp X Y)) A') :=
        ctr_ex (by simp) ⟨f⟩
      obtain ⟨s'⟩ : Nonempty (Derivation' n (imp A' B' ::ₘ B' ::ₘ Y ::ₘ Γ'.erase (imp X Y)) C') :=
        ctr_ex (by simp) ⟨s⟩
      exact ctr_ex (by simp) ⟨Derivation'.ImpL f' s'⟩

theorem invimp (X Y : Formula) (hD : CtrP Y) {n Γ C}
    (D : Derivation' n (imp X Y ::ₘ Γ) C) : Nonempty (Derivation' n (Y ::ₘ Γ) C) := by
  have := invimp_mem X Y hD D (mem_cons_self _ _)
  rwa [erase_cons_head] at this

theorem ctr_main (A : Formula) (H : ∀ φ : Formula, φ.size < A.size → CtrP φ) {n Γ B} :
    Derivation' n Γ B → ∀ (Δ : Multiset Formula), Γ = A ::ₘ A ::ₘ Δ →
      Nonempty (Derivation' n (A ::ₘ Δ) B)
  | .Id h, Δ, hΓ => by subst hΓ; exact ⟨.Id (ctr_mem_dup h)⟩
  | .BotL φ h, Δ, hΓ => by subst hΓ; exact ⟨.BotL φ (ctr_mem_dup h)⟩
  | .TopR, Δ, hΓ => ⟨.TopR⟩
  | .AndR fst snd, Δ, hΓ => by
    obtain ⟨f⟩ := ctr_main A H fst Δ hΓ
    obtain ⟨s⟩ := ctr_main A H snd Δ hΓ
    exact ⟨.AndR f s⟩
  | .OrR₀ D, Δ, hΓ => by
    obtain ⟨f⟩ := ctr_main A H D Δ hΓ
    exact ⟨.OrR₀ f⟩
  | .OrR₁ D, Δ, hΓ => by
    obtain ⟨f⟩ := ctr_main A H D Δ hΓ
    exact ⟨.OrR₁ f⟩
  | .ImpR (A := A') D, Δ, hΓ => by
    subst hΓ
    obtain ⟨f⟩ := ctr_main A H D (A' ::ₘ Δ) (by simp)
    rw [cons_swap] at f
    exact ⟨.ImpR f⟩
  | .AndL (n := n) (A := A') (B := B') (C := C') (Γ := Γ') D, Δ, hΓ => by
    by_cases hφ : and A' B' = A
    · subst hφ
      have hΓ' := (cons_inj_right _).1 hΓ
      subst hΓ'
      obtain ⟨D1⟩ : Nonempty (Derivation' n (and A' B' ::ₘ A' ::ₘ B' ::ₘ Δ) C') :=
        ctr_ex (by simp) ⟨D⟩
      have D2 := AndL_inv D1
      obtain ⟨c1⟩ := ctr_to (H A' (by simp only [Formula.size]; omega))
        (Γ2 := B' ::ₘ B' ::ₘ Δ) (Γ3 := A' ::ₘ B' ::ₘ B' ::ₘ Δ) (by simp) rfl D2
      obtain ⟨c2⟩ := ctr_to (H B' (by simp only [Formula.size]; omega))
        (Γ2 := A' ::ₘ Δ) (Γ3 := A' ::ₘ B' ::ₘ Δ) (by simp) (by simp) c1
      exact ⟨.AndL c2⟩
    · obtain ⟨Δ0, rfl, rfl⟩ := ctr_split hΓ hφ
      obtain ⟨f⟩ := ctr_main A H D (A' ::ₘ B' ::ₘ Δ0) (by simp)
      obtain ⟨g⟩ : Nonempty (Derivation' n (A' ::ₘ B' ::ₘ A ::ₘ Δ0) C') := ctr_ex (by simp) ⟨f⟩
      exact ctr_ex (by simp) ⟨Derivation'.AndL g⟩
  | .OrL (n := n) (A := A') (B := B') (C := C') (Γ := Γ') fst snd, Δ, hΓ => by
    by_cases hφ : or A' B' = A
    · subst hφ
      have hΓ' := (cons_inj_right _).1 hΓ
      subst hΓ'
      obtain ⟨f1⟩ : Nonempty (Derivation' n (or A' B' ::ₘ A' ::ₘ Δ) C') := ctr_ex (by simp) ⟨fst⟩
      obtain ⟨s1⟩ : Nonempty (Derivation' n (or A' B' ::ₘ B' ::ₘ Δ) C') := ctr_ex (by simp) ⟨snd⟩
      obtain ⟨f⟩ := ctr_to (H A' (by simp only [Formula.size]; omega))
        (Γ2 := Δ) (Γ3 := A' ::ₘ Δ) rfl rfl (OrL_inv f1).1
      obtain ⟨s⟩ := ctr_to (H B' (by simp only [Formula.size]; omega))
        (Γ2 := Δ) (Γ3 := B' ::ₘ Δ) rfl rfl (OrL_inv s1).2
      exact ⟨.OrL f s⟩
    · obtain ⟨Δ0, rfl, rfl⟩ := ctr_split hΓ hφ
      obtain ⟨f⟩ := ctr_main A H fst (A' ::ₘ Δ0) (by simp)
      obtain ⟨s⟩ := ctr_main A H snd (B' ::ₘ Δ0) (by simp)
      obtain ⟨f'⟩ : Nonempty (Derivation' n (A' ::ₘ A ::ₘ Δ0) C') := ctr_ex (by simp) ⟨f⟩
      obtain ⟨s'⟩ : Nonempty (Derivation' n (B' ::ₘ A ::ₘ Δ0) C') := ctr_ex (by simp) ⟨s⟩
      exact ctr_ex (by simp) ⟨Derivation'.OrL f' s'⟩
  | .ImpL (n := n) (A := A') (B := B') (C := C') (Γ := Γ') fst snd, Δ, hΓ => by
    by_cases hφ : imp A' B' = A
    · subst hφ
      have hΓ' := (cons_inj_right _).1 hΓ
      subst hΓ'
      obtain ⟨f⟩ := ctr_main _ H fst Δ rfl
      obtain ⟨s⟩ := invimp A' B' (H B' (by simp only [Formula.size]; omega)) snd
      obtain ⟨s2⟩ := ctr_to (H B' (by simp only [Formula.size]; omega))
        (Γ2 := imp A' B' ::ₘ Δ) (Γ3 := imp A' B' ::ₘ B' ::ₘ Δ) rfl (by simp) s
      exact ⟨.ImpL f s2⟩
    · obtain ⟨Δ0, rfl, rfl⟩ := ctr_split hΓ hφ
      obtain ⟨f⟩ := ctr_main A H fst (imp A' B' ::ₘ Δ0) (by simp)
      obtain ⟨s⟩ := ctr_main A H snd (imp A' B' ::ₘ B' ::ₘ Δ0) (by simp)
      obtain ⟨f'⟩ : Nonempty (Derivation' n (imp A' B' ::ₘ A ::ₘ Δ0) A') := ctr_ex (by simp) ⟨f⟩
      obtain ⟨s'⟩ : Nonempty (Derivation' n (imp A' B' ::ₘ B' ::ₘ A ::ₘ Δ0) C') :=
        ctr_ex (by simp) ⟨s⟩
      exact ctr_ex (by simp) ⟨Derivation'.ImpL f' s'⟩

theorem ctr_all' : ∀ (m : Nat) (A : Formula), A.size = m → CtrP A := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro A hm n Γ B D
    exact ctr_main A (fun φ hφ => ih φ.size (by omega) φ rfl) D Γ rfl

theorem ctr_all (A : Formula) : CtrP A := ctr_all' _ A rfl

noncomputable def Contraction :
  Derivation' n (A ::ₘ A ::ₘ Γ) B → Derivation' n (A ::ₘ Γ) B :=
  fun D => (ctr_all A D).some

set_option maxHeartbeats 1000000 in
-- Relaxed maxHeartbeats to verify massive pattern matching and termination proofs.
-- set_option trace.profiler true in
-- set_option diagnostics true in
def Cut (D₁ : Derivation' n₁ Γ φ) (D₂ : Derivation' n₂ (φ ::ₘ Γ) ψ) :
  Σ k, Derivation' k Γ ψ := by
  sorry

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

noncomputable def Contraction {Γ A B} :
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
