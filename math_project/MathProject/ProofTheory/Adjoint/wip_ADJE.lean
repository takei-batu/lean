import Mathlib.Order.Defs.LinearOrder
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Replicate
import MathProject.ProofTheory.Adjoint.mode
import MathProject.ProofTheory.Adjoint.formula

/-!
# ADJE
-/

variable {α : Type} [DecidableEq α] in
lemma multiset_sub_eq_singleton_iff {a : α} {s t : Multiset α} (h : t ≤ s) :
  s - t = {a} ↔ s = a ::ₘ t := by
  constructor
  · intro h₁
    rw [← Multiset.add_sub_cancel h, h₁, Multiset.singleton_add]
  · intro h₂
    rw [h₂, ← Multiset.singleton_add, Multiset.add_sub_cancel_right]

namespace ADJE

variable {M : Type} [Preorder M] [DecidableEq M]

open Formula
open Multiset

/- declaration of independence -/
abbrev DoI (Γ : Multiset (MFormula M)) (k : M) : Prop :=
  ∀ 𝒜 ∈ Γ, 𝒜.1 ≥ k

/- using Γ ≥ₘ k ↔ ∀ 𝒜 ∈ Γ, 𝒜.1 ≥ k -/
infix:50 " ≥ₘ " => DoI

omit [DecidableEq M] in
theorem DoI_cons {k 𝒜} (Γ : Multiset (MFormula M)) : 𝒜 ::ₘ Γ ≥ₘ k → Γ ≥ₘ k := by
  intro h x hx
  exact h x (mem_cons_of_mem hx)

theorem DoI_erase {k 𝒜} (Γ : Multiset (MFormula M)) : Γ ≥ₘ k → Γ.erase 𝒜 ≥ₘ k := by
  intro h x hx
  exact h x (mem_of_mem_erase hx)

/- Sequent for ADJE -/
inductive Derivation [HasSigma M] : Multiset (MFormula M) → {m : M} → Formula m -> Type where
| Id {A : Formula m}:
  Derivation {⟨m, A⟩} A
/- Structural -/
| Weakening {A : Formula m} {C : Formula k} :
  (h : 𝒲 ∈ σ m) → Derivation Γ C →
  Derivation (⟨m, A⟩ ::ₘ Γ) C
| Contraction {A : Formula m} {C : Formula k} :
  (h : 𝒞 ∈ σ m) →
  Derivation (⟨m, A⟩ ::ₘ ⟨m, A⟩ ::ₘ Γ) C →
  Derivation (⟨m, A⟩ ::ₘ Γ) C
/- Plus and Zero -/
| Plus_L {A B : Formula m} {C : Formula k} :
  Derivation (⟨m, A⟩ ::ₘ Γ) C →
  Derivation (⟨m, B⟩ ::ₘ Γ) C →
  Derivation (⟨m, Plus A B⟩ ::ₘ Γ) C
| Plus_R_1 {A B : Formula m} :
  Derivation Γ A →
  Derivation Γ (Plus A B)
| Plus_R_2 {A B : Formula m} :
  Derivation Γ B →
  Derivation Γ (Plus A B)
| Zero_L {A B : Formula m} {C : Formula k} :
  Derivation (⟨m, Zero⟩ ::ₘ Γ) C
-- no Zero_R
/- With and Top -/
| With_L_1 {A B : Formula m} {C : Formula k} :
  Derivation (⟨m, A⟩ ::ₘ Γ) C →
  Derivation (⟨m, With A B⟩ ::ₘ Γ) C
| With_L_2 {A B : Formula m} {C : Formula k} :
  Derivation (⟨m, B⟩ ::ₘ Γ) C →
  Derivation (⟨m, With A B⟩ ::ₘ Γ) C
| With_R {A B : Formula m} :
  Derivation Γ A →
  Derivation Γ B →
  Derivation Γ (With A B)
-- no Top_L
| Top_R :
  Derivation Γ Top
/- Tensor and One -/
| Tensor_L {A B : Formula m} {C : Formula k} :
  Derivation (⟨m, A⟩ ::ₘ ⟨m, B⟩ ::ₘ Γ) C →
  Derivation (⟨m, Tensor A B⟩ ::ₘ Γ) C
| Tensor_R {A B : Formula m} :
  (sub : Γ₁ ≤ Γ) →
  Derivation Γ₁ A →
  Derivation (Γ - Γ₁) B →
  Derivation Γ (Tensor A B)
| One_L {C : Formula k} :
  Derivation Γ C →
  Derivation (⟨m, One⟩ ::ₘ Γ) C
| One_R :
  Derivation {} One
/- Imp -/
| Imp_L {A B : Formula m} {C : Formula k} :
  (sub : Γ₁ ≤ Γ) →
  (side : Γ₁ ≥ₘ m) →
  Derivation Γ₁ A →
  Derivation (⟨m, B⟩ ::ₘ (Γ - Γ₁)) C →
  Derivation (⟨m, Imp A B⟩ ::ₘ Γ) C
| Imp_R {A B : Formula m} :
  Derivation (⟨m, A⟩ ::ₘ Γ) B →
  Derivation Γ (Imp A B)
/- Shift -/
| Down_L {h : m ≤ l} {A : Formula l} {C : Formula k} :
  Derivation (⟨l, A⟩ ::ₘ Γ) C →
  Derivation (⟨m, Down h A⟩ ::ₘ Γ) C
| Down_R {h : m ≤ l} {A : Formula l} :
  (side : Γ ≥ₘ l) →
  Derivation Γ A →
  Derivation Γ (Down h A)
| Up_L {h : k ≤ m} {A : Formula k} {C : Formula l} :
  (side : k ≥ l) →
  Derivation (⟨k, A⟩ ::ₘ Γ) C →
  Derivation (⟨m, Up h A⟩ ::ₘ Γ) C
| Up_R {h : k ≤ m} {A : Formula k} :
  Derivation Γ A →
  Derivation Γ (Up h A)

/-- cons_n n 𝒜 Γ = 𝒜 ::ₘ ... ::ₘ 𝒜 ::ₘ Γ -/
@[simp]
def cons_n (n : Nat) (𝒜 : MFormula M) (Γ : Multiset (MFormula M)) : Multiset (MFormula M) :=
  match n with
  | 0 => Γ
  | n + 1 => 𝒜 ::ₘ cons_n n 𝒜 Γ

def Contraction_n [HasSigma M] {m : M} {A : Formula m} {C : Formula k}
    (n : Nat) (h : 𝒞 ∈ σ m)
    (ℰ : Derivation (cons_n (n + 1) ⟨m, A⟩ Γ) C) :
    Derivation (⟨m, A⟩ ::ₘ Γ) C :=
  match n with
  | 0 => ℰ
  | n + 1 => Contraction_n n h (.Contraction h ℰ)

@[simp]
def mu (m : M) [HasSigma M] : Set Nat := {n : Nat | (n = 0 ∧ 𝒲 ∈ σ m) ∨ n = 1 ∨ (n ≥ 2 ∧ 𝒞 ∈ σ m)}

local notation "μ" => mu

omit [DecidableEq M] in
lemma iff_zero (m : M) [HasSigma M] : 0 ∈ μ m ↔ 𝒲 ∈ σ m := by
  simp?

omit [DecidableEq M] in
lemma iff_one (m : M) [HasSigma M] : 1 ∈ μ m ↔ true := by
  simp?

omit [DecidableEq M] in
lemma iff_two (h : n ≥ 2) (m : M) [HasSigma M] : n ∈ μ m ↔ 𝒞 ∈ σ m := by
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  simp? [h, h0, h1]

/- General Identity -/
/- noncomputable を外せるか？ → 現状では不可能！ADJIで示すべき -/
omit [DecidableEq M] in
variable [HasSigma M] in
noncomputable def Identity {m k : M} {A : Formula k} {Γ : Multiset (MFormula M)}
    (side : Γ ≥ₘ m) (h : 𝒲 ∈ σ m) : Derivation (⟨k, A⟩ ::ₘ Γ) A := by
  suffices Nonempty (Derivation (⟨k, A⟩ ::ₘ Γ) A) from Classical.choice this
  induction Γ using Multiset.induction_on with
  | empty =>
    exact ⟨.Id⟩
  | cons 𝒜 Γ ih =>
    rcases 𝒜 with ⟨l, B⟩
    rcases ih (DoI_cons Γ side) with ⟨D⟩
    have hm : m ≤ l := side ⟨l, B⟩ (mem_cons_self ⟨l, B⟩ Γ)
    have hW : 𝒲 ∈ σ l := σ.monotone hm h
    rw [cons_swap]
    exact ⟨.Weakening hW D⟩

/- General Weakening -/
/- General Contraction -/

open Derivation in
variable [HasSigma M] in
def Multicut {m : M} {φ : Formula m} {C : Formula k}
  (n : Nat) (sub : Γ₁ ≤ Γ) (side : Γ₁ ≥ₘ m ∧ m ≥ k) (h : n ∈ μ m)
  (𝒟 : Derivation Γ₁ φ) (ℰ : Derivation (cons_n n ⟨m, φ⟩ (Γ - Γ₁)) C) :
  Derivation Γ C := by
  generalize ctx : (cons_n n ⟨m, φ⟩ (Γ - Γ₁)) = Δ at ℰ
  match h₁ : φ, h₂ : 𝒟, h₃ : ℰ with
  | A, .Id, _ =>
    subst_vars
    match n with
    | 0 =>
      simp only [cons_n] at ℰ
      rw [←erase_cons_head ⟨m, A⟩ Γ, ←sub_singleton, cons_sub_of_le ⟨m, A⟩ sub]
      rw[iff_zero] at h
      exact Weakening (A := A) h ℰ
    | 1 =>
      simp only [cons_n, ←cons_sub_of_le ⟨m, A⟩ sub] at ℰ
      simp only [sub_singleton, erase_cons_head] at ℰ
      exact ℰ
    | n + 2 =>
      rw[iff_two (by omega)] at h
      have ℰ' := Contraction_n (n+1) h ℰ
      simp only [←cons_sub_of_le ⟨m, A⟩ sub] at ℰ'
      simp only [sub_singleton, erase_cons_head] at ℰ'
      exact ℰ'
  | A, _, .Id =>
    subst_vars
    match n with
    | 0 =>
      simp only [cons_n] at ctx
      rw[multiset_sub_eq_singleton_iff sub] at ctx
      rw[ctx]
      sorry
    | 1 =>
      simp only [cons_n] at ctx
      sorry
    | n + 2 =>
      simp only [cons_n] at ctx
      -- nomatch
      sorry
  | _, _, _ => sorry

end ADJE
