import Mathlib.Data.Set.Basic
import MathProject.Logic.formula

open prop

abbrev Theory := Set Formula

/-
  NK for Propositional Logic
  bottom-up の形式化（have tactic を使えば top-down も可）
  DNE の代わりに LEM を公理とする（通常の Gentzen の NK は NJ + DNE）
-/
namespace NK

inductive Provable : Theory → Formula → Prop where
  | Axiom (ϕ : Formula) :
    (h : ϕ ∈ Γ := by aesop) →
    Provable Γ ϕ
  | Imp_Intro :
    Provable (Γ ∪ {ϕ}) ψ →
    Provable Γ (.imp ϕ ψ)
  | Imp_Elim :
    Provable Γ (.imp ϕ ψ) →
    Provable Γ ϕ →
    Provable Γ ψ
  | And_Intro :
    Provable Γ ϕ →
    Provable Γ ψ →
    Provable Γ (.and ϕ ψ)
  | And_Elim_Left :
    Provable Γ (.and ϕ ψ) →
    Provable Γ ϕ
  | And_Elim_Right :
    Provable Γ (.and ϕ ψ) →
    Provable Γ ψ
  | Or_Intro_Left  :
    Provable Γ ϕ →
    Provable Γ (.or ϕ ψ)
  | Or_Intro_Right :
    Provable Γ ψ →
    Provable Γ (.or ϕ ψ)
  | Or_Elim :
    Provable Γ (.or ϕ ψ) →
    Provable (Γ ∪ {ϕ}) C →
    Provable (Γ ∪ {ψ}) C →
    Provable Γ C
  | Not_Intro :
    Provable (Γ ∪ {ϕ}) .bot →
    Provable Γ (.not ϕ)
  | Not_Elim :
    Provable Γ ϕ →
    Provable Γ (.not ϕ) →
    Provable Γ .bot
  | EXP :
    Provable Γ .bot →
    Provable Γ ϕ
  | LEM (ϕ : Formula) : Provable Γ (ϕ.or ϕ.not)

infix:50 " ⊢ " => Provable

open Provable

theorem weaking : Γ ⊆ Δ → Γ ⊢ ϕ → Δ ⊢ ϕ := by
  intro sub h
  induction h generalizing Δ with
  | Axiom A =>
    apply Axiom A
  | Imp_Intro h ih =>
    rename_i _ A _
    apply Imp_Intro
    · replace sub := Set.union_subset_union_left {A} sub
      exact ih sub
  | Imp_Elim h₁ h₂ ih₁ ih₂ =>
    rename_i _ A _
    apply Imp_Elim (ϕ := A)
    · exact ih₁ sub
    · exact ih₂ sub
  | And_Intro h₁ h₂ ih₁ ih₂ =>
    apply And_Intro
    · exact ih₁ sub
    · exact ih₂ sub
  | And_Elim_Left h ih =>
    apply And_Elim_Left
    · exact ih sub
  | And_Elim_Right h ih =>
    apply And_Elim_Right
    · exact ih sub
  | Or_Intro_Left h ih =>
    apply Or_Intro_Left
    · exact ih sub
  | Or_Intro_Right h ih =>
    apply Or_Intro_Right
    · exact ih sub
  | Or_Elim h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    rename_i _ A B _
    apply Or_Elim (ϕ := A) (ψ := B)
    · exact ih₁ sub
    · replace sub := Set.union_subset_union_left {A} sub
      exact ih₂ sub
    · replace sub := Set.union_subset_union_left {B} sub
      exact ih₃ sub
  | Not_Intro h ih =>
    rename_i _ A
    apply Not_Intro
    · replace sub := Set.union_subset_union_left {A} sub
      exact ih sub
  | Not_Elim h₁ h₂ ih₁ ih₂ =>
    apply Not_Elim
    · exact ih₁ sub
    · exact ih₂ sub
  | EXP h ih =>
    apply EXP
    · exact ih sub
  | LEM A =>
    apply LEM

theorem deduction : Γ ∪ {A} ⊢ B ↔ Γ ⊢ (.imp A B) := by
  constructor
  · apply Imp_Intro
  · intro h
    have : Γ ⊆ Γ ∪ {A} := by aesop
    apply Imp_Elim (ϕ := A)
    · apply weaking this h
    · apply Axiom A

theorem DNE_Axiom (A : Formula) : Γ ⊢ .imp A.not.not A := by
  apply Imp_Intro
  · apply Or_Elim
    · apply LEM A
    · apply Axiom A
    · apply EXP
      · apply Not_Elim (ϕ := A.not)
        · apply Axiom A.not
        · apply Axiom A.not.not

theorem DNE (A : Formula) : Γ ⊢ A.not.not → Γ ⊢ A := by
  intro h
  apply Imp_Elim (ϕ := A.not.not)
  · apply DNE_Axiom A
  · assumption

theorem RAA : Γ ∪ {.not A} ⊢ .bot → Γ ⊢ A := by
  intro h
  apply DNE
  apply Not_Intro
  assumption

end NK

section test

open NK Provable

variable (A B : Formula)

example : {} ⊢ .imp A A := by
  apply Imp_Intro
  apply Axiom A

example : {} ⊢ A.imp (B.imp A) := by
  apply Imp_Intro
  apply Imp_Intro
  apply Axiom A

end test

namespace semantics

abbrev Assignment := String → Prop

-- Truth Function associated with Assignment
def TF (v : Assignment) (ϕ : Formula) : Prop :=
  match ϕ with
  | .atom name => v name
  | .bot => False
  | .imp A B => TF v A → TF v B

lemma Truth_Not : TF v (ϕ.not) ↔ ¬ TF v ϕ := by
  dsimp [Formula.not, TF]
  grind

lemma Truth_Or : TF v (ϕ.or ψ) ↔ TF v ϕ ∨ TF v ψ := by
  dsimp [Formula.or, Formula.not, TF]
  grind

lemma Truth_And : TF v (ϕ.and ψ) ↔ TF v ϕ ∧ TF v ψ := by
  dsimp [Formula.and, Formula.or, Formula.not, TF]
  grind

def Valid (v : Assignment) (Γ : Theory) (ϕ : Formula) : Prop :=
  (∀ γ ∈ Γ, TF v γ) → TF v ϕ

def Model (Γ : Theory) (ϕ : Formula) : Prop :=
  ∀ v : Assignment, Valid v Γ ϕ

infix:50 " ⊨ " => Model

theorem weaking : Γ ⊆ Δ → Γ ⊨ ϕ → Δ ⊨ ϕ := by
  intro sub h v g
  rw[Model] at h
  have h₁ := h v
  have h₂ : ∀ (γ : Formula), γ ∈ Γ → TF v γ := by
    intro γ hγ
    apply g
    exact sub hγ
  exact h₁ h₂

end semantics

open NK semantics

theorem soundness : Γ ⊢ ϕ → Γ ⊨ ϕ := by
  intro h v g
  induction h with
  | Axiom A ih => exact g A ih
  | Imp_Intro h ih =>
    rename_i Δ A B
    intro hA
    have : ∀ (γ : Formula), γ ∈ Δ ∪ {A} → TF v γ := by
      rintro γ (h_in | rfl)
      · exact g γ h_in
      · exact hA
    exact ih this
  | Imp_Elim h₁ h₂ ih₁ ih₂ => exact ih₁ g (ih₂ g)
  | And_Intro h₁ h₂ ih₁ ih₂ =>
    rw[Truth_And]
    exact ⟨ih₁ g , ih₂ g⟩
  | And_Elim_Left h ih =>
    have := ih g
    rw[Truth_And] at this
    exact this.left
  | And_Elim_Right h ih =>
    have := ih g
    rw[Truth_And] at this
    exact this.right
  | Or_Intro_Left h ih =>
    rw[Truth_Or]
    exact Or.inl (ih g)
  | Or_Intro_Right h ih =>
    rw[Truth_Or]
    exact Or.inr (ih g)
  | Or_Elim h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    rename_i Δ A B C
    rw[Truth_Or] at ih₁
    apply Or.elim (ih₁ g)
    · intro hA
      have : ∀ (γ : Formula), γ ∈ Δ ∪ {A} → TF v γ := by
        rintro γ (h_in | rfl)
        · exact g γ h_in
        · exact hA
      exact ih₂ this
    · intro hB
      have : ∀ (γ : Formula), γ ∈ Δ ∪ {B} → TF v γ := by
        rintro γ (h_in | rfl)
        · exact g γ h_in
        · exact hB
      exact ih₃ this
  | Not_Intro h ih =>
    rename_i Δ A
    intro hA
    have : ∀ (γ : Formula), γ ∈ Δ ∪ {A} → TF v γ := by
      rintro γ (h_in | rfl)
      · exact g γ h_in
      · exact hA
    exact ih this
  | Not_Elim h₁ h₂ ih₁ ih₂ => exact (ih₂ g) (ih₁ g)
  | EXP h ih =>
    have := ih g
    contradiction
  | LEM A =>
    rw[Truth_Or]
    open Classical in
    exact Classical.em (TF v A)

-- theorem completeness : Γ ⊨ ϕ → Γ ⊢ ϕ := by sorry
