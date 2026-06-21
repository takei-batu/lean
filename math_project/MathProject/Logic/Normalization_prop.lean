import Mathlib.Data.Set.Basic
import MathProject.Logic.formula
import MathProject.Logic.prop

open prop
open NK

inductive Tree where
  | leaf (ϕ : Formula) : Tree
  | unary (T : Tree) (ϕ : Formula) : Tree
  | binary (T₁ T₂ : Tree) (ϕ : Formula) : Tree
  | trinary (T₁ T₂ T₃ : Tree) (ϕ : Formula) : Tree
deriving Repr, DecidableEq

def Consequence : Tree → Formula
  | .leaf ϕ => ϕ
  | .unary _ ϕ => ϕ
  | .binary _ _ ϕ => ϕ
  | .trinary _ _ _ ϕ => ϕ

inductive Proof : Theory → Tree → Prop where
  | Axiom (ϕ : Formula) :
    (h : ϕ ∈ Γ := by aesop) →
    Proof Γ (.leaf ϕ)
  | Imp_Intro :
    Proof (Γ ∪ {ϕ}) T →
    Consequence T = ψ →
    Proof Γ (.unary T (.imp ϕ ψ))
  | Imp_Elim :
    Proof Γ T₁ → Consequence T₁ = .imp ϕ ψ →
    Proof Γ T₂ → Consequence T₂ = ϕ →
    Proof Γ (.binary T₁ T₂ ψ)
  | And_Intro :
    Proof Γ T₁ → Consequence T₁ = ϕ →
    Proof Γ T₂ → Consequence T₂ = ψ →
    Proof Γ (.binary T₁ T₂ (.and ϕ ψ))
  | And_Elim_Left :
    Proof Γ T → Consequence T = .and ϕ _ →
    Proof Γ (.unary T ϕ)
  | And_Elim_Right :
    Proof Γ T → Consequence T = .and _ ψ →
    Proof Γ (.unary T ψ)
  | Or_Intro_Left :
    Proof Γ T → Consequence T = ϕ →
    Proof Γ (.unary T (.or ϕ ψ))
  | Or_Intro_Right :
    Proof Γ T → Consequence T = ψ →
    Proof Γ (.unary T (.or ϕ ψ))
  | Or_Elim :
    Proof Γ T₁ → Consequence T₁ = .or ϕ ψ →
    Proof (Γ ∪ {ϕ}) T₂ → Consequence T₂ = C →
    Proof (Γ ∪ {ψ}) T₃ → Consequence T₃ = C →
    Proof Γ (.trinary T₁ T₂ T₃ C)
  | Not_Intro :
    Proof (Γ ∪ {ϕ}) T → Consequence T = .bot →
    Proof Γ (.unary T (.not ϕ))
  | Not_Elim :
    Proof Γ T₁ → Consequence T₁ = ϕ →
    Proof Γ T₂ → Consequence T₂ = .not ϕ →
    Proof Γ (.binary T₁ T₂ .bot)
  | EXP :
    Proof Γ T → Consequence T = .bot →
    Proof Γ (.unary T ϕ)
  | LEM (ϕ : Formula) : Proof Γ (.leaf (ϕ.or ϕ.not))

def IsProof (Γ : Theory) (ϕ : Formula) : Prop := ∃ T : Tree, Consequence T = ϕ ∧ Proof Γ T

theorem Provable_then_IsProof : Γ ⊢ ϕ → IsProof Γ ϕ := by
  intro h
  induction h with
  | Axiom A =>
    use .leaf A
    constructor
    · rfl
    · apply Proof.Axiom ; assumption
  | Imp_Intro h ih =>
    rename_i Δ A B
    obtain ⟨T, hTC, hTP⟩ := ih
    use T.unary (A.imp B)
    constructor
    · rfl
    · apply Proof.Imp_Intro <;> assumption
  | Imp_Elim h₁ h₂ ih₁ ih₂ =>
    rename_i Δ A B
    obtain ⟨T₁, hT₁C, hT₁P⟩ := ih₁
    obtain ⟨T₂, hT₂C, hT₂P⟩ := ih₂
    use T₁.binary T₂ B
    constructor
    · rfl
    · apply Proof.Imp_Elim <;> assumption
  | And_Intro h₁ h₂ ih₁ ih₂ =>
    rename_i Δ A  B
    obtain ⟨T₁, hT₁C, hT₁P⟩ := ih₁
    obtain ⟨T₂, hT₂C, hT₂P⟩ := ih₂
    use T₁.binary T₂ (A.and B)
    constructor
    · rfl
    · apply Proof.And_Intro <;> assumption
  | And_Elim_Left h ih =>
    rename_i Δ A B
    obtain ⟨T, hTC, hTP⟩ := ih
    use T.unary A
    constructor
    · rfl
    · apply Proof.And_Elim_Left <;> assumption
  | And_Elim_Right h ih =>
    rename_i Δ A B
    obtain ⟨T, hTC, hTP⟩ := ih
    use T.unary B
    constructor
    · rfl
    · apply Proof.And_Elim_Right <;> assumption
  | Or_Intro_Left h ih =>
    rename_i Δ A B
    obtain ⟨T, hTC, hTP⟩ := ih
    use T.unary (A.or B)
    constructor
    · rfl
    · apply Proof.Or_Intro_Left <;> assumption
  | Or_Intro_Right h ih =>
    rename_i Δ B A
    obtain ⟨T, hTC, hTP⟩ := ih
    use T.unary (A.or B)
    constructor
    · rfl
    · apply Proof.Or_Intro_Right <;> assumption
  | Or_Elim h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    rename_i Δ A B C
    obtain ⟨T₁, hT₁C, hT₁P⟩ := ih₁
    obtain ⟨T₂, hT₂C, hT₂P⟩ := ih₂
    obtain ⟨T₃, hT₃C, hT₃P⟩ := ih₃
    use T₁.trinary T₂ T₃ C
    constructor
    · rfl
    · apply Proof.Or_Elim <;> assumption
  | Not_Intro h ih =>
    rename_i Δ A
    obtain ⟨T, hTC, hTP⟩ := ih
    use T.unary A.not
    constructor
    · rfl
    · apply Proof.Not_Intro <;> assumption
  | Not_Elim h₁ h₂ ih₁ ih₂ =>
    rename_i Δ A
    obtain ⟨T₁, hT₁C, hT₁P⟩ := ih₁
    obtain ⟨T₂, hT₂C, hT₂P⟩ := ih₂
    use T₁.binary T₂ .bot
    constructor
    · rfl
    · apply Proof.Not_Elim <;> assumption
  | EXP h ih =>
    rename_i Δ A
    obtain ⟨T, hTC, hTP⟩ := ih
    use T.unary A
    constructor
    · rfl
    · apply Proof.EXP <;> assumption
  | LEM A =>
    use .leaf (A.or A.not)
    constructor
    · rfl
    · apply Proof.LEM

theorem IsProof_then_Provable : IsProof Γ ϕ → Γ ⊢ ϕ := by
  intro ⟨T, hTC, hTP⟩
  rw[←hTC]
  induction hTP generalizing ϕ with
  | Axiom _ =>
    apply Provable.Axiom ; assumption
  | Imp_Intro h heq ih =>
    apply Provable.Imp_Intro ; rw[heq] at ih ; have := ih rfl ; assumption
  | Imp_Elim h₁ h₁eq h₂ h₂eq ih₁ ih₂ =>
    apply Provable.Imp_Elim
    · rw[h₁eq] at ih₁ ; have := ih₁ rfl ; assumption
    · rw[h₂eq] at ih₂ ; have := ih₂ rfl ; assumption
  | And_Intro h₁ h₁eq h₂ h₂eq ih₁ ih₂ =>
    apply Provable.And_Intro
    · rw[h₁eq] at ih₁ ; have := ih₁ rfl ; assumption
    · rw[h₂eq] at ih₂ ; have := ih₂ rfl ; assumption
  | And_Elim_Left h heq ih =>
    apply Provable.And_Elim_Left ; rw[heq] at ih ; have := ih rfl ; assumption
  | And_Elim_Right h heq ih =>
    apply Provable.And_Elim_Right ; rw[heq] at ih ; have := ih rfl ; assumption
  | Or_Intro_Left h heq ih =>
    apply Provable.Or_Intro_Left ; rw[heq] at ih ; have := ih rfl ; assumption
  | Or_Intro_Right h heq ih =>
    apply Provable.Or_Intro_Right ; rw[heq] at ih ; have := ih rfl ; assumption
  | Or_Elim h₁ h₁eq h₂ h₂eq h₃ h₃eq ih₁ ih₂ ih₃ =>
    apply Provable.Or_Elim
    · rw[h₁eq] at ih₁ ; have := ih₁ rfl ; assumption
    · rw[h₂eq] at ih₂ ; have := ih₂ rfl ; assumption
    · rw[h₃eq] at ih₃ ; have := ih₃ rfl ; assumption
  | Not_Intro h heq ih =>
    apply Provable.Not_Intro ; rw[heq] at ih ; have := ih rfl ; assumption
  | Not_Elim h₁ h₁eq h₂ h₂eq ih₁ ih₂ =>
    apply Provable.Not_Elim
    · rw[h₁eq] at ih₁ ; have := ih₁ rfl ; assumption
    · rw[h₂eq] at ih₂ ; have := ih₂ rfl ; assumption
    -- <;> assumption
  | EXP h heq ih =>
    apply Provable.EXP ; rw[heq] at ih ; have := ih rfl ; assumption
  | LEM _ =>
    apply Provable.LEM

theorem definition_equivalence : Γ ⊢ ϕ ↔ IsProof Γ ϕ :=
  ⟨Provable_then_IsProof, IsProof_then_Provable⟩
