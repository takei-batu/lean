import Mathlib.Order.Defs.PartialOrder
import MathProject.ProofTheory.Adjoint.mode

/-!
# Adjoint Logic Formulas
-/

/- Formula for ADJ -/
variable {M : Type} [Preorder M] in
inductive Formula : M → Type where
  | Atom : String → Formula m
  | Imp : Formula m → Formula m → Formula m
  | Tensor : Formula m → Formula m → Formula m
  | One : Formula m
  | Plus : Formula m → Formula m → Formula m
  | Zero : Formula m
  | With  : Formula m → Formula m → Formula m
  | Top : Formula m
  | Up {k : M} : k ≤ m → Formula k → Formula m
  | Down {l : M} : m ≤ l → Formula l → Formula m

/- tuple Formula and Mode -/
abbrev MFormula (M : Type) [Preorder M] := Σ m : M, Formula m

open List
open Formula
namespace Formula

variable {M : Type} [Preorder M]

def getMode {m : M} : Formula m → M
  | Up (k := k) _ _ => k
  | Down (l := l) _ _ => l
  | _ => m

/- Decidable Formula m -/
def decEq {m : M} [DecidableEq M] : (φ ψ : Formula m) → Decidable (φ = ψ) := by
  intro φ ψ
  cases φ <;> cases ψ
  -- Atom
  case Atom.Atom p q =>
    if h : p = q then
      exact isTrue (by rw [h])
    else
      exact isFalse (fun eq => by cases eq; exact h rfl)
  -- One, Zero, Top
  case One.One => exact isTrue rfl
  case Zero.Zero => exact isTrue rfl
  case Top.Top => exact isTrue rfl
  -- binary
  case Imp.Imp A B C D =>
    match decEq A C, decEq B D with
    | isTrue h1, isTrue h2 => exact isTrue (by rw [h1, h2])
    | isFalse h1, _ => exact isFalse (fun eq => by cases eq; exact h1 rfl)
    | _, isFalse h2 => exact isFalse (fun eq => by cases eq; exact h2 rfl)
  case Tensor.Tensor A B C D =>
    match decEq A C, decEq B D with
    | isTrue h1, isTrue h2 => exact isTrue (by rw [h1, h2])
    | isFalse h1, _ => exact isFalse (fun eq => by cases eq; exact h1 rfl)
    | _, isFalse h2 => exact isFalse (fun eq => by cases eq; exact h2 rfl)
  case Plus.Plus A B C D =>
    match decEq A C, decEq B D with
    | isTrue h1, isTrue h2 => exact isTrue (by rw [h1, h2])
    | isFalse h1, _ => exact isFalse (fun eq => by cases eq; exact h1 rfl)
    | _, isFalse h2 => exact isFalse (fun eq => by cases eq; exact h2 rfl)
  case With.With A B C D =>
    match decEq A C, decEq B D with
    | isTrue h1, isTrue h2 => exact isTrue (by rw [h1, h2])
    | isFalse h1, _ => exact isFalse (fun eq => by cases eq; exact h1 rfl)
    | _, isFalse h2 => exact isFalse (fun eq => by cases eq; exact h2 rfl)
  --Up, Down
  case Up.Up k₁ A a k₂ B b =>
    if h : k₁ = k₂ then
      subst h
      have : a = b := by rfl
      match decEq A B with
      | isTrue eq => exact isTrue (by rw [this, eq])
      | isFalse eq => exact isFalse (fun eq => by cases eq; exact eq rfl)
    else
      exact isFalse (by
        intro eq
        have hk : k₁ = k₂ := by
          have h_eq := congrArg Formula.getMode eq
          exact h_eq
        exact h hk
      )
  case Down.Down l₁ A a l₂ B b =>
    if h : l₁ = l₂ then
      subst h
      have : a = b := by rfl
      match decEq A B with
      | isTrue eq => exact isTrue (by rw [this, eq])
      | isFalse eq => exact isFalse (fun eq => by cases eq; exact eq rfl)
    else
      exact isFalse (by
        intro eq
        have hl : l₁ = l₂ := by
          have h_eq := congrArg Formula.getMode eq
          exact h_eq
        exact h hl
      )
  all_goals
    exact isFalse (fun h => by cases h)
instance {m : M} [DecidableEq M] : DecidableEq (Formula m) := decEq

/- size of Formula (i.e. the number of connectives) -/
@[simp]
def size {m : M} : Formula m → Nat
  | Atom _ => 0
  | One => 0
  | Zero => 0
  | Top => 0
  | Imp _ _ => 1
  | Tensor _ _ => 1
  | Plus _ _ => 1
  | With _ _ => 1
  | Up _ _ => 1
  | Down _ _ => 1

/- general Plus -/
def Plus_n {m : M} (ℱ : List (Formula m)) : Formula m :=
  match ℱ with
  | [] => .Zero
  | A :: [] => A
  | A :: rest => .Plus A (Plus_n rest)

/- general With -/
def With_n {m : M} (ℱ : List (Formula m)) : Formula m :=
  match ℱ with
  | [] => .Top
  | A :: [] => A
  | A :: rest => .With A (With_n rest)

/- ToString Formula m -/
def toString {m : M} [ToString M] : Formula m → String
  | .Atom p => s!"{p}({m})"
  | .Imp A B => s!"({toString A} ⊸({m}) {toString B})"
  | .Tensor A B => s!"({toString A} ⊗({m}) {toString B})"
  | .One => s!"1({m})"
  | .Plus A B => s!"({toString A} ⊕({m}) {toString B})"
  | .Zero => s!"0({m})"
  | .With A B => s!"({toString A} & {toString B})"
  | .Top => s!"⊤({m})"
  | .Up (k := k) _ A => s!"(↑({k},{m}){toString A})"
  | .Down (l := l) _ A => s!"(↓({l},{m}){toString A})"
instance {m : M} [ToString M] : ToString (Formula m) where
  toString := Formula.toString

/- encapsulation of mode -/
def hideMode {m : M} (A : Formula m) : Σ m : M, Formula m := ⟨m, A⟩

theorem mode_eq {m : M} (A : Formula m) : (hideMode A).1 = getMode A := by
  rw[hideMode]
  sorry

/- declaration of independence -/
abbrev DoI (Γ : List (MFormula M)) (k : M) : Prop := ∀ 𝒜 ∈ Γ, 𝒜.1 ≥ k

/- using Γ ≥ k ↔ ∀ 𝒜 ∈ Γ, 𝒜.1 ≥ k -/
infix:50 " ≥ₘ " => DoI

theorem DoI_cons {k 𝒜} {Γ : List (MFormula M)} : 𝒜 :: Γ ≥ₘ k → Γ ≥ₘ k := by
  intro h x hx
  exact h x (mem_cons_of_mem 𝒜 hx)

theorem DoI_erase [DecidableEq M] {k 𝒜} {Γ : List (MFormula M)} : Γ ≥ₘ k → Γ.erase 𝒜 ≥ₘ k := by
  intro h x hx
  exact h x (mem_of_mem_erase hx)

theorem Imp_eq {m : M} {A B : Formula m} {C D : Formula m} :
  A.Imp B = C.Imp D ↔ A = C ∧ B = D := by
  constructor
  · intro h
    injection h with _ hA hB
    exact ⟨hA, hB⟩
  · intro ⟨hA, hB⟩
    rw[hA, hB]

theorem Tensor_eq {m : M} {A B : Formula m} {C D : Formula m} :
  A.Tensor B = C.Tensor D ↔ A = C ∧ B = D := by
  constructor
  · intro h
    injection h with _ hA hB
    exact ⟨hA, hB⟩
  · intro ⟨hA, hB⟩
    rw[hA, hB]

theorem Plus_eq {m : M} {A B : Formula m} {C D : Formula m} :
  A.Plus B = C.Plus D ↔ A = C ∧ B = D := by
  constructor
  · intro h
    injection h with _ hA hB
    exact ⟨hA, hB⟩
  · intro ⟨hA, hB⟩
    rw[hA, hB]

theorem With_eq {m : M} {A B : Formula m} {C D : Formula m} :
  A.With B = C.With D ↔ A = C ∧ B = D := by
  constructor
  · intro h
    injection h with _ hA hB
    exact ⟨hA, hB⟩
  · intro ⟨hA, hB⟩
    rw[hA, hB]

end Formula

/- test -/
section Test

open LNLMode

private def φ : Formula U := .Up L_le_U (.Atom "p")
private def ψ : Formula L := .Down L_le_U φ
private def ψ' : Formula L := .Down L_le_U (.Up L_le_U (.Atom "p"))

#eval φ
#eval ψ
#eval ψ'
#eval ψ = ψ'
#eval ψ == ψ'

private def A : Formula U := .Plus_n [(.Atom "p"), (.Atom "q"), (.Atom "r")]
#eval A

private def B : Formula U := .With_n [(.Atom "p"), (.Atom "q"), (.Atom "r")]
#eval B

end Test
