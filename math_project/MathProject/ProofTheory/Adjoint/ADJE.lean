import MathProject.ProofTheory.Adjoint.mode
import MathProject.ProofTheory.Adjoint.Extract
import MathProject.ProofTheory.Adjoint.Perm
import MathProject.ProofTheory.Adjoint.formula

/-!
# ADJE
-/
namespace ADJE

variable {M : Type} [Preorder M]

open List Formula Extract ExtractList PermList

/-- Sequent for ADJE -/
inductive Derivation [HasSigma M] : List (MFormula M) → {m : M} → Formula m -> Type where
| Id {A : Formula m}:
  Derivation {⟨m, A⟩} A
/- Structural -/
| Weakening {A : Formula m} {C : Formula k} :
  (h : 𝒲 ∈ σ m) → Derivation Γ C →
  Derivation (⟨m, A⟩ :: Γ) C
| Contraction {A : Formula m} {C : Formula k} :
  (h : 𝒞 ∈ σ m) →
  Derivation (⟨m, A⟩ :: ⟨m, A⟩ :: Γ) C →
  Derivation (⟨m, A⟩ :: Γ) C
/- Plus and Zero -/
| Plus_L {A B : Formula m} {C : Formula k} [ext : Extract ⟨m, Plus A B⟩ Γ Γ'] :
  Derivation (⟨m, A⟩ :: Γ') C →
  Derivation (⟨m, B⟩ :: Γ') C →
  Derivation Γ C
| Plus_R_1 {A B : Formula m} :
  Derivation Γ A →
  Derivation Γ (Plus A B)
| Plus_R_2 {A B : Formula m} :
  Derivation Γ B →
  Derivation Γ (Plus A B)
| Zero_L {m : M} {C : Formula k} [ext : Extract ⟨m, Zero⟩ Γ Γ'] :
  Derivation Γ C
-- no Zero_R
/- With and Top -/
| With_L_1 {A B : Formula m} {C : Formula k} [ext : Extract ⟨m, With A B⟩ Γ Γ'] :
  Derivation (⟨m, A⟩ :: Γ') C →
  Derivation Γ C
| With_L_2 {A B : Formula m} {C : Formula k} [ext : Extract ⟨m, With A B⟩ Γ Γ'] :
  Derivation (⟨m, B⟩ :: Γ') C →
  Derivation Γ C
| With_R {A B : Formula m} :
  Derivation Γ A →
  Derivation Γ B →
  Derivation Γ (With A B)
-- no Top_L
| Top_R :
  Derivation Γ Top
/- Tensor and One -/
| Tensor_L {A B : Formula m} {C : Formula k} [ext : Extract ⟨m, Tensor A B⟩ Γ Γ'] :
  Derivation (⟨m, A⟩ :: ⟨m, B⟩ :: Γ') C →
  Derivation Γ C
| Tensor_R {A B : Formula m} [perm : PermList (Γ₁ ++ Γ₂) Γ] :
  Derivation Γ₁ A →
  Derivation Γ₂ B →
  Derivation Γ (Tensor A B)
| One_L {m : M} {C : Formula k} [ext : Extract ⟨m, One⟩ Γ Γ'] :
  Derivation Γ' C →
  Derivation Γ C
| One_R :
  Derivation {} One
/- Imp -/
| Imp_L {A B : Formula m} {C : Formula k}
  [ext : Extract ⟨m, Imp A B⟩ Γ Γ'] [perm : PermList (Γ₁ ++ Γ₂) Γ'] :
  (side : Γ₁ ≥ₘ m) →
  Derivation Γ₁ A →
  Derivation (⟨m, B⟩ :: Γ₂) C →
  Derivation Γ C
| Imp_R {A B : Formula m} :
  Derivation (⟨m, A⟩ :: Γ) B →
  Derivation Γ (Imp A B)
/- Shift -/
| Down_L {h : m ≤ l} {A : Formula l} {C : Formula k} [ext : Extract ⟨m, Down h A⟩ Γ Γ'] :
  Derivation (⟨l, A⟩ :: Γ') C →
  Derivation Γ C
| Down_R {h : m ≤ l} {A : Formula l} :
  (side : Γ ≥ₘ l) →
  Derivation Γ A →
  Derivation Γ (Down h A)
| Up_L {h : k ≤ m} {A : Formula k} {C : Formula l} [ext : Extract ⟨m, Up h A⟩ Γ Γ'] :
  (side : k ≥ l) →
  Derivation (⟨k, A⟩ :: Γ') C →
  Derivation Γ C
| Up_R {h : k ≤ m} {A : Formula k} :
  Derivation Γ A →
  Derivation Γ (Up h A)

open Derivation

/-- cons_n n 𝒜 Γ = 𝒜 :: ... :: 𝒜 :: Γ -/
@[reducible, simp]
def cons_n (n : Nat) (𝒜 : MFormula M) (Γ : List (MFormula M)) : List (MFormula M) :=
  match n with
  | 0 => Γ
  | n + 1 => 𝒜 :: cons_n n 𝒜 Γ

lemma DoI.cons_n {k 𝒜} {Γ : List (MFormula M)} : cons_n n 𝒜 Γ ≥ₘ k → Γ ≥ₘ k := by
  induction n with
  | zero => simp only [imp_self]
  | succ n ih =>
    intro h
    exact ih (DoI.cons h)

-- /- This instance in not necessary, but may make proof easy. -/
-- instance instExtractConsN {n : Nat} {𝒜 : MFormula M} {Γ : List (MFormula M)} :
--   Extract 𝒜 (cons_n (n + 1) 𝒜 Γ) (cons_n n 𝒜 Γ) := Extract.head

instance instPermListConsN {n : Nat} {𝒜 : MFormula M} {Γ Γ' : List (MFormula M)} [PermList Γ Γ'] :
  PermList (cons_n n 𝒜 Γ) (cons_n n 𝒜 Γ') := by
  induction n with
  | zero => simp only [cons_n]; trivial
  | succ n ih => simp only [cons_n]; infer_instance

/-- cons_n n x の中に要素 y を出し入れする置換 -/
instance instPermConsNCons {n : Nat} {𝒜 ℬ : MFormula M} {Γ : List (MFormula M)} :
  PermList (cons_n n 𝒜 (ℬ :: Γ)) (ℬ :: cons_n n 𝒜 Γ) := by
  induction n with
  | zero =>
    simp only [cons_n]
    exact inferInstance
  | succ n ih =>
    simp only [cons_n]
    have h1 : PermList (𝒜 :: cons_n n 𝒜 (ℬ :: Γ)) (𝒜 :: ℬ :: cons_n n 𝒜 Γ) := inferInstance
    have h2 : PermList (𝒜 :: ℬ :: cons_n n 𝒜 Γ) (ℬ :: 𝒜 :: cons_n n 𝒜 Γ) := inferInstance
    exact h1.trans h2

/-- μ(m) := {n : Nat | (n = 0 ∧ 𝒲 ∈ σ(m)) ∨ n = 1 ∨ (n ≥ 2 ∧ 𝒞 ∈ σ(m))} -/
@[simp]
def mu (m : M) [HasSigma M] : Set Nat := {n : Nat | (n = 0 ∧ 𝒲 ∈ σ m) ∨ n = 1 ∨ (n ≥ 2 ∧ 𝒞 ∈ σ m)}

notation "μ" => mu

lemma iff_zero (m : M) [HasSigma M] : 0 ∈ μ m ↔ 𝒲 ∈ σ m := by simp?

lemma iff_one (m : M) [HasSigma M] : 1 ∈ μ m ↔ True := by simp?

lemma mu_one {m : M} [HasSigma M] : 1 ∈ μ m := by simp?

lemma iff_two (h : n ≥ 2) (m : M) [HasSigma M] : n ∈ μ m ↔ 𝒞 ∈ σ m := by
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  simp? [h, h0, h1]

/-- if n ≥ 2 and n ∈ μ m, then n-1 ∈ μ m -/
lemma mu_more_than_two {n : Nat} (h : n + 1 ≥ 2) (m : M) [HasSigma M]
(side : n + 1 ∈ μ m) : n ∈ μ m := by
  match n with
  | 0 => contradiction
  | 1 => rw[iff_one]; trivial
  | n + 2 => rw[iff_two h] at side; rwa [iff_two (by omega)]

/-- n + 1 ∈ μ m (n ≥ 1) と Γ ≥ m から、Γ の全要素が縮約可能であることを導く -/
lemma contraction_of_mu {n : Nat} (h : n + 1 ≥ 2) {m : M} [HasSigma M]
    (side : n + 1 ∈ μ m) {Γ : List (MFormula M)} (h_doi : Γ ≥ₘ m) :
    ∀ x ∈ Γ, 𝒞 ∈ σ x.1 := by
  have hC : 𝒞 ∈ σ m := (iff_two h m).mp side
  intro x hx
  exact (σ.monotone (h_doi x hx)) hC

namespace Derivation

@[simp]
def size [HasSigma M] {m : M} {A : Formula m} {Γ : List (MFormula M)} : Derivation Γ A → Nat
  | .Id => 1
  | .Weakening _ D => size D + 1
  | .Contraction _ D => size D + 1
  | .Plus_L (ext := _) D₁ D₂ => size D₁ + size D₂ + 1
  | .Plus_R_1 D => size D + 1
  | .Plus_R_2 D => size D + 1
  | .Zero_L (ext := _) => 1
  | .With_L_1 (ext := _) D => size D + 1
  | .With_L_2 (ext := _) D => size D + 1
  | .With_R D₁ D₂ => size D₁ + size D₂ + 1
  | .Top_R => 1
  | .Tensor_L (ext := _) D => size D + 1
  | .Tensor_R (perm := _) D₁ D₂ => size D₁ + size D₂ + 1
  | .One_L (ext := _) D => size D + 1
  | .One_R => 1
  | .Imp_L (ext := _) (perm := _) _ D₁ D₂ => size D₁ + size D₂ + 1
  | .Imp_R D => size D + 1
  | .Down_L (ext := _) D => size D + 1
  | .Down_R _ D => size D + 1
  | .Up_L (ext := _) _ D => size D + 1
  | .Up_R D => size D + 1

def Exchange [perm : PermList Γ₁ Γ₂] [HasSigma M] {m : M} {A : Formula m} :
  Derivation Γ₁ A → Derivation Γ₂ A := by
  intro 𝒟
  sorry

/-- Admissible for General Identity -/
def Identity {m k : M} [HasSigma M] {A : Formula k} {Γ : List (MFormula M)}
  (side : Γ ≥ₘ m) (h : ∀ x ∈ Γ, 𝒲 ∈ σ x.1) : Derivation (⟨k, A⟩ :: Γ) A := by
  induction Γ with
  | nil => exact Id
  | cons x xs ih =>
    rcases x with ⟨l, B⟩
    have h' : ∀ x ∈ xs, 𝒲 ∈ σ x.fst := by aesop
    have := ih (DoI.cons side) h'
    have hx := h ⟨l, B⟩ (by simp only [mem_cons, true_or])
    have := Weakening (A := B) hx this
    exact Exchange this

/-- Contraction by n times -/
def Contraction_n [HasSigma M] {m : M} {A : Formula m} {C : Formula k}
    (n : Nat) (h : 𝒞 ∈ σ m)
    (ℰ : Derivation (cons_n (n + 1) ⟨m, A⟩ Γ) C) :
    Derivation (⟨m, A⟩ :: Γ) C :=
  match n with
  | 0 => ℰ
  | n + 1 =>
    have ℰ' : Derivation (cons_n (n + 1) ⟨m, A⟩ Γ) C := Contraction h ℰ
    Contraction_n n h ℰ'

/-- Admissible for General Contraction -/
def Contraction' [HasSigma M] {m : M} {C : Formula m} (h : ∀ x ∈ Γ₁, 𝒞 ∈ σ x.1) :
  Derivation ((Γ₁ ++ Γ₁) ++ Γ₂) C → Derivation (Γ₁ ++ Γ₂) C := by
  -- intro 𝒟
  match Γ₁ with
  | [] =>
    simp only [nil_append]
    exact id
  | x :: xs =>
    intro 𝓓
    have hx : 𝒞 ∈ σ x.fst := by grind
    have hxs : ∀ x ∈ xs, 𝒞 ∈ σ x.fst := by grind
    have ext : Extract x (xs ++ x :: (xs ++ Γ₂)) (xs ++ (xs ++ Γ₂)) := inferInstance
    simp only [←cons_append, ←append_assoc] at ext
    have perm : PermList (x :: xs ++ x :: xs ++ Γ₂) (x :: x :: xs ++ xs ++ Γ₂) := inferInstance
      -- ExtractList.cons (ext := Extract.head) (extractList_of_extract ext)
    have 𝓓₁ : Derivation (x :: x :: xs ++ xs ++ Γ₂) C := Exchange 𝓓
    have 𝓓₂ := Contraction hx 𝓓₁
    have perm : PermList (x :: (xs ++ xs ++ Γ₂)) (xs ++ xs ++ x :: Γ₂) := inferInstance
    have 𝒟₃ : Derivation (xs ++ xs ++ x :: Γ₂) C := Exchange 𝓓₂
    have ih𝓓 := Contraction' hxs 𝒟₃
    have : PermList (xs ++ x :: Γ₂) (x :: xs ++ Γ₂) := inferInstance
    exact Exchange ih𝓓

end Derivation

-- /-- 文脈が PermList で移りあうなら、Derivation 同士を自動キャストする -/
-- instance instCoeDerivationOfPerm [HasSigma M] [PermList Γ₁ Γ₂] {m : M} {A : Formula m} :
--     Coe (Derivation Γ₁ A) (Derivation Γ₂ A) where
--   coe 𝒟 := Exchange 𝒟

end ADJE
