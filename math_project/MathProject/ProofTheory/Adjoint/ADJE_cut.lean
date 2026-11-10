import MathProject.ProofTheory.Adjoint.ADJE
import MathProject.ProofTheory.Adjoint.Split

/-! Admissible for Multicut and Cut Elimination-/

open List Formula ADJE Derivation

variable {M : Type} [Preorder M]

def Multicut [perm : PermList (Γ₁ ++ Γ₂) Γ] [HasSigma M]
  {m k : M} {φ : Formula m} {C : Formula k}
  (n : Nat) (side₁ : Γ₁ ≥ₘ m) (side₂ : m ≥ k) (h : n ∈ μ m)
  (𝒟 : Derivation Γ₁ φ) (ℰ : Derivation (cons_n n ⟨m, φ⟩ Γ₂) C) : Derivation Γ C := by
  generalize ctx : (cons_n n ⟨m, φ⟩ Γ₂) = Δ at ℰ
  match h₁ : φ, h_n : n, h₂ : 𝒟, h₃ : ℰ with
  -- Identity ケース
  | A, 0, .Id, _ =>
    simp only [cons_n] at ctx
    subst_vars
    rw [iff_zero] at h
    have ℰ' : Derivation (⟨m, A⟩ :: Δ) C := Weakening (A := A) h ℰ
    exact Exchange ℰ'
  | A, 1, .Id, _ =>
    simp only [cons_n] at ctx
    subst_vars
    exact Exchange ℰ
  | A, n + 2, .Id, _ =>
    subst_vars
    rw [iff_two (by omega)] at h
    have ℰ' := Contraction_n (n + 1) h ℰ
    exact Exchange ℰ'
  | A, 0, _, .Id =>
    simp only [cons_n] at ctx
    subst_vars
    rw [iff_zero] at h
    have h' : ∀ x ∈ Γ₁, 𝒲 ∈ σ x.1 := by
      intro x hx
      have := side₁ x hx
      have : σ m ⊆ σ x.1 := σ.monotone this
      grind?
    have ℰ' : Derivation (⟨k, C⟩ :: Γ₁) C := Identity side₁ h'
    exact Exchange ℰ'
  | A, 1, _, .Id =>
    subst_vars
    simp only [cons_n] at ctx
    injection ctx with head _
    injection head
    subst_vars
    simp only [append_nil] at perm
    exact Exchange 𝒟
  | A, n + 2, _, .Id =>
    subst_vars
    simp only [cons_n] at ctx
    injection ctx with _ tail
    contradiction
  -- Weakening Imp ケース
  | Imp A B, 0, Imp_R 𝒟₁, Imp_L (ext := .head) side' ℰ₁ ℰ₂ =>
    sorry
  -- Principal Imp ケース
  | Imp A B, n + 1,
    Imp_R 𝒟₁, Imp_L (m := m) (Γ₁ := Φ₁) (Γ₂ := Φ₂) (ext := .head) (A := α) (B := β) side' ℰ₁ ℰ₂ =>
    -- simp only [cons_n] at ctx
    -- injection ctx with head tail
    -- injection head with m_eq eq
    -- subst m_eq
    -- have ⟨hA, hB⟩ := Imp_eq.mp (eq_of_heq eq)
    -- subst_vars
    -- have 𝒟 := Imp_R 𝒟₁
    -- rename_i inst
    -- have ⟨i, j, eq₁, Φ₁', Φ₂', perm, eq₂, extl⟩ := extractList_cons_n_split ⟨m, Imp α β⟩ n inst
    -- match i, j with
    -- | 0, 0 => sorry
    -- | i+1, 0 =>
    --   simp only [cons_n] at eq₂
    --   subst eq₂
    --   rw[←DoI_of_permList (k := m) (perm := perm)] at side'
    --   have side'' := DoI_cons_n side'
    --   simp only [Nat.add_zero] at eq₁
    --   subst eq₁
      -- have hi := mu_n (by omega) m h
      -- have perm' := perm.symm
      -- have ℰ₁' : Derivation (cons_n (i + 1) ⟨m, Imp α β⟩ Φ₁') α := Exchange ℰ₁
      -- let ⟨Ψ, h_psi⟩ := extractList_append Γ₁ Φ₁'
      -- have cut : Derivation Ψ α := Multicut (i + 1) side₁ le_rfl hi 𝒟 ℰ₁'
      -- have := Imp_L _ cut ℰ₂
      sorry
    -- | 0, j+1 => sorry
    -- | i+1, j+1 => sorry
  -- Commutative Imp ケース
  | A, n, 𝒟, Imp_L (ext := .there ext_tail) side' ℰ₁ ℰ₂ => sorry
  | _, _, _, _ => sorry
