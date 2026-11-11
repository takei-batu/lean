import MathProject.ProofTheory.Adjoint.ADJE
import MathProject.ProofTheory.Adjoint.Split

/-! Admissible for Multicut and Cut Elimination-/

open List Formula ADJE Derivation

variable {M : Type} [Preorder M]

set_option maxHeartbeats 1000000 in
-- Relaxed maxHeartbeats to verify massive pattern matching and termination proofs.
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
    Imp_R 𝒟₁, Imp_L (m := m) (Γ₁ := Φ₁) (Γ₂ := Φ₂) (ext := .head) (perm := perm') (A := α) (B := β) side' ℰ₁ ℰ₂ =>
    simp only [cons_n] at ctx
    injection ctx with head tail
    injection head with m_eq eq
    subst m_eq
    have ⟨hA, hB⟩ := Imp_eq.mp (eq_of_heq eq)
    rw[←tail] at perm'
    subst_vars
    have 𝒟 := Imp_R 𝒟₁
    have ⟨i, j, eq', Φ₁', Φ₂', perm'', perm₁, perm₂⟩ := perm_cons_n_split ⟨m, Imp α β⟩ n perm'
    rw[←DoI_of_permList (perm := perm₁)] at side'
    have ℰ₁' := Exchange (perm := perm₁.symm) ℰ₁
    have : PermList (⟨m, β⟩ :: cons_n j ⟨m, α.Imp β⟩ Φ₂') (⟨m, β⟩ :: Φ₂) := inferInstance
    have ℰ₂' := Exchange (perm := this.symm) ℰ₂
    match i, j with
    | 0, 0 =>
      -- set-up
      simp only [cons_n] at side' perm₁ ℰ₁' perm₂ ℰ₂'
      have perm₃ : PermList (Φ₁' ++ (Γ₁ ++ Φ₂')) (Γ₁ ++ (Φ₁' ++ Φ₂')) := inferInstance
      have perm₄ : PermList (Γ₁ ++ (Φ₁' ++ Φ₂')) (Γ₁ ++ Γ₂) := inferInstance
      -- cut
      have cut₁ : Derivation (Φ₁' ++ Γ₁) β := Multicut 1 side' le_rfl mu_one ℰ₁' 𝒟₁
      have cut₂ : Derivation (Φ₁' ++ (Γ₁ ++ Φ₂')) C := Multicut 1 (DoI.append.mpr ⟨side', side₁⟩) side₂ mu_one cut₁ ℰ₂'
      -- goal
      have := Exchange (perm := perm₃) cut₂
      exact Exchange (perm := perm₄.trans perm) this
    | i+1, 0 =>
      -- set-up
      simp only [Nat.add_zero] at eq'
      simp only [cons_n] at perm₂ ℰ₂'
      have hi := eq' ▸ mu_more_than_two (by omega) m h
      have hΓ₁ := contraction_of_mu (by omega) h side₁
      have perm₃ : PermList (Γ₁ ++ Φ₁' ++ (Γ₁ ++ Φ₂')) (Γ₁ ++ Γ₁ ++ (Φ₁' ++ Φ₂')) := inferInstance
      have perm₄ : PermList (Γ₁ ++ (Φ₁' ++ Φ₂')) (Γ₁ ++ Γ₂) := inferInstance
      -- cut
      have cut₁ : Derivation (Γ₁ ++ Φ₁') α := Multicut (i + 1) side₁ le_rfl hi 𝒟 ℰ₁'
      have cut₂ : Derivation (⟨m,α⟩ :: Γ₁ ++ Φ₂') C := Multicut 1 (by grind) side₂ mu_one 𝒟₁ ℰ₂'
      have cut₃ : Derivation (Γ₁ ++ Φ₁' ++ (Γ₁ ++ Φ₂')) C := Multicut 1 (DoI.append.mpr ⟨side₁, DoI.cons_n side'⟩) side₂ mu_one cut₁ cut₂
      -- contraction
      have := Exchange (perm := perm₃) cut₃
      have cut₄ := Contraction' hΓ₁ this
      exact Exchange (perm := perm₄.trans perm) cut₄
    | 0, j+1 => --sorry
      -- set-up
      simp only [Nat.zero_add] at eq'
      simp only [cons_n] at perm₁ ℰ₁'
      have hj := eq' ▸ mu_more_than_two (by omega) m h
      have hΓ₁ := contraction_of_mu (by omega) h side₁
      have perm₂' : PermList (cons_n (j + 1) ⟨m, α.Imp β⟩ (⟨m, β⟩ :: Φ₂')) (⟨m, β⟩ :: (cons_n (j + 1) ⟨m, α.Imp β⟩ Φ₂')) := inferInstance
      have ℰ₂'' := Exchange (perm := perm₂'.symm) ℰ₂'
      have perm₃ : PermList (Φ₁' ++ Γ₁ ++ (Γ₁ ++ Φ₂')) (Γ₁ ++ Γ₁ ++ (Φ₁' ++ Φ₂')) := inferInstance
      have perm₄: PermList (Γ₁ ++ (Φ₁' ++ Φ₂')) (Γ₁ ++ Γ₂) := inferInstance
      -- cut
      have cut₁ : Derivation (Γ₁ ++ (⟨m, β⟩ :: Φ₂')) C := Multicut (j + 1) side₁ side₂ hj 𝒟 ℰ₂''
      have cut₂ : Derivation (Φ₁' ++ Γ₁) β := Multicut 1 side' le_rfl mu_one ℰ₁' 𝒟₁
      have : PermList (Γ₁ ++ ⟨m, β⟩ :: Φ₂') (⟨m, β⟩ :: Γ₁ ++ Φ₂') := inferInstance
      have cut₁' := Exchange (perm := this) cut₁
      have cut₃ : Derivation (Φ₁' ++ Γ₁ ++ (Γ₁ ++ Φ₂')) C :=
        Multicut 1 (DoI.append.mpr ⟨side', side₁⟩) side₂ mu_one cut₂ cut₁'
      -- contraction
      have := Exchange (perm := perm₃) cut₃
      have cut₄ := Contraction' hΓ₁ this
      exact Exchange (perm := perm₄.trans perm) cut₄
    | i+1, j+1 => sorry
  -- Commutative Imp ケース
  | A, n, 𝒟, Imp_L (ext := .there ext) (perm := perm') (A := α) (B := β) side' ℰ₁ ℰ₂ =>
    sorry
  | _, _, _, _ => sorry
termination_by (φ.size, 𝒟.size, ℰ.size)
decreasing_by
  all_goals
    subst_vars
    simp only [Prod.lex_def]
    -- dsimp only [Formula.size, Derivation.size]
    -- omega
    sorry
