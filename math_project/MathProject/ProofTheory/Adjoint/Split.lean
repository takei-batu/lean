import MathProject.ProofTheory.Adjoint.ADJE

/-! -/


/-- x :: Δ から Φ₁ を抜いた残りが Φ₂ なら、x は Φ₁ に入るか、Φ₂ に残るかのどちらか -/
inductive ExtractListConsSplit {α : Type} (x : α) (Δ : List α) (Φ₁ Φ₂ : List α) : Type where
| in_left {Φ₁' : List α} (hx : Extract x Φ₁ Φ₁') (h : ExtractList Φ₁' Δ Φ₂) :
    ExtractListConsSplit x Δ Φ₁ Φ₂
| in_right {Φ₂' : List α} (heq : Φ₂ = x :: Φ₂') (h : ExtractList Φ₁ Δ Φ₂') :
    ExtractListConsSplit x Δ Φ₁ Φ₂

/-- 1ステップの文脈分割補題 -/
def extractList_cons_split {α : Type} {x : α} {Δ : List α} :
  {Φ₁ Φ₂ : List α} → (h : ExtractList Φ₁ (x :: Δ) Φ₂) → ExtractListConsSplit x Δ Φ₁ Φ₂
| [], _, ExtractList.nil =>
  ExtractListConsSplit.in_right rfl ExtractList.nil
| _ :: _, _, ExtractList.cons (ext := Extract.head) h_tail =>
  ExtractListConsSplit.in_left Extract.head h_tail
| _ :: _, _, ExtractList.cons (ext := Extract.there hy_tail) h_tail =>
  match extractList_cons_split h_tail with
  | ExtractListConsSplit.in_left hx_tail h_rest =>
    ExtractListConsSplit.in_left (Extract.there hx_tail) (ExtractList.cons (ext := hy_tail) h_rest)
  | ExtractListConsSplit.in_right heq h_rest =>
    ExtractListConsSplit.in_right heq (ExtractList.cons (ext := hy_tail) h_rest)

open ADJE Derivation

variable {M : Type} [Preorder M]

/-- cons_n n x Γ₂ から Φ₁ を抜いた残りが Φ₂ ならば、
    x は Φ₁ に i 個、Φ₂ に j 個分配され、i + j = n となる -/
structure ExtractListConsNSplit (𝒜 : MFormula M)
(n : Nat) (Γ₂ Φ₁ Φ₂ : List (MFormula M)) : Type where
  i : Nat
  j : Nat
  sum_eq : i + j = n
  Φ₁' : List (MFormula M)
  Φ₂' : List (MFormula M)
  perm₁ : PermList (cons_n i 𝒜 Φ₁') Φ₁
  eq₂ : Φ₂ = cons_n j 𝒜 Φ₂'
  extl : ExtractList Φ₁' Γ₂ Φ₂'

/-- n ステップの文脈分割定理 -/
def extractList_cons_n_split (𝒜 : MFormula M) :
    (n : Nat) → {Γ₂ Φ₁ Φ₂ : List (MFormula M)} →
    (h : ExtractList Φ₁ (cons_n n 𝒜 Γ₂) Φ₂) →
    ExtractListConsNSplit 𝒜 n Γ₂ Φ₁ Φ₂
| 0, _, _, _, h =>
  { i := 0
    j := 0
    sum_eq := rfl
    Φ₁' := _
    Φ₂' := _
    perm₁ := extractList_refl
    eq₂ := rfl
    extl := h }
| n + 1, Γ₂, Φ₁, Φ₂, h =>
  match extractList_cons_split h with
  | ExtractListConsSplit.in_right heq h_tail =>
    let rec_res := extractList_cons_n_split 𝒜 n h_tail
    { i := rec_res.i
      j := rec_res.j + 1
      sum_eq := by have := rec_res.sum_eq; omega
      Φ₁' := rec_res.Φ₁'
      Φ₂' := rec_res.Φ₂'
      perm₁ := rec_res.perm₁
      eq₂ := heq.trans (congrArg (𝒜 :: ·) rec_res.eq₂)
      extl := rec_res.extl }
  | ExtractListConsSplit.in_left hx h_tail =>
    let rec_res := extractList_cons_n_split 𝒜 n h_tail
    { i := rec_res.i + 1
      j := rec_res.j
      sum_eq := by have := rec_res.sum_eq; omega
      Φ₁' := rec_res.Φ₁'
      Φ₂' := rec_res.Φ₂'
      perm₁ := ExtractList.cons (ext := hx) rec_res.perm₁
      eq₂ := rec_res.eq₂
      extl := rec_res.extl }
