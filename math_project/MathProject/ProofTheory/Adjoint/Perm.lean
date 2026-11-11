import MathProject.ProofTheory.Adjoint.Extract
import MathProject.ProofTheory.Adjoint.formula

/-! -/

open List Extract ExtractList

/-- Permutation -/
abbrev PermList {α : Type} (L₁ L₂ : List α) : Type := ExtractList L₁ L₂ []

namespace PermList

@[instance_reducible, refl]
def refl {α : Type} : (L : List α) → PermList L L := fun _ => extractList_refl

@[instance_reducible]
def trans {α : Type} {L₁ L₂ L₃ : List α} :
  (PermList L₁ L₂) → (PermList L₂ L₃) → PermList L₁ L₃ := fun h₁ h₂ => extractList_trans h₁ h₂

@[instance_reducible, symm]
def symm {α : Type} {L₁ L₂ : List α} :
  (PermList L₁ L₂) → PermList L₂ L₁ := fun h => extractList_symm h

end PermList

instance {α : Type} : Trans (PermList (α := α)) (PermList (α := α)) (PermList (α := α)) where
  trans := PermList.trans

/-- 反射律のインスタンス -/
instance instPermListRefl {α : Type} {L : List α} : PermList L L := PermList.refl _

/-- 先頭2要素の入れ替え (隣接スワップ) を O(1) で即座に解決するインスタンス -/
instance instPermListSwap {α : Type} {x y : α} {xs : List α} :
  PermList (y :: x :: xs) (x :: y :: xs) :=
  .cons (ext := .there .head) (.cons (ext := .head) extractList_refl)

/-- 置換の両辺の後ろに同じ共通リスト L'' を追加する置換 (右アペンド合同性) -/
instance instPermListAppendRight {α : Type} {L L' L'' : List α} [perm : PermList L L'] :
  PermList (L ++ L'') (L' ++ L'') := by
  have : ExtractList L (L' ++ L'') L'' := extractList_append_right_rem perm L''
  have : ExtractList L'' L'' [] := extractList_refl
  exact instExtractListAppend

/-- 置換の両辺の前に同じ共通リスト L を追加する置換 (左アペンド合同性) -/
instance instPermListAppendLeft {α : Type} {L L' L'' : List α} [perm : PermList L L'] :
  PermList (L'' ++ L) (L'' ++ L') := by
  have : ExtractList L (L'' ++ L') L'' := extractList_append_left_rem perm L''
  have : ExtractList L'' L'' [] := extractList_refl
  exact instExtractListAppend

/-- リストの途中にある要素 x を先頭に引っ張り出す置換 -/
instance instPermListAppendCons {α : Type} {x : α} {xs L : List α} :
  PermList (xs ++ x :: L) (x :: xs ++ L) := by
  have ext : Extract x (xs ++ x :: L) (xs ++ L) := instExtractAppendRight (ext := Extract.head)
  exact extractList_of_extract ext

/-- 自動化①: コンテキストに (L₁ ++ [x]) があれば、自動的に (x :: L₁) として解決する -/
instance instPermListConsFromAppendSingleton {α : Type} {x : α} {L₁ Γ : List α}
  [perm : PermList (L₁ ++ [x]) Γ] : PermList (x :: L₁) Γ := by
  have ext : Extract x (L₁ ++ [x]) (L₁ ++ []) := instExtractAppendRight (ext := Extract.head)
  have h : PermList (x :: L₁) (L₁ ++ [x]) := by
    rw [List.append_nil] at ext
    exact ExtractList.cons (ext := ext) extractList_refl
  exact extractList_trans h perm

/-- コンテキストに PermList ([x] ++ Δ) Γ があれば、自動的に PermList (x :: Δ) Γ として解決する -/
instance instPermListConsFromSingletonAppend {α : Type} {x : α} {L L' : List α}
  [perm : PermList ([x] ++ L) L'] : PermList (x :: L) L' := perm

-- /-- 自動化②: コンテキストに (L₁ ++ []) があれば、自動的に L₁ として解決する -/
-- instance instPermListFromAppendNil {α : Type} {L₁ Γ : List α}
--   [perm : PermList (L₁ ++ []) Γ] : PermList L₁ Γ := by
--   have h : PermList L₁ (L₁ ++ []) := by
--     rw [List.append_nil]
--     exact extractList_refl
--   exact extractList_trans h perm

instance instPermListSwapAssoc {α : Type} {A B C : List α} :
  PermList (A ++ (B ++ C)) (B ++ (A ++ C)) := by
  simp only [←append_assoc]
  exact inferInstance

instance instPermListSwapAssoc' {α : Type} {A B C D : List α} :
  PermList (A ++ B ++ (C ++ D)) (A ++ C ++ (B ++ D)) := by
  simp only [append_assoc]
  have : PermList (B ++ (C ++ D)) (C ++ (B ++ D)) := inferInstance
  have : PermList (A ++ (B ++ (C ++ D))) (A ++ (C ++ (B ++ D))) := inferInstance
  exact this

instance instPermListSwapAssoc'' {α : Type} {A B C D : List α} :
  PermList (A ++ B ++ (C ++ D)) (B ++ C ++ (A ++ D)) := by
  -- have : PermList (A ++ ((B ++ C) ++ D)) ((B ++ C) ++ (A ++ D)) := inferInstance
  -- have eq : A ++ B ++ (C ++ D) = A ++ ((B ++ C) ++ D) := by simp only [append_assoc]
  -- exact eq ▸ this
  have perm₁ : PermList (A ++ B ++ (C ++ D)) (B ++ A ++ (C ++ D)) := inferInstance
  have perm₂ : PermList (B ++ A ++ (C ++ D)) (B ++ C ++ (A ++ D)) := inferInstance
  exact perm₁.trans perm₂

example : PermList [1, 2, 3, 4] [1, 2, 3, 4] := inferInstance
example : PermList [1, 2, 3, 4] [2, 1, 3, 4] := inferInstance
example : PermList [1, 2, 3, 4] [3, 4, 1, 2] := inferInstance
example : PermList (1 :: 2 :: [3, 4]) (2 :: 1 :: [3, 4]) := inferInstance
example : PermList [1, 2, 3, 4] (1 :: [2, 3, 4]) := inferInstance
example : PermList [1, 2, 3, 4] ([1, 2] ++ [3, 4]) := inferInstance
example : PermList [1, 2, 3, 4] ([1] ++ [2, 3, 4]) := inferInstance
example : PermList ([1, 2] ++ [3, 4]) [1, 2, 3, 4]  := inferInstance
example : PermList ([3, 4] ++ [1, 2]) [1, 2, 3, 4]  := inferInstance
example : PermList ([1] ++ [2, 3, 4]) [1, 2, 3, 4]  := inferInstance
example : PermList ([1, 2, 3] ++ [4]) ([1] ++ [2, 3, 4]) := inferInstance

/-- 1個抜き出すと、要素は「抜かれた要素」か「残りの要素」のどちらかになる -/
theorem mem_iff_eq_or_mem_of_extract {α : Type} {x y : α} {Γ Γ' : List α}
    (h : Extract y Γ Γ') : x ∈ Γ ↔ x = y ∨ x ∈ Γ' := by
  induction h with
  | head =>
    simp only [List.mem_cons]
  | there _ ih =>
    simp only [List.mem_cons, ih]
    grind?

/-- リストを抜き出すと、元の要素は「抜かれたリスト」か「残りのリスト」の和集合になる -/
theorem mem_iff_mem_or_mem_of_extractList {α : Type} {x : α} {Γ₁ Γ Γ₂ : List α}
    (h : ExtractList Γ₁ Γ Γ₂) : x ∈ Γ ↔ x ∈ Γ₁ ∨ x ∈ Γ₂ := by
  induction h with
  | nil =>
    simp only [List.not_mem_nil, false_or]
  | cons h_tail ih =>
    rename_i ext
    rw [mem_iff_eq_or_mem_of_extract ext, ih, List.mem_cons]
    grind?

/-- PermList は要素の所属関係（∈）を完全に保存する -/
theorem mem_of_permList {α : Type} {x : α} {Γ₁ Γ₂ : List α} [h : PermList Γ₁ Γ₂] :
    x ∈ Γ₁ ↔ x ∈ Γ₂ := by
  have := mem_iff_mem_or_mem_of_extractList (x := x) h
  simp only [List.not_mem_nil, or_false] at this
  exact this.symm

/-- 任意の述語 P に対する全称量化（∀ x ∈ Γ, P x）も PermList で保存される -/
theorem all_of_permList {α : Type} {P : α → Prop} {Γ₁ Γ₂ : List α} [PermList Γ₁ Γ₂] :
    (∀ x ∈ Γ₁, P x) ↔ (∀ x ∈ Γ₂, P x) := by
  constructor
  · intro h x hx
    exact h x (mem_of_permList.mpr hx)
  · intro h x hx
    exact h x (mem_of_permList.mp hx)

lemma DoI_of_permList
 {M : Type} [Preorder M] {k : M} {Γ₁ Γ₂ : List (MFormula M)} [perm : PermList Γ₁ Γ₂] :
  Γ₁ ≥ₘ k ↔ Γ₂ ≥ₘ k := all_of_permList
