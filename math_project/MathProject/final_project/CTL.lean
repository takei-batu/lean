import Mathlib
set_option linter.style.longLine false

abbrev AP := String
abbrev State := Nat

inductive Formula where
  -- | bot : Formula -- ⊥
  | top : Formula -- ⊤
  | atom (name : AP) : Formula -- atomic formula
  | not : Formula → Formula -- ¬p
  | and : Formula → Formula → Formula -- p ∧ q
  | or : Formula → Formula → Formula -- p ∨ q
  | imp : Formula → Formula → Formula -- p ⇒ q
  -- | iff : Formula → Formula → Formula -- p ↔ p
  | AX : Formula → Formula -- AX p
  | EX : Formula → Formula -- EX p
  | AG : Formula → Formula -- AG p
  | EG : Formula → Formula -- EG p
  | AF : Formula → Formula -- AF p
  | EF : Formula → Formula -- EF p
  | AU : Formula → Formula → Formula -- A (p U q)
  | EU : Formula → Formula → Formula -- E (p U q)
deriving Repr, DecidableEq

structure TransitionSystem where
  states : Finset State
  trans : Finset (State × State)
  trans_valid :  ∀ w ∈ trans, w.1 ∈ states ∧ w.2 ∈ states := by decide -- 不正な遷移関係を入力するとエラー
  label : State → Finset Formula

abbrev TS := TransitionSystem

-- {s | s → s'}
def next (t : TS) (s : State) : Finset State :=
  t.trans.filter (fun w => w.1 == s) |>.image (fun w => w.2)

lemma next_valid : next t s ⊆ t.states := by
  intro x hx
  unfold next at hx
  simp only [Finset.mem_image, Finset.mem_filter, beq_iff_eq] at hx
  obtain ⟨⟨s, x⟩, ⟨h, rfl⟩, rfl⟩ := hx
  exact (t.trans_valid (s, x) h).right

def gfp (step : Finset State → Finset State) (S : Finset State) : Finset State :=
  -- let fix := S ∩ step S
    if _h : S ∩ step S = S then S else gfp step (S ∩ step S)
  -- 停止性の証明（mathlib の既存の定理を使って証明）
  termination_by S.card
  decreasing_by
  apply Finset.card_lt_card
  rw[Finset.ssubset_iff_subset_ne]
  constructor
  · exact Finset.inter_subset_left
  · exact _h

lemma gfp_subset {step : Finset State → Finset State} {S : Finset State} : gfp step S ⊆ S := by
  induction S using gfp.induct step with
  | case1 S h => rw[gfp, dif_pos h]
  | case2 S h₁ h₂ =>
    rw[gfp, dif_neg h₁]
    have h₃ : S ∩ step S ⊆ S := Finset.inter_subset_left
    exact Finset.Subset.trans h₂ h₃

-- gfp step S is Greatest Fixed Point
theorem gfp_is_fix {step : Finset State → Finset State} (monotonic : ∀ S₁ S₂, S₁ ⊆ S₂ → step S₁ ⊆ step S₂) (S : Finset State) : gfp step S = S ∩ step (gfp step S) := by
  induction S using gfp.induct step with
  | case1 S h =>
    have fix : gfp step S = S := by rw[gfp, dif_pos h]
    simp only[fix]
    exact h.symm
  | case2 S h₁ h₂ =>
    have h₃ : step (gfp step S) ⊆ step S := monotonic (gfp step S) S gfp_subset
    have h₄ : gfp step S = gfp step (S ∩ step S) := by rw [gfp, dif_neg h₁]
    rw[←h₄] at h₂
    rw [← Finset.inter_eq_left, Finset.inter_comm] at h₃
    rw [Finset.inter_assoc, h₃] at h₂
    exact h₂

def lfp (univ : Finset State) (step : Finset State → Finset State) (S : Finset State) : Finset State :=
  if _guard: S ∪ step S ⊆ univ then -- univ が満たすべき条件
    if _h : S ∪ step S = S then S else lfp univ step (S ∪ step S)
  else S
  -- 停止性の証明
  termination_by univ.card - S.card
  decreasing_by
  apply tsub_lt_tsub_left_of_le
  · apply Finset.card_le_card
    exact _guard
  · apply Finset.card_lt_card
    rw[Finset.ssubset_iff_subset_ne]
    constructor
    · exact Finset.subset_union_left
    · exact Ne.symm _h

lemma lfp_subset {univ : Finset State} {step : Finset State → Finset State} {S : Finset State} : S ⊆ lfp univ step S := by
  induction S using lfp.induct univ step with
  | case1 S guard h => rw[lfp, dif_pos guard, dif_pos h]
  | case2 S guard h₁ h₂ =>
    rw[lfp, dif_pos guard, dif_neg h₁]
    have h₃ : S ⊆ S ∪ step S := Finset.subset_union_left
    exact Finset.Subset.trans h₃ h₂
  | case3 _ guard => rw[lfp, dif_neg guard]

-- lfp step S is Least Fixed Point
theorem lfp_is_fix {univ : Finset State} {step : Finset State → Finset State} (step_univ : ∀ X, X ⊆ univ → step X ⊆ univ) (monotonic : ∀ S₁ S₂, S₁ ⊆ S₂ → step S₁ ⊆ step S₂) (S : Finset State) (S_univ : S ⊆ univ) : lfp univ step S = S ∪ step (lfp univ step S) := by
  induction S using lfp.induct univ step with
  | case1 S guard h =>
    have fix : lfp univ step S = S := by rw[lfp, dif_pos guard, dif_pos h]
    simp only[fix]
    exact h.symm
  | case2 S guard h₁ h₂ =>
    have h₃ : step S ⊆ step (lfp univ step S) := monotonic S (lfp univ step S) lfp_subset
    have h₄ : lfp univ step S = lfp univ step (S ∪ step S) := by rw [lfp, dif_pos guard, dif_neg h₁]
    rw[←h₄] at h₂
    rw [← Finset.union_eq_left, Finset.union_comm] at h₃
    rw [Finset.union_assoc, h₃] at h₂
    exact h₂ guard
  | case3 S guard =>
    rw[lfp, dif_neg guard]
    have stepS_univ : step S ⊆ univ := step_univ S S_univ
    have : S ∪ step S ⊆ univ := Finset.union_subset S_univ stepS_univ
    contradiction

lemma lfp_subset_univ {univ : Finset State} {step : Finset State → Finset State} {S : Finset State} : S ⊆ univ → lfp univ step S ⊆ univ := by
  induction S using lfp.induct univ step with
  | case1 S guard h =>
    intro h_S
    have h_lfp : lfp univ step S = S := by rw [lfp, dif_pos guard, dif_pos h]
    rw [h_lfp]
    exact h_S
  | case2 S guard h₁ ih =>
    intro _
    have h_lfp : lfp univ step S = lfp univ step (S ∪ step S) := by rw [lfp, dif_pos guard, dif_neg h₁]
    rw [h_lfp]
    exact ih guard
  | case3 S guard =>
    intro h_S
    have h_lfp : lfp univ step S = S := by rw [lfp, dif_neg guard]
    rw [h_lfp]
    exact h_S

def backward (t : TS) (X S : Finset State) : Finset State := X.filter (fun s => next t s ⊆ S)

lemma backward_is_monotonic : ∀ S₁ S₂, S₁ ⊆ S₂ → backward t (t.states) S₁  ⊆ backward t (t.states) S₂ := by
  intro S₁ S₂ h s
  unfold backward
  simp only[Finset.mem_filter]
  intro hs
  constructor
  · exact hs.left
  · exact Finset.Subset.trans hs.right h

def forward (t : TS) (X S : Finset State) : Finset State := X.filter (fun s => (next t s ∩ S).Nonempty)

lemma forward_is_monotonic : ∀ S₁ S₂, S₁ ⊆ S₂ → forward t (t.states) S₁  ⊆ forward t (t.states) S₂ := by
  intro S₁ S₂ h s
  unfold forward
  simp only[Finset.mem_filter]
  intro hs
  constructor
  · exact hs.left
  · obtain ⟨x, hx⟩ := hs.right
    use x
    rw[Finset.mem_inter] at hx ⊢
    constructor
    · exact hx.left
    · exact h hx.right

-- Labeling algorithm
-- t, s ⊨ ϕ ⇔ s ∈ model t ϕ
def model (t : TS) (f : Formula) : Finset State :=
  match f with
  | .top => t.states -- for all states
  | .atom p => t.states.filter (fun s => (.atom p) ∈ t.label s) -- {s | p ∈ L(s)}
  | .not ϕ => t.states \ (model t ϕ) -- {s | s ⊭ ϕ }
  | .and ϕ ψ => (model t ϕ) ∩ (model t ψ) -- {s | s ⊨ ϕ ∧ s ⊨ ψ}
  | .or ϕ ψ => (model t ϕ) ∪ (model t ψ) -- {s | s ⊨ ϕ ∨ s ⊨ ψ}
  | .imp ϕ ψ => (t.states \ (model t ϕ)) ∪ (model t ψ) -- {s | s ⊨ ϕ ⇒ s ⊨ ψ} = {s | s ⊭ ϕ ∨ s ⊨ ψ}
  | .AX ϕ => backward t (t.states) (model t ϕ) -- {s | ∀ s', s → s' ⇒ s' ⊨ ϕ} = {s | (next t s) ⊆ model t ϕ}
  | .EX ϕ => forward t (t.states) (model t ϕ) -- {s | ∃ s', s → s' ∧ s' ⊨ ϕ} = {s | (next t s) ∩ model t ϕ ≠ ∅}
  | .AG ϕ => gfp (fun S => backward t (t.states) S) (model t ϕ) -- AG ϕ ≡ ϕ ∧ AX (AG ϕ)
  | .EG ϕ => gfp (fun S => forward t (t.states) S) (model t ϕ) -- EG ϕ ≡ ϕ ∧ EX (EG ϕ)
  | .AF ϕ => lfp (t.states) (fun S => backward t (t.states) S) (model t ϕ) -- AF ϕ ≡ ϕ ∨ AX (AF ϕ)
  | .EF ϕ => lfp (t.states) (fun S => forward t (t.states) S) (model t ϕ) -- EF ϕ ≡ ϕ ∨ EX (EF ϕ)
  | .AU ϕ ψ => lfp (t.states) (fun S => backward t (model t ϕ) S) (model t ψ) -- A (ϕ U ψ) ≡ ψ ∧ AX (A (ϕ U ψ))
  | .EU ϕ ψ => lfp (t.states) (fun S => forward t (model t ϕ) S) (model t ψ) -- E (ϕ U ψ) ≡ ψ ∨ EX (E (ϕ U ψ))

lemma backward_dual_forward (t : TS) (X S : Finset State) : X \ backward t X S = forward t X (t.states \ S) := by
  ext s
  rw [Finset.mem_sdiff, backward, forward]
  simp only[Finset.mem_filter]
  apply and_congr_right
  intro hs
  rw [not_and]
  constructor
  · intro h
    have := h hs
    rw [Finset.not_subset] at this
    obtain ⟨x , hx⟩ := this
    use x
    rw[Finset.mem_inter, Finset.mem_sdiff]
    exact ⟨hx.left, next_valid hx.left, hx.right⟩
  · intro h₁ h₂ h₃
    obtain ⟨x, hx⟩ := h₁
    simp only [Finset.mem_inter, Finset.mem_sdiff] at hx
    exact (hx.right.right) (h₃ hx.left)

lemma forward_dual_backward (t : TS) (X S : Finset State) : X \ forward t X S = backward t X (t.states \ S) := by
  -- have :=  backward_dual_forward t X (t.states \ S)
  ext s
  rw [Finset.mem_sdiff, forward, backward]
  simp only [Finset.mem_filter]
  apply and_congr_right
  intro hs
  rw [not_and]
  constructor
  · intro h x hx
    rw [Finset.mem_sdiff]
    constructor
    · exact next_valid hx
    · intro hx_S
      -- 矛盾を導くための Nonempty を構築
      have h_nonempty : (next t s ∩ S).Nonempty := by
        use x
        rw [Finset.mem_inter]
        exact ⟨hx, hx_S⟩
      exact (h hs) h_nonempty
  · intro h _ h_nonempty
    obtain ⟨x, hx⟩ := h_nonempty
    rw [Finset.mem_inter] at hx
    have h_sdiff := h hx.left
    rw [Finset.mem_sdiff] at h_sdiff
    exact h_sdiff.right hx.right

theorem lfp_dual_gfp {univ : Finset State}
  (backward forward : Finset State → Finset State)
  (safe : ∀ X, X ⊆ univ → backward X ⊆ univ)
  (dual : ∀ X, X ⊆ univ → univ \ (X ∪ backward X) = (univ \ X) ∩ forward (univ \ X))
  (S : Finset State) (h_S : S ⊆ univ) :
  univ \ lfp univ backward S = gfp forward (univ \ S) := by
  induction S using lfp.induct univ backward with
  | case1 S guard h =>
    have h_lfp : lfp univ backward S = S := by rw [lfp, dif_pos guard, dif_pos h]
    rw [h_lfp]
    have h_dual := dual S h_S
    rw [h] at h_dual
    have h_gfp : gfp forward (univ \ S) = univ \ S := by rw [gfp, dif_pos h_dual.symm]
    rw [h_gfp]
  | case2 S guard h₁ h₂ =>
    have h_lfp : lfp univ backward S = lfp univ backward (S ∪ backward S) := by rw [lfp, dif_pos guard, dif_neg h₁]
    rw [h_lfp]
    have h_dual := dual S h_S
    have h_gfp_stop : ¬((univ \ S) ∩ forward (univ \ S) = univ \ S) := by
      intro h
      rw [← h_dual] at h
      have eq_S : S ∪ backward S = S := by
        ext x
        constructor
        · intro hx
          by_contra hx_not_S
          have hx_univ : x ∈ univ := guard hx
          have hx_diff : x ∈ univ \ S := by
            rw [Finset.mem_sdiff]
            exact ⟨hx_univ, hx_not_S⟩
          rw [← h, Finset.mem_sdiff] at hx_diff
          exact hx_diff.right hx
        · intro hx
          exact Finset.subset_union_left hx
      exact h₁ eq_S
    have h_gfp : gfp forward (univ \ S) = gfp forward ((univ \ S) ∩ forward (univ \ S)) := by rw [gfp, dif_neg h_gfp_stop]
    rw [h_gfp, ← h_dual]
    exact h₂ guard
  | case3 S guard =>
    have h_back_univ := safe S h_S
    have h_union_univ : S ∪ backward S ⊆ univ := Finset.union_subset h_S h_back_univ
    contradiction

lemma model_subset_states (t : TS) (ϕ : Formula) : model t ϕ ⊆ t.states := by
  induction ϕ with
  | top => rfl
  | atom p => unfold model; intro s h; rw[Finset.mem_filter] at h; exact h.left
  | not ψ => exact Finset.sdiff_subset
  | and ψ₁ ψ₂ h _ => exact Finset.inter_subset_left.trans h
  | or ψ₁ ψ₂ h₁ h₂ => exact Finset.union_subset h₁ h₂
  | imp ψ₁ ψ₂ h₁ h₂=> exact Finset.union_subset Finset.sdiff_subset h₂
  | EX ψ _ => exact Finset.filter_subset _ _
  | AX ψ _ => exact Finset.filter_subset _ _
  | EG ψ h => exact Finset.Subset.trans gfp_subset h
  | AG ψ h => exact Finset.Subset.trans gfp_subset h
  | EF ψ h => exact lfp_subset_univ h
  | AF ψ h => exact lfp_subset_univ h
  | EU ϕ ψ _ h => exact lfp_subset_univ h
  | AU ϕ ψ _ h => exact lfp_subset_univ h

-- t, s ⊨ ¬ AX ϕ ⇔ t, s ⊨ ¬ (EX ¬ ϕ)
example (ϕ : Formula) : model t ϕ.AX.not = model t ((ϕ.not).EX) := by
  unfold model
  exact backward_dual_forward t t.states (model t ϕ)

-- t, s ⊨ ¬ AF ϕ ⇔ t, s ⊨ EG ¬ ϕ
example (ϕ : Formula) : model t ϕ.AF.not = model t ((ϕ.not).EG) := by
  unfold model
  apply lfp_dual_gfp (fun S => backward t t.states S) (fun S => forward t t.states S)
  · intro X hX
    exact Finset.filter_subset _ _
  · intro X hX
    rw [Finset.sdiff_union_distrib]
    rw [backward_dual_forward t t.states X]
  · exact model_subset_states t ϕ

-- t, s ⊨ ¬ EF ϕ ⇔ t, s ⊨ AG ¬ ϕ
example (ϕ : Formula) : model t ϕ.EF.not = model t ((ϕ.not).AG) := by
  unfold model
  apply lfp_dual_gfp (fun S => forward t t.states S) (fun S => backward t t.states S)
  · intro X _
    exact Finset.filter_subset _ _
  · intro X _
    rw [Finset.sdiff_union_distrib]
    rw [forward_dual_backward t t.states X]
  · exact model_subset_states t ϕ

-- t, s ⊨ EF ϕ ⇔ t, s ⊨ E[true U ϕ]
example (ϕ : Formula) : model t ϕ.EF = model t (.EU .top ϕ) := by
  unfold model
  have step_eq : (fun S => forward t t.states S) = (fun S => forward t (model t Formula.top) S) := by rfl
  rw [step_eq]

-- t, s ⊨ AF ϕ ⇔ t, s ⊨ A[true U ϕ]
example (ϕ : Formula) : model t ϕ.AF = model t (.AU .top ϕ) := by
  unfold model
  have step_eq : (fun S => backward t t.states S) = (fun S => backward t (model t Formula.top) S) := by rfl
  rw [step_eq]

-- Mutual Exclusion
def ME : TS := {
  states := {0, 1, 2, 3, 4, 5 ,6 , 7, 8},
  trans := {(0,1),(1,2),(2,3),(1,4),(4,3), (4,0), (3,5), (0,5),(5,6),(6,7), (5,8), (8,7), (8,0), (7,1)},
  label := fun s : State => match s with
  | 0 => {.atom "n₁", .atom "n₂"}
  | 1 => {.atom "t₁", .atom "n₂"}
  | 2 => {.atom "t₁", .atom "t₂"}
  | 3 => {.atom "c₁", .atom "t₂"}
  | 4 => {.atom "c₁", .atom "n₂"}
  | 5 => {.atom "n₁", .atom "t₂"}
  | 6 => {.atom "t₁", .atom "t₂"}
  | 7 => {.atom "t₁", .atom "c₂"}
  | 8 => {.atom "n₁", .atom "c₂"}
  | _ => ∅
}

-- 実行テスト
section test

def ϕ₁ : Formula := .EU (.not (.atom "c₂")) (.atom "c₁")
def ϕ₂ : Formula := .AG (.imp (.atom "t₁") (.AF (.atom "c₁)")))
def ϕ₃ : Formula := .EF (.and (.atom "c₁") (.atom "c₂"))
def ϕ₄ : Formula := .AG (.EF (.and (.atom "n₁") (.atom "n₂")))
def ϕ₅ : Formula := .EF (.atom "c₁")

#eval model ME ϕ₁
#eval model ME ϕ₂
#eval model ME ϕ₃
#eval model ME ϕ₄
#eval model ME ϕ₅

end test
