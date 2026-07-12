import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset

structure NFA (α : Type) [Fintype α] (β : Type) [Fintype β] where
  mk ::
  initial : β
  final : Finset β
  transition : β → α → Finset β

namespace NFA


theorem finset_subset_inter_empty [DecidableEq α] {A B C : Finset α}
  : A ⊆ B → B ∩ C = ∅ → A ∩ C = ∅ := by
  intro h1 h2
  have := Finset.inter_subset_inter_right (u := C) h1
  rw[h2] at this
  exact Finset.subset_empty.mp this


variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]


-- 与えられた文字列の最終的な状態の集合を返す
def hat (transition : β → α → Finset β) (q : β) : List α → Finset β
  | [] => {q}
  | x :: xs =>
     (transition q x).biUnion (fun q => hat transition q xs)

def accept (nfa : NFA α β) (w : List α) : Prop :=
   (hat nfa.transition nfa.initial w ∩ nfa.final).Nonempty

#check accept

namespace Example

-- Σ = {0,1} and L = { w 0 a} where w ∈ Σ^* and a ∈ Σ
-- Write the definition of NFA for L and prove its correctness.

def transition : Fin 3 → Fin 2 → Finset (Fin 3)
  | 0, 0 => {0,1}
  | 0, 1 => {0}
  | 1, 0 => {2}
  | 1, 1 => {2}
  | 2, 0 => ∅
  | 2, 1 => ∅

def ex1 : NFA (Fin 2) (Fin 3) := {
    initial := 0
    final := {2}
    transition := transition
  }


lemma alphabet (x : Fin 2) : x = 0 ∨ x = 1 := by omega

lemma state (q : Fin 3) : q = 0 ∨ q = 1 ∨ q = 2 := by omega

lemma q0 : 0 ∈ transition 0 a := by
  rcases alphabet a with h0 | h1 <;>
  (first | rw[h0] | rw[h1]) <;>
  simp only [transition] <;>
  decide

lemma q1 : 1 ∈ transition 0 0 := by
  rw[transition]
  decide

lemma not_q1 : 1 ∉ transition q 1 := by
  rcases state q with h0 | h1 | h2 <;>
  (first | rw[h0] | rw[h1] | rw[h2]) <;>
  simp only [transition] <;>
  decide

lemma q2 : 2 ∈ transition 1 a := by
  rcases alphabet a with h0 | h1 <;>
  (first | rw[h0] | rw[h1]) <;>
  rw[transition] <;>
  decide

lemma not_q2 : q = 0 ∨ q = 2 → 2 ∉ transition q a := by
  intro h
  rcases h with h0 | h2 <;>
  (first | rw[h0] | rw[h2]) <;>
  rcases alphabet a with g0 | g1 <;>
  (first | rw[g0] | rw[g1]) <;>
  simp only [transition] <;>
  decide

lemma hat_once : hat transition q [x] = transition q x := by
  simp only [hat, Finset.biUnion_singleton_eq_self]

lemma hat_append (xs ys : List (Fin 2)) :
  hat transition q (xs ++ ys) = (hat transition q xs).biUnion (fun q' => hat transition q' ys) := by
  induction xs generalizing q with
  | nil =>
    rw[hat]
    simp only [List.nil_append, Finset.singleton_biUnion]
  | cons x xs ih =>
    simp only [List.cons_append, hat, ih]
    aesop

lemma hat_append_single :
  hat transition q (w ++ [x]) = (hat transition q w).biUnion (fun q' => transition q' x) := by
  simp only[← hat_once]
  rw[hat_append]

lemma reach_q0 {xs : List (Fin 2)} :
  0 ∈ hat transition 0 xs := by
  induction xs using List.reverseRecOn with
  | nil =>
    rw[hat]
    decide
  | append_singleton ys y ih =>
    rw[hat_append]
    simp only [Finset.mem_biUnion]
    use 0
    rw[hat_once]
    exact ⟨ih, q0⟩

lemma exists_append {α} {xs : List α} :
  xs.length > 0 → ∃ ys x, xs = ys ++ [x] := by
  intro h
  induction xs using List.reverseRecOn with
  | nil =>
    rw[List.length] at h
    contradiction
  | append_singleton ys x _ =>
    use ys, x

lemma length_q1 {xs : List (Fin 2)} :
  1 ∈ hat transition 0 xs → xs.length > 0 := by
  intro h
  cases xs with
  | nil =>
    rw[hat] at h
    contradiction
  | cons a as =>
    simp only [List.length_cons]
    omega

lemma reach_q1 (xs : List (Fin 2)) :
  1 ∈ hat transition 0 xs ↔ ∃ ys, 0 ∈ hat transition 0 ys ∧ xs = ys ++ [0] := by
  constructor
  · intro h
    obtain ⟨as, a, ha⟩ := exists_append (length_q1 h)
    cases alphabet a with
    | inl h0 =>
      rw[h0] at ha
      use as
      exact ⟨reach_q0, ha⟩
    | inr h1 =>
      rw[h1] at ha
      rw[ha, hat_append_single, Finset.mem_biUnion] at h
      obtain ⟨q, _, hq⟩ := h
      have := not_q1 hq
      contradiction
  · intro ⟨zs, h1, h2⟩
    rw[h2, hat_append_single, Finset.mem_biUnion]
    use 0
    have : 1 ∈ transition 0 0 := by
      rw[transition]
      decide
    constructor <;> assumption

lemma length_q2 {xs : List (Fin 2)} :
  2 ∈ hat transition 0 xs → xs.length > 1 := by
  intro h
  match xs with
  | [] =>
    rw[hat] at h
    contradiction
  | [x] =>
    rw[hat_once] at h
    have := not_q2 (by tauto) h
    contradiction
  | x :: y :: ys =>
    simp only [List.length]
    omega

lemma reach_q2 (xs : List (Fin 2)) :
  2 ∈ hat transition 0 xs ↔ ∃ ys x, 1 ∈ hat transition 0 ys ∧ xs = ys ++ [x] := by
  constructor
  · intro h
    have := length_q2 h
    have : xs.length > 0 := by omega
    obtain ⟨as, a, ha⟩ := exists_append this
    rw[ha, hat_append_single, Finset.mem_biUnion] at h
    use as, a
    obtain ⟨q, hq1, hq2⟩ := h
    constructor
    · have := state q
      have : q = 1 ∨ q = 0 ∨ q = 2 := by tauto
      cases this with
      | inl h1 =>
        rw[h1] at hq1
        assumption
      | inr h02 =>
        have := not_q2 h02 hq2
        contradiction
    · assumption
  · intro ⟨as, a, h1, h2⟩
    rw[h2, hat_append_single, Finset.mem_biUnion]
    use 1
    constructor
    · assumption
    · exact q2

lemma accept_iff (xs : List (Fin 2)) :
  accept ex1 xs ↔ 2 ∈ hat transition 0 xs := by
  constructor
  · intro h
    rw[accept] at h
    dsimp [ex1] at h
    obtain ⟨x, hx⟩ := h
    simp only [Fin.isValue, Finset.mem_inter, Finset.mem_singleton] at hx
    obtain ⟨_, rfl⟩ := hx
    assumption
  · intro h
    rw[accept]
    dsimp [ex1]
    have : 2 ∈ hat transition 0 xs ∩ {2} := by
      simp only [Finset.mem_inter, Finset.mem_singleton, and_true]
      assumption
    use 2

theorem accept_prop (xs : List (Fin 2)) :
  accept ex1 xs ↔ ∃ ys x, xs = ys ++ [0, x]  := by
  simp only[accept_iff, reach_q2, reach_q1, reach_q0, true_and]
  aesop

end Example

end NFA
