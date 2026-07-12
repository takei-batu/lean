import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic


structure DFA (α : Type) [Fintype α] (β : Type) [Fintype β] where
  mk ::
  initial : β
  final : Finset β
  transition : β → α → β

#check DFA.final

namespace DFA

variable {α β : Type} [Fintype α] [Fintype β] (dfa : DFA α β)

-- 与えられた文字列の最終的な状態を返す
def hat (transition : β → α → β) (q : β) : List α → β
  | [] => q
  | x :: xs => hat transition (transition q x) xs

-- 与えらえた文字列の受理判定
def accept (xs : List α) := (hat dfa.transition dfa.initial xs) ∈ dfa.final

namespace Example

-- Σ = {0} and L = { 0^2n }.

def transition : Fin 2 → Fin 1 → Fin 2
  | 0, 0 => 1
  | 1, 0 => 0

def ex1 : DFA (Fin 1) (Fin 2) := DFA.mk 0 {0} transition

example : accept ex1 [] := by
  simp [accept, hat, ex1]

example : accept ex1 [0, 0] := by
  simp [accept, hat, ex1, transition]

example : ¬ (accept ex1 [1]) := by
   simp [accept, hat, ex1, transition]

lemma transition_prop (n : ℕ) :
  hat transition 0 (List.replicate (2 * n) 0) = 0
  ∧ hat transition 0 (List.replicate (2 * n  + 1) 0) = 1
  ∧ hat transition 1 (List.replicate (2 * n) 0) = 1
  ∧ hat transition 1 (List.replicate (2 * n  + 1) 0) = 0
  := by
  -- sorry
  induction n with
  | zero =>
    simp only [Fin.isValue, Nat.mul_zero, List.replicate_zero, Nat.zero_add, List.replicate_one]
    simp only [hat, transition]
    trivial
  | succ n ih =>
    have : 2 * (n + 1) = 2 * n  + 1 + 1 := by omega
    rw [this]
    simp only[List.replicate_succ]
    simp only[hat, transition]
    assumption


theorem Fin1_list (xs : List (Fin 1)) :
  xs = (List.replicate (List.length xs) 0) := by
  -- sorry
  induction xs with
  | nil =>
    simp only [List.length_nil, Fin.isValue, List.replicate_zero]
  | cons x rest ih =>
    simp only [List.length_cons, List.replicate_succ]
    rw[←ih]
    have : x = 0 := Fin.eq_zero x
    rw[this]

lemma Fin1_list_even_odd (xs : List (Fin 1)) : (∃ n, xs = (List.replicate (2 * n) 0) ∨
  xs = (List.replicate (2 * n + 1) 0)) := by
  have h0: xs = (List.replicate (2 * (List.length xs / 2) + (List.length xs % 2)) 0) := by
    rw [Nat.div_add_mod]
    apply Fin1_list
  have h2: List.length xs % 2 = 0 ∨ List.length xs % 2 = 1 := by
    grind
  apply Exists.intro (List.length xs / 2)
  grind


theorem accept_prop (xs : List (Fin 1)) :
  accept ex1 xs ↔ ∃ n, xs = (List.replicate (2 * n) 0) := by
  -- sorry
  constructor
  · intro h
    obtain ⟨n, g⟩ := Fin1_list_even_odd xs
    cases g with
    | inl gl => exact ⟨n, gl⟩
    | inr gr =>
      rw[accept] at h
      dsimp [ex1] at h
      have : hat transition 0 (List.replicate (2 * n  + 1) 0) = 1 := (transition_prop n).right.left
      rw[gr, this] at h
      contradiction
  · intro ⟨n, nh⟩
    rw[accept, nh]
    dsimp [ex1]
    have : hat transition 0 (List.replicate (2 * n) 0) = 0 := (transition_prop n).left
    rw[this]
    decide

end Example


section Complement

variable {α : Type} [Fintype α] {β : Type} [Fintype β] [DecidableEq β]

#check Finset.univ

-- Correct the following definition.
def complement (dfa : DFA α β) : DFA α β :=
    DFA.mk dfa.initial dfa.finalᶜ dfa.transition

theorem correct_comnplement (dfa : DFA α β) (xs : List α) :
    accept (complement dfa) xs ↔ ¬ accept dfa xs := by
    -- sorry
    constructor
    · intro h hc
      rw[accept] at h hc
      dsimp[complement] at h
      simp only [Finset.mem_compl] at h
      exact h hc
    · intro h
      rw[accept] at h ⊢
      dsimp[complement]
      simp only [Finset.mem_compl]
      assumption


end Complement

end DFA
