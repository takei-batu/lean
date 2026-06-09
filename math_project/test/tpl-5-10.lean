
-- 1.
section chap3

variable (p q r : Prop)

example : p ∨ False ↔ p := by
  constructor
  · intro h
    cases h
    · assumption
    · contradiction
  · intro h
    apply Or.inl; assumption

example : p ∧ False ↔ False := by
  constructor
  · intro ⟨_,_⟩; contradiction
  · intro _; contradiction

example : (p → q) → (¬q → ¬p) := by
  intro h₁ h₂ h₃
  exact h₂ (h₁ h₃)

open Classical

example : (¬q → ¬p) → (p → q) := by
  intro h₁ h₂
  have em := em q
  cases em with
  | inl h => assumption
  | inr h =>
    have := h₁ h h₂
    contradiction

example : p ∨ ¬p := by exact em p

example : (((p → q) → p) → p) := by
  intro h₁
  cases Classical.em p with
  | inl hp => exact hp
  | inr hnp =>
      apply h₁
      intro hp
      have := hnp hp
      contradiction

end chap3

section chap4

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro h x
  cases h with
  | inl g => apply Or.inl (g x)
  | inr g => apply Or.inr (g x)

open Classical

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  constructor
  · intro h
    have em := em r
    cases em with
    | inl hr => apply Or.inr hr
    | inr hnr =>
      apply Or.inl
      intro x
      cases (h x) with
      | inl g => assumption
      | inr g =>
        have := hnr g
        contradiction
  · intro h x
    cases h with
      | inl g => apply Or.inl (g x)
      | inr g => apply Or.inr g

end chap4

-- 2.
example (p q r : Prop) (hp : p) : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  and_intros <;> repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)
  -- and_intros
  -- · apply Or.inl; assumption
  -- · apply Or.inr; apply Or.inl; assumption
  -- · apply Or.inr; apply Or.inr; assumption
