
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


example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry

example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry

end chap3

section chap4

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry

end chap4

-- 2.
example (p q r : Prop) (hp : p) : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  and_intros <;> repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)
  -- and_intros
  -- · apply Or.inl; assumption
  -- · apply Or.inr; apply Or.inl; assumption
  -- · apply Or.inr; apply Or.inr; assumption
