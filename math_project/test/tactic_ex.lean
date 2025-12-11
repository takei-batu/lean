example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq

example (p q : Prop) : p ∧ q → q ∧ p := by
  intro hpq
  apply And.intro
  apply And.right
  exact hpq
  apply And.left
  exact hpq

example (p q : Prop) : p ∧ q → q ∧ p := by
  intro hpq
  cases hpq with
  | intro hp hq => constructor; exact hq; exact hp

example (p q : Prop) : p ∧ q → q ∧ p := by
  intro hpq
  cases hpq with
  | intro hp hq => constructor <;> assumption

example (p q : Prop) : p ∧ q → q ∧ p := by
  intro ⟨ hp, hq ⟩
  exact ⟨ hq , hp ⟩

example (p q : Prop) : p ∧ q → q ∧ p := by
  intro ⟨ hp, hq ⟩ ; constructor <;> assumption
