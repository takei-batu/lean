-- chapter 3 Exercises

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
⟨
  fun h => ⟨ h.right, h.left ⟩,
  fun h => ⟨ h.right, h.left ⟩
⟩

example : p ∧ q ↔ q ∧ p :=
⟨
  fun ⟨ hp , hq ⟩ => ⟨ hq , hp ⟩,
  fun ⟨ hq , hp ⟩ => ⟨ hp , hq ⟩
⟩

example : p ∨ q ↔ q ∨ p :=
⟨
  fun h => Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq),
  fun h => Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)
⟩

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
⟨
  fun h => ⟨ h.left.left, h.left.right, h.right ⟩,
  fun h => ⟨ ⟨ h.left, h.right.left ⟩, h.right.right ⟩ ,
⟩

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
⟨
  fun ⟨⟨hp , hq⟩, hr⟩ => ⟨hp, hq, hr⟩,
  fun ⟨hp, hq, hr⟩ => ⟨⟨hp , hq⟩, hr⟩
⟩

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
⟨
  fun h => Or.elim h
    (fun hpq => Or.elim hpq (fun hp => Or.inl hp) (fun hq => Or.inr (Or.inl hq)))
    (fun h => Or.inr (Or.inr h)),
  fun h => Or.elim h
    (fun hp => Or.inl (Or.inl hp))
    (fun hqr => Or.elim hqr (fun hq => Or.inl (Or.inr hq)) (fun hr => Or.inr hr))
⟩

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
⟨ -- match ver.
  fun h => match h with
  | Or.inl hpq => match hpq with
    | Or.inl hp => Or.inl hp
    | Or.inr hq => Or.inr (Or.inl hq)
  | Or.inr h => Or.inr (Or.inr h),
  fun h => match h with
  | Or.inl hp => Or.inl (Or.inl hp)
  | Or.inr hqr => match hqr with
    | Or.inl hq => Or.inl (Or.inr hq)
    | Or.inr hr => Or.inr hr
⟩

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
⟨
  fun h => Or.elim h.right
    (fun hq => Or.inl ⟨ h.left, hq ⟩)
    (fun hr => Or.inr ⟨ h.left, hr ⟩),
  fun h => Or.elim h
    (fun hpq => ⟨ hpq.left, Or.inl hpq.right ⟩)
    (fun hpr => ⟨ hpr.left, Or.inr hpr.right ⟩)
⟩

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
⟨
  fun h => Or.elim h
    (fun hp => ⟨ Or.inl hp, Or.inl hp ⟩)
    (fun hqr => ⟨ Or.inr hqr.left, Or.inr hqr.right ⟩),
  fun ⟨ hpq , hpr ⟩ => Or.elim hpq
    (fun hp => Or.inl hp)
    (fun hq => Or.elim hpr (fun hp => Or.inl hp) (fun hr => Or.inr ⟨ hq, hr ⟩))
⟩

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
⟨
  fun h => fun hpq => h hpq.left hpq.right,
  fun h => fun hp => fun hq => h ⟨ hp , hq ⟩
⟩
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
⟨
  fun h => ⟨ fun hp => h (Or.inl hp) , fun hq => h (Or.inr hq) ⟩,
  fun ⟨ h₁ , h₂ ⟩ => fun hpq => Or.elim hpq (fun hp => h₁ hp) (fun hp => h₂ hp)
⟩
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
⟨
  fun h => ⟨ fun hp => h (Or.inl hp) , fun hq => h (Or.inr hq) ⟩,
  fun ⟨ h₁ , h₂ ⟩ => fun hpq => Or.elim hpq (fun hp => h₁ hp) (fun hq => h₂ hq)
⟩
example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun h => Or.elim h (fun hnp => fun ⟨ hp , _ ⟩ => hnp hp) (fun hnq => fun ⟨ _ , hq ⟩ => hnq hq)

example : ¬(p ∧ ¬p) := fun ⟨ hp , hnp ⟩ => hnp hp

example : p ∧ ¬q → ¬(p → q) := fun ⟨ h₁ , h₂ ⟩ => fun g => h₂ (g h₁)
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry
