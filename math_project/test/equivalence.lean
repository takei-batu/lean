variable (p q : Prop)

#check Iff.intro

-- p ∧ q ↔ q ∧ p
theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q => show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h : q ∧ p => show p ∧ q from And.intro (And.right h) (And.left h))

#check and_swap p q

variable (h : p ∧ q)

#check Iff.mp

-- p ∧ q → q ∧ p
example : p ∧ q → q ∧ p := Iff.mp (and_swap p q)

-- q ∧ p
example : q ∧ p := Iff.mp (and_swap p q) h
