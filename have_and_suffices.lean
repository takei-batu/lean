variable (p q : Prop)

-- p ∧ q → q ∧ p
example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp

-- p ∧ q → q ∧ p
example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  -- It suffices to show q, by proving the original goal of q ∧ p with the hypothesis hq : q.
  suffices hq : q from And.intro hq hp
  -- Finally, we have to show q.
  show q from And.right h
