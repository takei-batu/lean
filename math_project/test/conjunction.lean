variable (p q : Prop)

#check And.intro

-- p → q → p ∧ q
example (hp : p) (hq : q) : p ∧ q := And.intro hp hq
#check λ (hp : p) (hq : q) => And.intro hp hq
-- shorthand And.intro
example (hp : p) (hq : q) : p ∧ q := ⟨ hp , hq ⟩

#check And.left
#check And.right

-- p ∧ q → p
example (h : p ∧ q) : p := And.left h
-- shorthand And.left:
example (h : p ∧ q) : p := h.left

-- p ∧ q → p
example (h : p ∧ q) : q := And.right h
-- shorthand And.right:
example (h : p ∧ q) : q := h.right

-- p ∧ q → q ∧ p
example (h : p ∧ q) : q ∧ p := And.intro (And.right h) (And.left h)
-- shorthand above:
example (h : p ∧ q) : q ∧ p := ⟨ h.right, h.left ⟩

-- p ∧ q → q ∧ p ∧ q
example (h : p ∧ q) : q ∧ p ∧ q := ⟨ h.right, ⟨ h.left, h.right ⟩ ⟩
-- you can flatten nestted constructors that associated to the right:
example (h : p ∧ q) : q ∧ p ∧ q := ⟨ h.right, h.left, h.right ⟩
