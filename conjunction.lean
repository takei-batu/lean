variable (p q : Prop)

#check And.intro
example (hp : p) (hq : q) : p ∧ q := And.intro hp hq
#check λ (hp : p) (hq : q) => And.intro hp hq

#check And.left
#check And.right
example (h : p ∧ q) : p := And.left h
example (h : p ∧ q) : q := And.right h

-- you can use below istead of And.intro
example (hp : p) (hq : q) : p ∧ q := ⟨ hp , hq ⟩

-- you can use below istead of And.left and And.right
example (h : p ∧ q) : p := h.left
example (h : p ∧ q) : q := h.right

example (h : p ∧ q) : q ∧ p := And.intro (And.right h) (And.left h)
-- you can also be written:
example (h : p ∧ q) : q ∧ p := ⟨ h.right, h.left ⟩

example (h : p ∧ q) : q ∧ p ∧ q := ⟨ h.right, ⟨ h.left, h.right ⟩ ⟩
-- you can flatten nestted constructors that associated to the right:
example (h : p ∧ q) : q ∧ p ∧ q := ⟨ h.right, h.left, h.right ⟩
