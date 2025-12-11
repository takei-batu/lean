variable (p q : Prop)

#check Or.intro_left
#check Or.intro_right

-- p → p ∨ q
example (hp : p) : p ∨ q := Or.intro_left q hp
-- shorthand Or.intro_left:
example (hp : p) : p ∨ q := Or.inl hp

-- q → p ∨ q
example (hq : q) : p ∨ q := Or.intro_right p hq
-- shorthand Or.intro_right:
example (hq : q) : p ∨ q := Or.inr hq

#check Or.elim

-- p ∨ q → q ∨ p
example (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p => show q ∨ p from Or.intro_right q hp)
    (fun hq : q => show q ∨ p from Or.intro_left p hq)
-- shorthand Or.elim:
example (h : p ∨ q) : q ∨ p :=
  h.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq)
