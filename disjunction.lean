variable (p q r : Prop)

#check Or.intro_left
#check Or.intro_right
example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq

#check Or.elim
example (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p => -- suppose p
      show q ∨ p from Or.intro_right q hp) -- get q ∨ p from q by ∨ intro
    (fun hq : q => -- suppose q
      show q ∨ p from Or.intro_left p hq) -- get q ∨ p from q by ∨ intro

-- shorthand Or.intro:
example (h : p ∨ q) : q ∨ p :=
  Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)

-- same mean:
example (h : p ∨ q) : q ∨ p :=
  h.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq)
