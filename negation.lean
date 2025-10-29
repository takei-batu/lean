variable (p q r : Prop)

-- ¬p is defined as p → False
-- type False is mean ⊥
section
  variable (hp : p) (hnp : ¬p)
  #check hnp hp
end

-- (p → q) → (¬q → ¬p)
example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp : p => show False from hnq (hpq hp)

-- p → ¬p → q
example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)
example (hp : p) (hnp : ¬p) : q := absurd hp hnp

-- ¬p → q → (q → p) → r:
example (hnp : ¬p) (hq : q) (hqp : q → p) : r := absurd (hqp hq) hnp

-- type False has only elimination rule and type True has only introduction rule
#check False.elim
#check True.intro
