#check And

#check Or

#check Not

def Implies (p q : Prop) : Prop := p → q
#check Implies

variable (p q r : Prop)
#check And p q
#check Or (And p q) r
#check And (Implies p q) (Implies q p)

structure Proof (p : Prop) : Type where
  proof : p
#check Proof

axiom and_commute (p q : Prop) : Proof (Implies (And p q) (And p q))
#check and_commute p q
#check (and_commute p q).proof

-- MP
axiom modus_ponens (p q : Prop) : Proof (Implies p q) → Proof p → Proof q

-- DR
axiom implies_intro (p q : Prop) : (Proof p → Proof q) → Proof (Implies p q)

set_option linter.unusedVariables false
variable {p : Prop}
variable {q : Prop}

theorem t1 : p → q → p := fun hp : p => fun hq : q => hp
#print t1

theorem t2 : p → q → p :=
  fun hp : p =>
  fun hq : q =>
  show p from hp

theorem t3 (hp : p) (hq : q) : p := hp
#print t3

axiom hp : p
theorem t4 : q → p := t3 hp

theorem t5 (p q : Prop) (hp : p) (hq : q) : p := hp

variable (p q r s : Prop)
#check t5 p q
#check t5 r s
#check t5 (r → s) (s → r)

variable (h : r → s)
#check t5 (r → s) (s → r) h

theorem t6 (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p =>
  show r from h₁ (h₂ h₃)

variable (p q r: Prop)
#check t6 p q r
