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
  fun hp : p => -- suppose p
  fun hq : q => -- suppose q
    show p from hp -- get q -> p from q by DR, then get p -> q -> p from q -> p by DR

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

theorem t6 (h₁ : p → q) (h₂ : q → r) : p → r :=
  fun h : p => -- suppose p
    show r from h₂ (h₁ h) -- get q from p -> q and p by MP, then get r from q -> r and q by MP

variable (p q r: Prop)
#check t6 p q r
