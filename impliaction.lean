
set_option linter.unusedVariables false

-- p → q → p (ex1 ~ ex3)
namespace ex1
  variable (p q : Prop)

  -- the lambda abstractions hp : p and hq : q can be viewed as temporary assumptions
  theorem t : p → q → p :=
    fun hp : p => -- suppose p
    fun hq : q => -- suppose q
    hp --  infer p
end ex1

namespace ex2
  variable (p q : Prop)

  -- to specify the type of the final term hp, explicitly, you can use a show statement:
  theorem t : p → q → p :=
    fun hp : p =>
    fun hq : q =>
    show p from hp
end ex2

-- As with ordinary definitions, we can move the lambda-abstracted variables to the left of the colon:
namespace ex3
  variable (p q : Prop)

  -- to specify the type of the final term hp, explicitly, you can use a show statement:
  theorem t (hp : p) (hq : q) : p :=
    show p from hp
end ex3

#print ex1.t
#print ex2.t
#print ex3.t

-- you can use example statement without naming it or storing it in the permanent context:
section
  variable (p q : Prop)
  example (hp : p) (hq : q) : p :=
    show p from hp
end

namespace ex4
  variable {p q : Prop}

  theorem t1 (hp : p) (hq : q) : p := hp
  axiom hp : p
  theorem t2 : q → p := t1 hp
end ex4

namespace ex5
  variable (p q : Prop)

  theorem t (hp : p) (hq : q) : p := hp
end ex5

section
  variable (p q r s : Prop)
  variable (hp : p)
  #check ex5.t p q
  #check ex5.t p q hp
  #check ex5.t r s
  #check ex5.t (r → s) (s → r)
end

namespace ex6
  variable (p q r : Prop)

  theorem t (h₁ : q → r) (h₂ : p → q) : p → r :=
    fun h₃ : p =>
    show r from h₁ (h₂ h₃)
end ex6

section
  variable (p q r s : Prop)
  variable (hqr : q → r) (hpq : p → q) (hp : p)
  #check ex6.t p q r
  #check ex6.t p q r hqr
  #check ex6.t p q r hqr hpq
  #check ex6.t p q r hqr hpq hp
end
