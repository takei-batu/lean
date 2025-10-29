open Classical

variable (p : Prop)

-- excluded middle (EM)
#check em
#check em p

-- double-negation elimination (DNE)
-- ¬¬p → p
theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)

-- EM from DNE
-- p → p ∨ ¬p
theorem em_from_dne (p : Prop) : p ∨ ¬p :=
  have lem : ¬¬(p ∨ ¬p) :=
    fun nem : ¬(p ∨ ¬p) => -- suppose ¬(p ∨ ¬p)
      have np : ¬p :=
        fun hp : p => -- suppose p
          have x : p ∨ ¬p :=
            show p ∨ ¬p from Or.inl hp -- infer p ∨ ¬p
        show False from absurd x nem -- infer ⊥ -> infer ¬p
      have y : p ∨ ¬p :=
        show p ∨ ¬p from Or.inr np -- infer p ∨ ¬p
    show False from absurd y nem -- infer ⊥ -> infer ¬¬(p ∨ ¬p)
  show p ∨ ¬p from dne lem -- infer p ∨ ¬p

-- p ∨ ¬p
#check em_from_dne
#check em_from_dne p

variable (p q : Prop)

-- ¬(p ∧ q) → ¬p ∨ ¬q
theorem deMorgan (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  have em : p ∨ ¬p :=
    show p ∨ ¬p from em p -- axiom EM
  have x : p → ¬p ∨ ¬q :=
    fun hp : p => -- suppose p
      have x1 : ¬q :=
        fun hq : q => -- suppose q
          have x2 : p ∧ q :=
            show p ∧ q from ⟨hp, hq⟩ -- infer p ∧ q
      show False from absurd x2 h -- infer ⊥ -> infer ¬q
    show ¬p ∨ ¬q from Or.inr x1 -- infer ¬p ∨ ¬q -> infer p → ¬p ∨ ¬q
  have y : ¬p → ¬p ∨ ¬q :=
    fun hp : ¬p => -- suppose ¬p
      show ¬p ∨ ¬q from Or.inl hp -- infer ¬p ∨ ¬q -> infer ¬p → ¬p ∨ ¬q
  show ¬p ∨ ¬q from Or.elim em x y -- infer ¬p ∨ ¬q
