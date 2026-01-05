import MathProject.prooftree.prop
open Formula

def A := atom "A"
def B := atom "B"

-- open Provable
theorem t1 : [A] ⊢ A := by
  apply Provable.Axiom
  trivial

theorem t2 : [] ⊢ A ⇒ A := by
  exact Provable.ImpIntro t1

theorem t3 : [A, B] ⊢ A ∧ B := by
  apply Provable.AndIntro
  · apply Provable.Axiom
    trivial
  · apply Provable.Axiom
    trivial

theorem t4 : [] ⊢ A ⇒ B ⇒ A ∧ B := by
  apply Provable.ImpIntro
  apply Provable.ImpIntro
  apply Provable.AndIntro
  · apply Provable.Axiom
    trivial
  · apply Provable.Axiom
    trivial

def P1 : Option ProofState := Assume A
#eval P1

def P2 : Option ProofState := by
  apply Imp_I A
  exact (Assume A)
#eval P2

def P3 : Option ProofState := by
  apply And_I
  · exact Assume A
  · exact Assume B
#eval P3

def P4 : Option ProofState := by
  apply Imp_I A
  apply Imp_I B
  apply And_I
  · exact Assume A
  · exact Assume B
#eval P4

-- example : [A] ⊢ A := by
