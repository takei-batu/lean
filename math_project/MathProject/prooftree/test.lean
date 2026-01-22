-- import ProofWidgets
import MathProject.prooftree.prop
import MathProject.prooftree.tree_to_latex

open Formula MyStyle

def A := atom "A"
def B := atom "B"
def C := atom "C"

def P : Proof :=
  Assume (A ∧ B)
  <|
  And_Intro
  (And_Elim_Right <| Take (A ∧ B))
  (And_Elim_Left <| Take (A ∧ B))
  |>
  Imp_Intro (A ∧ B)

def P1 : Proof := by
  assume A ∧ B
  unary
    binary
    · unary
        take A ∧ B
      yields And_Elim_Right
    · unary
        take A ∧ B
      yields And_Elim_Left
    yields And_Intro
  yields Imp_Intro (A ∧ B)

def P2 : Proof := by
  assume A ∧ B
  imp_I A ∧ B
  and_I
  · and_ER
    take A ∧ B
  · and_EL
    take A ∧ B

#eval P
#eval P1
#eval P2

-- #eval (¬A).toLatex
-- #eval (¬¬A).toLatex

-- #eval (A ⇒ B).toLatex
-- #eval (A ⇒ ⊥).toLatex
-- #eval (A ⇒ B ⇒ C).toLatex
-- #eval (A ⇒ (B ⇒ C)).toLatex
-- #eval ((A ⇒ B) ⇒ C).toLatex

-- #eval (A ∧ B).toLatex
-- #eval (A ∧ B ∧ C).toLatex
-- #eval (A ∧ (B ∧ C)).toLatex
-- #eval ((A ∧ B) ∧ C).toLatex

-- #eval (A ∨ B).toLatex
-- #eval (A ∨ B ∨ C).toLatex
-- #eval (A ∨ (B ∨ C)).toLatex
-- #eval ((A ∨ B) ∨ C).toLatex

-- #eval (A ↔ B).toLatex
-- #eval (A ↔ B ↔ C).toLatex
-- #eval (A ↔ (B ↔ C)).toLatex
-- #eval ((A ↔ B) ↔ C).toLatex

-- #eval (A ∨ B ∧ C).toLatex
-- #eval (A ∧ B ∨ C).toLatex
-- #eval (¬A ∧ B ⇒ C).toLatex
-- #eval (A ⇒ ¬B ∧ C).toLatex

#eval IO.println (P.run []).toOption.get!.tree.toLatex
#eval IO.println P.toLatex.get!

-- open ProofWidgets
-- open ProofWidgets.Jsx
-- open Lean
