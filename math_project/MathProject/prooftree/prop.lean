import Lean
-- set_option linter.style.longLine false

inductive Formula where
  | atom (name : String) : Formula -- atomic formula
  | bot : Formula -- ⊥
  | not : Formula → Formula -- ¬A
  | imp : Formula → Formula → Formula -- A ⇒ B
  | and : Formula → Formula → Formula -- A ∧ B
  | or : Formula → Formula → Formula -- A ∨ B
  | iff : Formula → Formula → Formula -- A ↔ B
deriving Repr, DecidableEq

-- namespace Formula
-- end Formula

-- abbrev not (A : Formula) : Formula := imp A bot
-- abbrev iff (A B : Formula) : Formula := and (imp A B) (imp B A)

instance : Inhabited Formula where
  default := Formula.atom "False"

namespace MyStyle

notation "⊥"   => Formula.bot
notation:20 left:20 " ↔ " right:21 => Formula.iff left right
notation:25 left:26 " ⇒ " right:25 => Formula.imp left right
notation:30 left:31 " ∨ " right:30 => Formula.or left right
notation:35 left:36 " ∧ " right:35 => Formula.and left right
notation:40 " ¬ " arg:40 => Formula.not arg

end MyStyle

-- def Formula.toStr : Formula → String
--   | atom s => s
--   | bot => "⊥"
--   | not A => s!"¬({A.toStr})"
--   | imp A B => s!"({A.toStr} ⇒ {B.toStr})"
--   | and A B => s!"({A.toStr} ∧ {B.toStr})"
--   | or A B  => s!"({A.toStr} ∨ {B.toStr})"
--   | iff A B => s!"({A.toStr} ↔ {B.toStr})"

inductive Rule where
  | assume
  | imp_intro
  | imp_elim
  | and_intro
  | and_elim_left
  | and_elim_right
  | or_intro_left
  | or_intro_right
  | or_elim
  | not_intro
  | not_elim
  | exp
  | lem
  | dne
  | raa
deriving Repr, DecidableEq

inductive Tree where
  | leaf (A : Formula) : Tree
  -- | node (premisses : List Tree) (rule : Rule) (conclusion : Formula) : Tree
  | unary (T : Tree) (rule : Rule) (C : Formula) : Tree
  | binary (T₁ T₂ : Tree) (rule : Rule) (C : Formula) : Tree
  | trinary (T₁ T₂ T₃ : Tree) (rule : Rule) (C : Formula) : Tree
deriving Repr

instance : Inhabited Tree where
  default := Tree.leaf default

abbrev Context := List Formula

structure proof where
  hypothesis : Context
  consequence : Formula
  tree : Tree
deriving Repr

instance : Inhabited proof where
  default := {
    hypothesis := []
    consequence := default
    tree := default
  }

inductive ProofError
  | failed
  | not_found_assumption (A : Formula)
  | major_mismatch (rule : Rule) (expected : Formula) (actual : Formula)
  | minor_mismatch (rule : Rule) (expected : Formula) (actual : Formula)
deriving Repr, BEq

instance : Lean.ToMessageData ProofError where
  toMessageData
    | .failed => m!"Proof was Failed !"
    | .not_found_assumption A => m!"Not Assumed hypothesis {repr A} !"
    | .major_mismatch rule expected actual =>
      m!"{repr rule} is not able to apply the major premises {repr actual} !\n Expected Formula : such {repr expected}."
    | .minor_mismatch rule expected actual =>
      m!"{repr rule} is not able to apply the minor premises {repr actual} !\n Expected Formula : such {repr expected}."

-- abbrev Proof := ReaderT Context Option proof
abbrev Proof := ReaderT Context (Except ProofError) proof

-- instance : Repr Proof where
--   reprPrec P prec :=
--     match P.run [] with
--     | some p => reprPrec p prec
--     | none => "Proof Verification Failed"
instance : Repr Proof where
  reprPrec P _ :=
    match P.run [] with
    | Except.ok p => repr p
    | Except.error e => repr e

open Formula ProofError

def push (A : Formula) (premises : Context) : Context :=
  A :: premises

def discharge (A : Formula) (premises : Context) : Except ProofError Context :=
  if premises.contains A then
    Except.ok (premises.filter (fun x => x != A))
  else Except.error (not_found_assumption A)

def merge (premises₁ premises₂ : Context) : Context :=
  (premises₁ ++ premises₂).eraseDups

def Assume (A : Formula) (P : Proof) : Proof :=
  withReader (push A) P

def Take (A : Formula) : Proof := do
  let ctx ← read
  if ctx.contains A then
    pure {
      hypothesis := [A]
      consequence := A
      tree := Tree.leaf A
    }
  else throw (not_found_assumption A)

def Imp_Intro (A : Formula) (premises : Proof) : Proof := do
  let P ← premises
  let rule := Rule.imp_intro
  let prem ← discharge A P.hypothesis
  let cons := .imp A P.consequence
  pure { P with
    hypothesis := prem
    consequence := cons
    tree := Tree.unary P.tree rule cons
  }

def Imp_Elim (minor major : Proof) : Proof := do
  let Pₗ ← minor
  let Pᵣ ← major
  match Pᵣ.consequence with
  | .imp A B =>
    if Pₗ.consequence == A then
      let rule := Rule.imp_elim
      let prem := merge Pₗ.hypothesis Pᵣ.hypothesis
      let cons := B
      pure {
        hypothesis := prem
        consequence := cons
        tree := Tree.binary Pₗ.tree Pᵣ.tree rule cons
      }
    else throw (minor_mismatch Rule.imp_elim A Pᵣ.consequence)
  | _ =>
    let A := atom "A"
    let B := atom "B"
    throw (major_mismatch Rule.imp_elim (.imp A B) Pₗ.consequence)

def And_Intro (left right : Proof) : Proof := do
  let Pₗ ← left
  let Pᵣ ← right
  let rule := Rule.and_intro
  let prem := merge Pₗ.hypothesis Pᵣ.hypothesis
  let cons := .and Pₗ.consequence Pᵣ.consequence
  pure {
    hypothesis := prem
    consequence := cons
    tree := Tree.binary Pₗ.tree Pᵣ.tree rule cons
  }

def And_Elim_Left (premises : Proof) : Proof := do
  let P ← premises
  match P.consequence with
  | .and A _ =>
    let rule := Rule.and_elim_left
    let prem := P.hypothesis
    let cons := A
    pure {
      hypothesis := prem
      consequence := cons
      tree := Tree.unary P.tree rule cons
    }
  | _ =>
    let A := atom "A"
    let B := atom "B"
    throw (major_mismatch Rule.and_elim_left (.and A B) P.consequence)

def And_Elim_Right (premises : Proof) : Proof := do
  let P ← premises
  match P.consequence with
  | .and _ B =>
    let rule := Rule.and_elim_right
    let prem := P.hypothesis
    let cons := B
    pure {
      hypothesis := prem
      consequence := cons
      tree := Tree.unary P.tree rule cons
    }
  | _ =>
    let A := atom "A"
    let B := atom "B"
    throw (major_mismatch Rule.and_elim_right (.and A B) P.consequence)


def Or_Intro_Left (A : Formula) (premises : Proof) : Proof := do
  let P ← premises
  let rule := Rule.or_intro_left
  let prem := P.hypothesis
  let cons := .or A P.consequence
  pure {
    hypothesis := prem
    consequence := cons
    tree := Tree.unary P.tree rule cons
  }

def Or_Intro_Right (B : Formula) (premises : Proof) : Proof := do
  let P ← premises
  let rule := Rule.or_intro_right
  let prem := P.hypothesis
  let cons := .or P.consequence B
  pure {
    hypothesis := prem
    consequence := cons
    tree := Tree.unary P.tree rule cons
  }

def Or_Elim (major left right : Proof) : Proof := do
  let P ← major
  let Pₗ ← left
  let Pᵣ ← right
  match P.consequence with
  | .or A B =>
    if Pₗ.consequence == Pᵣ.consequence then
      let rule := Rule.or_elim
      let Δₗ ← discharge A Pₗ.hypothesis
      let Δᵣ ← discharge B Pᵣ.hypothesis
      let prem := merge P.hypothesis (merge Δₗ Δᵣ)
      let cons := Pₗ.consequence
      pure {
        hypothesis := prem
        consequence := cons
        tree := Tree.trinary P.tree Pₗ.tree Pᵣ.tree rule cons
      }
    else throw (minor_mismatch Rule.or_elim Pₗ.consequence Pᵣ.consequence)
  | _ =>
    let A := atom "A"
    let B := atom "B"
    throw (major_mismatch Rule.or_elim (.or A  B) P.consequence)

def Not_Intro (A : Formula) (premises : Proof) : Proof := do
  let P ← premises
  let rule := Rule.not_intro
  let prem ← discharge A P.hypothesis
  let cons := .not A
  pure { P with
    hypothesis := prem
    consequence := cons
    tree := Tree.unary P.tree rule cons
  }

def Not_Elim (minor major : Proof) : Proof := do
  let Pₗ ← minor
  let Pᵣ ← major
  match Pᵣ.consequence with
  | .imp A .bot =>
    if Pₗ.consequence == A then
      let rule := Rule.not_elim
      let prem := merge Pₗ.hypothesis Pᵣ.hypothesis
      let cons := .bot
      pure {
        hypothesis := prem
        consequence := cons
        tree := Tree.binary Pₗ.tree Pᵣ.tree rule cons
      }
    else throw (minor_mismatch Rule.not_elim A Pᵣ.consequence)
  | _ =>
    let A := atom "A"
    throw (major_mismatch Rule.not_elim (.not A) Pₗ.consequence)

def EXP (A : Formula) (premises : Proof) : Proof := do
  let P ← premises
  match P.consequence with
  | .bot =>
    let rule := Rule.exp
    let prem := P.hypothesis
    let cons := A
    pure { P with
      hypothesis := prem
      consequence := cons
      tree := Tree.unary P.tree rule cons
    }
  | _ => throw (major_mismatch Rule.exp .bot P.consequence)

def LEM (A : Formula) (premises : Proof) : Proof := do
  let P ← premises
  match P.consequence with
  | .bot =>
    let rule := Rule.lem
    let prem ← discharge (.not A) P.hypothesis
    let cons := A
    pure {
      hypothesis := prem
      consequence := cons
      tree := Tree.unary P.tree rule cons
    }
  | _ => throw (major_mismatch Rule.lem .bot P.consequence)

def DNE (premises : Proof) : Proof := do
  let P ← premises
  match P.consequence with
  | .not (.not A) =>
    let rule := Rule.dne
    let prem := P.hypothesis
    let cons := A
    pure {
      hypothesis := prem
      consequence := cons
      tree := Tree.unary P.tree rule cons
    }
  | _ =>
    let A := atom "A"
    throw (major_mismatch Rule.dne (.not (.not A)) P.consequence)

open Lean.Parser.Tactic

syntax "unary" tactic "yields" term : tactic
macro_rules
  | `(tactic| unary $seq yields $rule) =>
    `(tactic| refine $rule ?_ ; {$seq})

syntax "binary" tactic* "yields" term : tactic
macro_rules
  | `(tactic| binary $seq1 $seq2 yields $rule) =>
    `(tactic| refine $rule ?_ ?_ ; {$seq1} ; {$seq2})

syntax "trinary" tactic* "yields" term : tactic
macro_rules
  | `(tactic| trinary $seq1 $seq2 $seq3 yields $rule) =>
    `(tactic| refine $rule ?_ ?_ ?_ ; {$seq1} ; {$seq2} ; {$seq3})

macro "take" f:term : tactic => `(tactic| exact Take $f)
macro "assume" f:term : tactic => `(tactic| refine Assume $f ?_)

macro "imp_I" f:term : tactic => `(tactic| refine Imp_Intro $f ?_)
-- macro "imp_I_end" f:term : tactic => `(tactic| exact Imp_Intro ($f) ‹Proof›)
macro "and_I" : tactic => `(tactic| refine And_Intro ?_ ?_)
macro "and_EL" : tactic => `(tactic| refine And_Elim_Left ?_)
macro "and_ER" : tactic => `(tactic| refine And_Elim_Right ?_)
