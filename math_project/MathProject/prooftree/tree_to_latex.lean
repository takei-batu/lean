import MathProject.prooftree.prop

namespace Rule

def toLatex (rule : Rule) : String :=
  match rule with
  | imp_intro => "$\\to$I"
  | imp_elim => "$\\to$E"
  | and_intro => "$\\land$I"
  | and_elim_left => "$\\land$E-L"
  | and_elim_right => "$\\land$E-R"
  | or_intro_left => "$\\lor$I-L"
  | or_intro_right => "$\\lor$I-R"
  | or_elim => "$\\lor$E"
  | not_intro => "$\\not$I"
  | not_elim => "$\\not$E"
  | exp => "EXP"
  | lem => "LEM"
  | dne => "DNE"
  | raa => "RAA"
  | _ => ""

end Rule

namespace Formula

def precedence : Formula → Nat
  | iff _ _ => 20
  | imp _ _ => 25
  | and _ _ => 30
  | or _ _ => 30
  | not _   => 40
  | _       => 100

def toLatex (A : Formula) (parentPrec : Nat := 0) : String :=
  let currentPrec := A.precedence
  let body :=
    match A with
    | atom s => s
    | bot => s!"\\bot"
    | not A  =>  s!"\\neg {A.toLatex 40}"
    | imp A B => s!"{A.toLatex 26} \\to {B.toLatex 25}"
    | and A B => s!"{A.toLatex 31} \\land {B.toLatex 30}"
    | or A B => s!"{A.toLatex 31} \\or {B.toLatex 30}"
    | iff A B => s!"{A.toLatex 21} \\iff {B.toLatex 20}"
  if currentPrec < parentPrec then
    s!"({body})"
  else
    body

end Formula

namespace Tree

def toLatex (T : Tree) : String :=
  match T with
  | .leaf C =>
    "\\AxiomC{" ++ s!"${C.toLatex}$" ++ "}"
  | .unary T rule C =>
    s!"{T.toLatex}\n" ++
    "\\RightLabel{\\scriptsize " ++ s!"{rule.toLatex}" ++ "}\n" ++
    "\\UnaryInfC{" ++ s!"${C.toLatex}$" ++ "}"
  | .binary T₁ T₂ rule C =>
    s!"{T₁.toLatex}\n" ++
    s!"{T₂.toLatex}\n" ++
    "\\RightLabel{\\scriptsize " ++ s!"{rule.toLatex}" ++ "}\n" ++
    "\\BinaryInfC{" ++ s!"${C.toLatex}$" ++ "}"
  | .trinary T₁ T₂ T₃ rule C =>
    s!"{T₁.toLatex}\n" ++
    s!"{T₂.toLatex}\n" ++
    s!"{T₃.toLatex}\n" ++
    "\\RightLabel{\\scriptsize " ++ s!"{rule.toLatex}" ++ "}\n" ++
    "\\TrinaryInfC{" ++ s!"{C.toLatex}" ++ "}"

end Tree

namespace Proof

def toLatex (P : Proof) : Option String :=
  match P.run [] with
  | Except.ok p =>
    let proofs := p.tree.toLatex
    "\\documentclass[border=10pt]{standalone}\n\n" ++
    "\\usepackage{bussproofs}\n" ++
    "\\usepackage{amssymb}\n" ++
    "\\usepackage{amsmath}\n\n" ++
    "\\begin{document}\n" ++
    -- "\\begin{prooftree}\n" ++
    s!"{proofs}\n" ++
    "\\DisplayProof\n" ++
    -- "\\end{prooftree}\n" ++
    "\\end{document}"
  | _ => none

end Proof
