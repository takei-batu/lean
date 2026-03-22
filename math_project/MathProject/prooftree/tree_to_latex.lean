import MathProject.prooftree.prop

namespace Rule

def toLatex (rule : Rule) : String :=
  match rule with
  | imp_intro => r"$\to$\,I"
  | imp_elim => r"$\to$\,E"
  | and_intro => r"$\land$\,I"
  | and_elim_left => r"$\land$\,E-L"
  | and_elim_right => r"$\land$\,E-R"
  | or_intro_left => r"$\lor$\,I-L"
  | or_intro_right => r"$\lor$\,I-R"
  | or_elim => r"$\lor$\,E"
  | not_intro => r"$\not$\,I"
  | not_elim => r"$\not$\,E"
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
    | bot => r"\bot"
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
    r"\AxiomC{" ++ s!"${C.toLatex}$}"
  | .unary T rule C =>
    String.intercalate "\n" [
      s!"{T.toLatex}",
      r"\RightLabel{\ " ++ s!"{rule.toLatex}}",
      r"\UnaryInfC{" ++ s!"${C.toLatex}$}"
    ]
  | .binary T₁ T₂ rule C =>
    String.intercalate "\n" [
      s!"{T₁.toLatex}",
      s!"{T₂.toLatex}",
      r"\RightLabel{\ " ++ s!"{rule.toLatex}}",
      r"\BinaryInfC{" ++ s!"${C.toLatex}$}"
    ]
  | .trinary T₁ T₂ T₃ rule C =>
    String.intercalate "\n" [
      s!"{T₁.toLatex}",
      s!"{T₂.toLatex}",
      s!"{T₃.toLatex}",
      r"\RightLabel{\ " ++ s!"{rule.toLatex}}",
      r"\TrinaryInfC{" ++ s!"{C.toLatex}}"
    ]

end Tree

namespace Proof

def toTree (P : Proof) : String := Id.run do
  let mut i : Nat := 0
  match P.run [] with
  | Except.ok p =>
    match p.tree with
    | .leaf C =>
      if p.hypothesis.contains C then
        r"\AxiomC{" ++ s!"${C.toLatex}$}"
      else
        r"\AxiomC{" ++ s!"$[{C.toLatex}]^{i}$}"
    | .unary T rule C =>
      match rule with
      | .imp_intro | .or_elim| .not_intro =>
        i := i + 1
      | _ => pure ()
      String.intercalate "\n" [
        s!"{T.toLatex}",
        r"\RightLabel{\ " ++ s!"{rule.toLatex}}",
        r"\UnaryInfC{" ++ s!"${C.toLatex}$}"
      ]
    | .binary T₁ T₂ rule C =>
      String.intercalate "\n" [
        s!"{T₁.toLatex}",
        s!"{T₂.toLatex}",
        r"\RightLabel{\ " ++ s!"{rule.toLatex}}",
        r"\BinaryInfC{" ++ s!"${C.toLatex}$}"
      ]
    | .trinary T₁ T₂ T₃ rule C =>
      String.intercalate "\n" [
        s!"{T₁.toLatex}",
        s!"{T₂.toLatex}",
        s!"{T₃.toLatex}",
        r"\RightLabel{\ " ++ s!"{rule.toLatex}}",
        r"\TrinaryInfC{" ++ s!"{C.toLatex}}"
      ]
  | _ => ""

def toLatex (P : Proof) : Option String :=
  match P.run [] with
  | Except.ok p =>
    let source := [
      r"\documentclass[border=10pt]{standalone}",
      r"\usepackage{bussproofs}",
      r"\usepackage{amssymb}",
      r"\usepackage{amsmath}",
      r"\begin{document}",
      p.tree.toLatex,
      r"\DisplayProof",
      r"\end{document}"
    ]
    String.intercalate "\n" source
  | _ => none

def get_prooftree (P : Proof) : String :=
  let source := [
    r"\begin{prooftree}",
    P.toTree,
    r"\end{prooftree}"
  ]
  String.intercalate "\n" source
  -- match P.run [] with
  -- | Except.ok p =>
  -- | _ => ""

end Proof
