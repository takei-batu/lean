import Mathlib.Data.List.Basic
import Mathlib.Control.Basic
set_option linter.style.longLine false
-- set_option linter.unusedVariables false

-- Formula（論理式）の定義
inductive Formula where
  | atom (name : String) : Formula -- 命題変数記号（Stringでタグ付け）
  | bot : Formula -- ⊥
  | imp : Formula → Formula → Formula -- 含意 A → B
  | and : Formula → Formula → Formula -- 連言 A ∧ B
  | or : Formula → Formula → Formula -- 選言 A ∨ B
deriving Repr, DecidableEq

-- ¬ A ↔ A → ⊥
def Formula.not (A : Formula) : Formula := Formula.imp A Formula.bot

notation "⊥"   => Formula.bot
infixr:55 " ⇒ " => Formula.imp
infixl:60 " ∧ " => Formula.and
infixl:55 " ∨ " => Formula.or
prefix:75 "¬" => Formula.not

-- 表示を見やすくする設定 (ToString)
def Formula.toStr : Formula → String
  | atom s => s
  | bot => "⊥"
  | imp A B => "(" ++ A.toStr ++ " → " ++ B.toStr ++ ")"
  | and A B => "(" ++ A.toStr ++ " ∧ " ++ B.toStr ++ ")"
  | or A B  => "(" ++ A.toStr ++ " ∨ " ++ B.toStr ++ ")"

-- Provable (Bottom up)
inductive Provable : List Formula → Formula → Prop where
  | Axiom (h : A ∈ Γ) : Provable Γ A
  | ImpIntro (h : Provable (A :: Γ) B) : Provable Γ (Formula.imp A B)
  | ImpElim (h₁ : Provable Γ A) (h₂ : Provable Γ (Formula.imp A B)) : Provable Γ B
  | AndIntro (h₁ : Provable Γ A) (h₂ : Provable Γ B) : Provable Γ (Formula.and A B)
  | AndElimL (h : Provable Γ (Formula.and A B)): Provable Γ A
  | AndElimR (h : Provable Γ (Formula.and A B)): Provable Γ B
  | OrIntroL (h : Provable Γ A) : Provable Γ (Formula.or A B)
  | OrIntroR (h : Provable Γ B) : Provable Γ (Formula.or A B)
  | OrElim (h₁ : Provable Γ (Formula.or A B)) (h₂ : Provable (A :: Γ) C) (h₃ : Provable (B :: Γ) C) : Provable Γ (Formula.and A B)
  | Exp (h : Provable Γ Formula.bot) : Provable Γ A
  | LEM : Provable Γ (Formula.or A (Formula.not A))
infix:50 " ⊢ " => Provable

-- Deriving (Top Down)
inductive Rule where
  | Intro
  | Elim
deriving Repr, DecidableEq

inductive Label where
  | Imp | And | Or | Not
  | Exp | LEM | DNE | RAA
  | Assume
deriving Repr, DecidableEq

inductive Side where
  | Left
  | Right
  | None
deriving Repr, DecidableEq

-- NodeInfo
structure NodeInfo where
  rule : Rule := Rule.Intro
  label : Label := Label.Assume
  side : Side := Side.None
deriving Repr, DecidableEq

-- ProofTree
inductive ProofTree where
  | assumption (info : NodeInfo) (F : Formula)
  | unary (info : NodeInfo) (T : ProofTree)
  | binary (info : NodeInfo) (T₁ T₂ : ProofTree)
  | trinary (info : NodeInfo) (T₁ T₂ T₃ : ProofTree)
deriving Repr, DecidableEq

-- ProofState
structure ProofState where
  hypothesis : List Formula
  consequence : Formula
  tree : ProofTree
deriving Repr

-- assumption rule
def Assume (A : Formula) : Option ProofState :=
  let tree := ProofTree.assumption {} A
  some {
    hypothesis := [A]
    consequence := A
    tree := tree }

-- inference rule
def ImpIntro (A : Formula) (P : ProofState) : Option ProofState :=
  let newH := P.hypothesis.filter (fun x => x != A)
  let newF := Formula.imp A P.consequence
  let info : NodeInfo := {
    rule := Rule.Intro
    label := Label.Imp }
  let newT := ProofTree.unary info P.tree
  some { P with
    hypothesis := newH
    consequence := newF
    tree := newT }
def Imp_I (A : Formula) (P : Option ProofState) : Option ProofState := P.bind (fun P => ImpIntro A P)

def ImpElim (minor major : ProofState) : Option ProofState :=
  match major.consequence with
  | Formula.imp A B =>
    if A == minor.consequence then
      let newH := minor.hypothesis ∪ major.hypothesis
      let info : NodeInfo := {
        rule := Rule.Elim
        label := Label.Imp }
      let newT := ProofTree.binary info minor.tree major.tree
      some {
        hypothesis := newH
        consequence := B
        tree := newT }
    else none
  | _ => none
def Imp_E (minor major : Option ProofState) : Option ProofState := major.bind (fun M => minor.bind (fun m => ImpElim m M))

def AndIntro (P₁ P₂ : ProofState) : Option ProofState :=
  let newH := P₁.hypothesis ∪ P₂.hypothesis
  let newF := Formula.and P₁.consequence P₂.consequence
  let info : NodeInfo := {
      rule := Rule.Intro
      label := Label.And }
  let newT := ProofTree.binary info P₁.tree P₂.tree
  some {
    hypothesis := newH
    consequence := newF
    tree := newT }
def And_I (P₁ P₂ : Option ProofState) : Option ProofState := P₁.bind (fun P₁ => P₂.bind (fun P₂ => AndIntro P₁ P₂))

def AndElim (d : Side) (P : ProofState) : Option ProofState :=
  match P.consequence with
  | Formula.and A B =>
    let info : NodeInfo := {
        rule := Rule.Elim
        label := Label.And
        side := d }
    let newT := ProofTree.unary info P.tree
    some { P with
      consequence := if d == Side.Left then A else B
      tree := newT }
  | _ => none
def And_E (d : Side) (P : Option ProofState) : Option ProofState := P.bind (fun P => AndElim d P)

def OrIntro (A : Formula) (d : Side) (P : ProofState) : Option ProofState :=
  let newF := if d == Side.Left then (Formula.or P.consequence A) else (Formula.or A P.consequence)
  let info : NodeInfo := {
      rule := Rule.Intro
      label := Label.Or
      side := d }
  let newT := ProofTree.unary info P.tree
  some { P with
    consequence := newF
    tree := newT }
def Or_I (A : Formula) (d : Side) (P : Option ProofState) : Option ProofState := P.bind (fun P => OrIntro A d P)

def OrElim (major left right : ProofState) : Option ProofState :=
  match major.consequence with
  | Formula.or A B =>
    if left.consequence == right.consequence then
      let newH := major.hypothesis ∪ left.hypothesis.filter (fun x => x != A) ∪ right.hypothesis.filter (fun x => x != B)
      let newF := left.consequence
      let info : NodeInfo := {
          rule := Rule.Elim
          label := Label.Or }
      let newT := ProofTree.trinary info major.tree left.tree right.tree
      some {
        hypothesis := newH
        consequence := newF
        tree := newT }
      else none
  | _ => none
def Or_E (major left right : Option ProofState) : Option ProofState := major.bind (fun M => left.bind (fun L => right.bind (fun R => OrElim M L R)))

def NotIntro (A : Formula) (P : ProofState) : Option ProofState :=
  if P.consequence == Formula.bot then
    let newH := P.hypothesis.filter (fun x => x != A)
    let newF := Formula.not A
    let info : NodeInfo := {
      rule := Rule.Intro
      label := Label.Not }
    let newT := ProofTree.unary info P.tree
    some { P with
      hypothesis := newH
      consequence := newF
      tree := newT }
  else none
def Not_I (A : Formula) (P : Option ProofState) : Option ProofState := P.bind (fun P => NotIntro A P)

def NotElim (minor major : ProofState) : Option ProofState :=
  match major.consequence with
  | Formula.imp A Formula.bot =>
    if A == minor.consequence then
      let newH := minor.hypothesis ∪ major.hypothesis
      let info : NodeInfo := {
        rule := Rule.Elim
        label := Label.Not }
      let newT := ProofTree.binary info minor.tree major.tree
      some {
        hypothesis := newH
        consequence := Formula.bot
        tree := newT }
    else none
  | _ => none
def Not_E (minor major : Option ProofState) : Option ProofState := major.bind (fun M => minor.bind (fun m => NotElim m M))

def Law_of_EXP (A : Formula) (P : ProofState) : Option ProofState :=
  if P.consequence == Formula.bot then
    let info : NodeInfo := {
      rule := Rule.Elim -- ⊥ を取り除くという意味合い
      label := Label.Exp }
    let newT := ProofTree.unary info P.tree
    some { P with
      consequence := A
      tree := newT }
  else none
def EXP (A : Formula) (P : Option ProofState) : Option ProofState := P.bind (fun P => Law_of_EXP A P)

def Law_of_LEM (A : Formula) (P : ProofState) : Option ProofState :=
  let newF := Formula.or A (Formula.not A)
  let info : NodeInfo := {
    rule := Rule.Intro -- 仮定無しで結論づけるという意味合い
    label := Label.LEM }
  let newT := ProofTree.assumption info newF
  some { P with
    consequence := newF
    tree := newT }
def LEM (A : Formula) (P : Option ProofState) : Option ProofState := P.bind (fun P => Law_of_LEM A P)

def Law_of_DNE (A : Formula) (P : ProofState) : Option ProofState :=
  if P.consequence == Formula.not (Formula.not A) then
    let info : NodeInfo := {
      rule := Rule.Elim -- 仮定無しで結論づけるという意味合い
      label := Label.DNE }
    let newT := ProofTree.unary info P.tree
    some { P with
      consequence := A
      tree := newT }
  else none
def DNE (A : Formula) (P : Option ProofState) : Option ProofState := P.bind (fun P => Law_of_DNE A P)

def Law_of_RAA (A : Formula) (P : ProofState) : Option ProofState :=
  if P.consequence == Formula.bot then
    let newH := P.hypothesis.filter (fun x => x != Formula.not A)
    let info : NodeInfo := {
      rule := Rule.Intro -- RAAを導入するという意味合い
      label := Label.RAA }
    let newT := ProofTree.unary info P.tree
    some { P with
      hypothesis := newH
      consequence := A
      tree := newT }
  else none
def RAA (A : Formula) (P : Option ProofState) : Option ProofState := P.bind (fun P => Law_of_RAA A P)

-- soundness
namespace ProofState

-- ProofState → Prop
def toProp (P : ProofState) : Prop :=
  Provable P.hypothesis P.consequence

end ProofState

-- theorem ImpIntro_is_valid (A : Formula) (P : ProofState) :
--   P.toProp → ∀ S : ProofState, ImpIntro P A = some S -> S.toProp := by
--   sorry
