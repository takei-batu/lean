import Mathlib.Data.List.Basic
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
infixr:55 " → " => Formula.imp
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
  rule : Rule
  label : Label
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
def Assume (P : ProofState) (A : Formula) : Option ProofState :=
  if P.hypothesis.contains A then
    let info : NodeInfo := {
      rule := Rule.Intro -- 仮定の導入という意味合い
      label := Label.Assume }
    let tree := ProofTree.assumption info A
    some { P with
           consequence := A
           tree := tree }
  else
    none

-- inference rule
def ImpIntro (P : ProofState) (A : Formula) : Option ProofState :=
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

def AndElim (P : ProofState) (d : Side) : Option ProofState :=
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

def OrIntro (P : ProofState) (A : Formula) (d : Side) : Option ProofState :=
  let newF := if d == Side.Left then (Formula.or P.consequence A) else (Formula.or A P.consequence)
  let info : NodeInfo := {
      rule := Rule.Intro
      label := Label.Or
      side := d }
  let newT := ProofTree.unary info P.tree
  some { P with
    consequence := newF
    tree := newT }

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

def NotIntro (P : ProofState) (A : Formula) : Option ProofState :=
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

def Exp (P : ProofState) (A : Formula) : Option ProofState :=
  if P.consequence == Formula.bot then
    let info : NodeInfo := {
      rule := Rule.Elim -- ⊥ を取り除くという意味合い
      label := Label.Exp }
    let newT := ProofTree.unary info P.tree
    some { P with
      consequence := A
      tree := newT }
  else none

def LEM (P : ProofState) (A : Formula) : Option ProofState :=
  let newF := Formula.or A (Formula.not A)
  let info : NodeInfo := {
    rule := Rule.Intro -- 仮定無しで結論づけるという意味合い
    label := Label.LEM }
  let newT := ProofTree.assumption info newF
  some { P with
    consequence := newF
    tree := newT }

def DNE (P : ProofState) (A : Formula) : Option ProofState :=
  if P.consequence == Formula.not (Formula.not A) then
    let info : NodeInfo := {
      rule := Rule.Elim -- 仮定無しで結論づけるという意味合い
      label := Label.DNE }
    let newT := ProofTree.unary info P.tree
    some { P with
      consequence := A
      tree := newT }
  else none

def RAA (P : ProofState) (A : Formula) : Option ProofState :=
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

-- inductive Provable (hypothesis : List Formula) (consequence : Formula) : Prop where
inductive Provable : List Formula → Formula → Prop where
  | Axom (h : A ∈ Γ) : Provable Γ A
  | ImpIntro : Provable (Γ ∪ [A]) B → Provable Γ (Formula.imp A B)
  | ImpElim : Provable Γ₁ A → Provable Γ₂ (Formula.imp A B) → Provable (Γ₁ ∪ Γ₂) B
  | AndIntro : Provable Γ₁ A → Provable Γ₂ B → Provable (Γ₁ ∪ Γ₂) (Formula.and A B)
  | AndElimL : Provable Γ (Formula.and A B) → Provable Γ A
  | AndElimR : Provable Γ (Formula.and A B) → Provable Γ B
  | OrIntroL : Provable Γ A → Provable Γ (Formula.or A B)
  | OrIntroR : Provable Γ B → Provable Γ (Formula.or A B)
  | OrElim : Provable Γ₁ (Formula.or A B) → Provable (Γ₂ ∪ [A]) C → Provable (Γ₃ ∪ [B]) C → Provable (Γ₁ ∪ Γ₂ ∪ Γ₃) (Formula.and A B)
  | Exp : Provable Γ Formula.bot → Provable Γ A
  | LEM : Provable Γ (Formula.or A (Formula.not A))

infix:50 " ⊢ " => Provable
