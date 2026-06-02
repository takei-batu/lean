import Mathlib
open Set

abbrev Var := Int -- 正整数
abbrev Literal := Int -- 命題変数の否定は，負整数
abbrev Clause := Finset Literal --この表現では ∅ が ⊥
abbrev CNF := Finset Clause --この表現では ∅ が ⊤，{∅} が ⊥
-- lean4 の Set は無限集合も扱うため一般には Decidable ではない（条件文に使えない）
-- 有限集合とするために Finset を使う

-- def varOfLiteral (i : Int) := abs i

def simp (cnf : CNF) : CNF := if ∅ ∈ cnf then {∅} else cnf

def substClause (c : Clause) (l : Int) : CNF :=
  if l ∈ c then ∅
  else if -l ∈ c then {c.erase (-l)}
  else {c}

def substCNF (cnf : CNF) (l : Int) : CNF := cnf.biUnion (substClause · l)

def dpll (cnf : CNF) (vars : List Nat) : Bool :=
  if cnf == ∅ then true
  else if cnf == {∅} then false
  else
    match vars with
    | [] => false -- CNFが空ではないが変数が残っている場合は矛盾
    | var :: remain =>
      let (toTop, toBtm) := (simp (substCNF cnf var), simp (substCNF cnf (-↑var)))
      if (dpll toTop remain) then true
      else if (dpll toBtm remain) then true
      else false

-- System.FilePath は パス専用のString（ラップされた String）
def parser (path : System.FilePath) : IO (Nat × CNF) := do
  let handle ← IO.FS.Handle.mk path IO.FS.Mode.read
  let firstLine ← handle.getLine
  let firstLineArray := firstLine |>.trimAsciiEnd |>.toString |>.splitOn " " |>.filter (· != "")
  let nVars := match firstLineArray[2]? with
  | some s => s.toNat?.getD 0
  | none => 0
  let nCluases := match firstLineArray[3]? with
  | some s => s.toNat?.getD 0
  | none => 0
  let mut cnf : CNF := ∅
  for _ in [:nCluases] do
    let line ← handle.getLine
    let clause := line |>.splitOn " " |>.filterMap (·.toInt?) |>.toFinset |>.erase 0
    cnf := insert clause cnf
  return (nVars, cnf)

def solver (path : System.FilePath) := do
  let (n, cnf) ← parser path
  let result :=  if (dpll cnf (List.range' 1 n)) then "SAT" else "UNSAT"
  IO.println result


-- (x₁ ∨ x₃ ∨ ¬x₄) ∧ x₄ ∧ (x₂ ∨ ¬x₃)
def test1 : CNF := {{1, 3, -4}, {4}, {2, -3}}
#eval dpll test1 [1,2,3,4]

-- (x₁ ∨ x₂ ∨ ¬x₃) ∧ (x₁ ∨ ¬x₂) ∧ ¬x₁ ∧ x₃
def test2 : CNF := {{1, 2, -3}, {1, -2}, {-1}, {3}}
#eval dpll test2 [1,2,3]

-- カレントディレクトリ
#eval IO.Process.getCurrentDir

def ex := solver "./final_project/example1.cnf"
#eval ex

def two_queen := solver "./final_project/N=2.cnf"
#eval two_queen

def eight_queen := solver "./final_project/N=8.cnf"
#eval eight_queen

-- 上記の実装では時間がかかりすぎる
def one_hundred_fifty_queen := solver "./final_project/N=150.cnf"
-- #eval one_hundred_fifty_queen
