import Mathlib
open Set

abbrev Var := Int -- 正整数
abbrev Literal := Int -- 命題変数の否定は，負整数
abbrev Clause := Finset Literal --この表現では ∅ が偽
abbrev CNF := Finset Clause     --この表現では, ∅ が真，{∅} が偽
-- lean4 の Set は無限集合も扱うため一般には Decidable ではない（条件文に使えない）
-- 有限集合とするために Finset を使う

def varOfLiteral (i : Int) := abs i

def simp (cnf : CNF) : CNF := if ∅ ∈ cnf then {∅} else cnf

-- リテラル x を真にする
-- 結果: None はリレラル全体が真
-- 講義資料の simp(c[T/l]) に対応
def substClause (c : Clause) (l : Int) : CNF := sorry

-- System.FilePath は パス専用のString（ラップされた String）
def parse (path : System.FilePath) : IO (Int × CNF) := do
  let handle ← IO.FS.Handle.mk path IO.FS.Mode.read
  let firstLine ← handle.getLine
  let firstLineArray := firstLine.splitOn " " |>.filter (· != "")
  let nVars := match firstLineArray[2]? with
  | some s => s.toNat?.getD 0
  | none => 0
  let nCluases := match firstLineArray[3]? with
  | some s => s.toNat?.getD 0
  | none => 0
  let mut cnf : CNF := ∅
  for _ in [:nCluases] do
    let line ← handle.getLine
    let clause := line.splitOn " " |>.filterMap (·.toInt?) |>.toFinset |>.erase 0
    cnf := insert clause cnf
  return (nVars, cnf)
