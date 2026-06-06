import Mathlib
open Set
set_option linter.style.longLine false

abbrev Var := Nat -- 正整数
abbrev Literal := Int -- 命題変数の否定は，負整数
abbrev Clause := Finset Literal --この表現では ∅ が ⊥
abbrev CNF := Finset Clause --この表現では ∅ が ⊤，{∅} が ⊥
abbrev Asg := List Int -- 変数の割り当てのリスト

-- 節を単純化する関数
def simp (cnf : CNF) : CNF := if ∅ ∈ cnf then {∅} else cnf

-- 節の論理式を置換する関数
def substClause (c : Clause) (l : Literal) : CNF :=
  if l ∈ c then ∅
  else if -l ∈ c then {c.erase (-l)}
  else {c}

-- 全体の論理式を置換する関数
def substCNF (cnf : CNF) (l : Literal) : CNF := cnf.biUnion (substClause · l)

/-
  単一のリテラルからなる節のうち最初に現れたものリテラルを返す
  def UnitLiteral (cnf : CNF) (n : Var) : Option Literal := Id.run do
    let UnitClauses := cnf.filter (fun c => c.card == 1)
    for i in [1 : n + 1] do
      if {↑i} ∈ unitClauses then return some ↑i
      if {-↑i} ∈ unitClauses then return some (-↑i)
    return none
  for 文は証明で扱いづらいため，高階関数 List.findSome? で書き換える
-/

def UnitLiteral (cnf : CNF) (n : Var) : Option Literal := --Id.run do
  let UnitClauses := cnf.filter (fun c => c.card == 1)
  let FindUnit := fun i : Var => if {↑i} ∈ UnitClauses then some ↑i else if {-↑i} ∈ UnitClauses then some (-↑i) else none
  (List.range' 1 n (step := 1)).findSome? (FindUnit)

def num_var_set (cnf : CNF) : Finset Var := cnf.biUnion (fun c => c.image Int.natAbs)

def num_var (cnf : CNF) : Var := (num_var_set cnf).card

lemma subst_monotone (cnf : CNF) (l : Literal) : num_var_set (simp (substCNF cnf l)) ⊆ num_var_set cnf := by
  intro c h
  simp only [num_var_set, Finset.mem_biUnion, Finset.mem_image] at h
  simp only [num_var_set, Finset.mem_biUnion, Finset.mem_image]
  obtain ⟨w₁, hw₁, w₂, hw₂, hw₃⟩ := h
  unfold simp at hw₁
  split at hw₁
  next _ =>
    simp only [Finset.mem_singleton] at hw₁
    rw[hw₁] at hw₂
    contradiction
  next g =>
    simp only [substCNF, Finset.mem_biUnion] at hw₁
    obtain ⟨x, ⟨gx₁, gx₂⟩⟩ := hw₁
    unfold substClause at gx₂
    split_ifs at gx₂
    next _ =>
      contradiction
    next _ =>
      simp only [Finset.mem_singleton] at gx₂
      rw[gx₂] at hw₂
      have Thm := Finset.erase_subset (-l) x
      use x
      constructor
      · exact gx₁
      · use w₂
        exact ⟨Thm hw₂, hw₃⟩
    next _ =>
      simp only [Finset.mem_singleton] at gx₂
      rw[gx₂] at hw₂
      use x
      constructor
      · exact gx₁
      · use w₂

lemma UnitLiteral_notin_subst_cnf (cnf : CNF) (l : Literal) : l.natAbs ∉ num_var_set (simp (substCNF cnf l)) := by
  intro h
  simp only [num_var_set, Finset.mem_biUnion, Finset.mem_image] at h
  obtain ⟨w₁, hw₁, w₂, hw₂, hw₃⟩ := h
  unfold simp at hw₁
  split at hw₁
  next _ =>
    simp only [Finset.mem_singleton] at hw₁
    rw[hw₁] at hw₂
    contradiction
  next _ =>
    simp only [substCNF, Finset.mem_biUnion] at hw₁
    obtain ⟨x, ⟨gx₁, gx₂⟩⟩ := hw₁
    rw[Int.natAbs_eq_natAbs_iff] at hw₃
    unfold substClause at gx₂
    split_ifs at gx₂
    next _ => contradiction
    next p₁ p₂ =>
      simp only [Finset.mem_singleton] at gx₂
      have Thm := Finset.erase_subset (-l) x
      rw[gx₂] at hw₂
      have r : w₂ ∈ x := Thm hw₂
      rcases hw₃ with q₁ | q₂
      · rw[q₁] at r
        exact p₁ r
      · rw[q₂] at hw₂
        simp at hw₂
    next p₁ p₂ =>
      simp only [Finset.mem_singleton] at gx₂
      rw[gx₂] at hw₂
      rcases hw₃ with q₁ | q₂
      · rw[q₁] at hw₂
        contradiction
      · rw[q₂] at hw₂
        contradiction

lemma UnitLiteral_in_cnf {cnf : CNF} {n : Var} {l : Literal} (h : UnitLiteral cnf n = some l) : l.natAbs ∈ num_var_set cnf := by
  simp[num_var_set]
  unfold UnitLiteral at h
  dsimp only at h
  simp only [List.findSome?_eq_some_iff] at h
  obtain ⟨_, a, _, _, h₂, _⟩ := h
  split_ifs at h₂
  next g₁ =>
    rw[Finset.mem_filter] at g₁
    rw[Option.some_inj] at h₂
    use {↑a}
    constructor
    · exact g₁.left
    · use ↑a
      rw[h₂, Finset.mem_singleton]
      simp
  next g₂ =>
    rw[Finset.mem_filter] at g₂
    rw[Option.some_inj] at h₂
    use {-↑a}
    constructor
    · exact g₂.left
    · use -↑a
      rw[h₂, Finset.mem_singleton]
      simp

/-
  最頻出の変数のうち最初に現れた変数のリテラルを返す
  def ModeLiteral (cnf : CNF) (n : Var) : Option Literal := Id.run do
    let mut M : Var := 0
    for i in [1 : n + 1] do
      let pos_count := (cnf.filter (fun c => ↑i ∈ c)).card -- +i の個数
      let neg_count := (cnf.filter (fun c => -↑i ∈ c)).card -- -i の個数
      let count := pos_count + neg_count
      if count > M then
        M := count
        if pos_count >= neg_count then return some ↑i
        else return some (-↑i)
    return none
  ただし，for 文は証明で扱いづらいため，高階関数 List.foldl で書き換える
-/

-- ModeLiteralのループ一回分の処理
def FindMode (cnf : CNF) (acc : Var × Option Literal) (i : Var) : Var × Option Literal :=
  let pos_count := (cnf.filter (fun c => ↑i ∈ c)).card -- +i の個数
  let neg_count := (cnf.filter (fun c => -↑i ∈ c)).card -- -i の個数
  let count := pos_count + neg_count
  if count > acc.1 then
    if pos_count >= neg_count then (count , some (↑i))
    else (count , some (-↑i))
  else acc

def ModeLiteral (cnf : CNF) (n : Var) : Option Literal :=
  ((List.range' 1 n (step := 1)).foldl (FindMode cnf) (0, none)).2

lemma foldl_ModeLiteral {cnf : CNF} {vars : List Var} (acc : Var × Option Literal) (invariant : ∀ l, acc.2 = some l → l.natAbs ∈ num_var_set cnf) :
  ∀ l, (vars.foldl (FindMode cnf) acc).2 = some l → l.natAbs ∈ num_var_set cnf := by
  induction vars generalizing acc with
  | nil =>
    dsimp
    exact invariant
  | cons i tail IH =>
    apply IH
    intro l hl
    unfold FindMode at hl
    dsimp only at hl
    split_ifs at hl
    next _ =>
      simp only[num_var_set, Finset.mem_biUnion, Finset.mem_image]
      dsimp at hl
      have h : 0 < {c ∈ cnf | ↑i ∈ c}.card := by omega
      rw[Finset.card_pos] at h
      obtain ⟨c, hc⟩ := h
      rw [Finset.mem_filter] at hc
      use c
      constructor
      · exact hc.left
      · use ↑i
        rw[Option.some_inj] at hl
        rw[hl] at hc ⊢
        simp only[and_true]
        exact hc.right
    next _ =>
      simp only[num_var_set, Finset.mem_biUnion, Finset.mem_image]
      dsimp at hl
      have h : 0 < {c ∈ cnf | -↑i ∈ c}.card := by omega
      rw[Finset.card_pos] at h
      obtain ⟨c, hc⟩ := h
      rw [Finset.mem_filter] at hc
      use c
      constructor
      · exact hc.left
      · use -↑i
        rw[Option.some_inj] at hl
        rw[hl] at hc ⊢
        simp only[and_true]
        exact hc.right
    next _ =>
      exact invariant l hl

lemma ModeLiteral_in_cnf {cnf : CNF} {l : Literal} (h : ModeLiteral cnf n = some l) : l.natAbs ∈ num_var_set cnf := by
  unfold ModeLiteral at h
  have H : ∀ l, (0, (none : Option Literal)).snd = some l → l.natAbs ∈ num_var_set cnf := by
    intro _ _
    contradiction
  exact foldl_ModeLiteral (0 , none) H l h

-- DPLL のアルゴリズムと停止性の証明
def DPLL (cnf : CNF) (n : Var) : Option Asg :=
  if _h₁ : cnf = ∅ then some []
  else if _h₂ : ∅ ∈ cnf then none
  else
    match _h₃ : UnitLiteral cnf n with
    | some l =>
      match DPLL (simp (substCNF cnf l)) n with
      | some A => some (l :: A)
      | none => none
    | none =>
      match _h₄ : ModeLiteral cnf n with
      | none => none
      | some l =>
        match DPLL (simp (substCNF cnf l)) n with
        | some A => some (l :: A)
        | none =>
          match DPLL (simp (substCNF cnf (-l))) n with
          | some A => some (-l :: A)
          | none => none
  -- 停止性の証明
  termination_by num_var cnf
  decreasing_by
  · simp only [num_var]
    apply Finset.card_lt_card
    rw[Finset.ssubset_iff_subset_ne]
    constructor
    · exact subst_monotone cnf l
    · intro h
      have l_in := UnitLiteral_in_cnf _h₃
      have l_notin := UnitLiteral_notin_subst_cnf cnf l
      rw[h] at l_notin
      contradiction
  · simp only [num_var]
    apply Finset.card_lt_card
    rw[Finset.ssubset_iff_subset_ne]
    constructor
    · exact subst_monotone cnf l
    · intro h
      have l_in := ModeLiteral_in_cnf _h₄
      have l_notin := UnitLiteral_notin_subst_cnf cnf l
      rw [h] at l_notin
      contradiction
  · simp only [num_var]
    apply Finset.card_lt_card
    rw[Finset.ssubset_iff_subset_ne]
    constructor
    · exact subst_monotone cnf (-l)
    · intro h
      have l_in := ModeLiteral_in_cnf _h₄
      have l_notin := UnitLiteral_notin_subst_cnf cnf (-l)
      rw [h, Int.natAbs_neg] at l_notin
      contradiction

-- System.FilePath は パス専用のString（ラップされた String）
def parser (path : System.FilePath) : IO (Var × CNF) := do
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
  match DPLL cnf n with
  | some A =>
      IO.println "SAT"
      let A := A.toArray.qsort (fun a b => a.natAbs < b.natAbs)
      IO.println s!"{A}"
  | none => IO.println "UNSAT"


-- カレントディレクトリ
#eval IO.Process.getCurrentDir

-- 実行テスト
section test

-- (x₁ ∨ x₃ ∨ ¬x₄) ∧ x₄ ∧ (x₂ ∨ ¬x₃)
def test1 : CNF := {{1, 3, -4}, {4}, {2, -3}}
#eval DPLL test1 4

-- (x₁ ∨ x₂ ∨ ¬x₃) ∧ (x₁ ∨ ¬x₂) ∧ ¬x₁ ∧ x₃
def test2 : CNF := {{1, 2, -3}, {1, -2}, {-1}, {3}}
#eval DPLL test2 3

def ex := solver "./final_project/example1.cnf"
#time #eval ex

-- N-Queen Problem
def two_queen := solver "./final_project/N=2.cnf"
def three_queen := solver "./final_project/N=3.cnf"
def four_queen := solver "./final_project/N=4.cnf"
def five_queen := solver "./final_project/N=5.cnf"
def six_queen := solver "./final_project/N=6.cnf"
def seven_queen := solver "./final_project/N=7.cnf"
def eight_queen := solver "./final_project/N=8.cnf"
def nine_queen := solver "./final_project/N=9.cnf"
def ten_queen := solver "./final_project/N=10.cnf"
def eleven_queen := solver "./final_project/N=11.cnf"
def twelve_queen := solver "./final_project/N=12.cnf"
def thirteen_queen := solver "./final_project/N=13.cnf"
def fourteen_queen := solver "./final_project/N=14.cnf"
def fifteen_queen := solver "./final_project/N=15.cnf"

#time #eval two_queen
#time #eval three_queen
#time #eval four_queen
#time #eval five_queen
#time #eval six_queen
#time #eval seven_queen
#time #eval eight_queen
#time #eval nine_queen
#time #eval ten_queen
#time #eval eleven_queen
#time #eval twelve_queen
#time #eval thirteen_queen
#time #eval fourteen_queen
#time #eval fifteen_queen

end test
