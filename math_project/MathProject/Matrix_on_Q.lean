-- 文字列のパディング（右埋め）
def padRight (s : String) (width : Nat) : String := s ++ "".pushn ' ' (width - s.length)

-- ℚ上の行列の定義
structure Matrix (m n :Nat) where
  rows : Nat := m
  cols : Nat := n
  data : Array (Array Rat)
  -- size : Nat := data.size
  -- deriving Repr
  deriving DecidableEq

instance : Repr (Matrix m n) where
  reprPrec M _ :=
    let data := M.data
    -- 1. 全要素を文字列に変換
    let strData := data.map (fun row => row.map toString)

    -- 2. 最も長い文字列の長さを探す（列揃えのため）
    let maxLen := strData.foldl (fun acc row =>
      row.foldl (fun acc2 cell => max acc2 cell.length) acc
    ) 0
    let colWidth := maxLen + 2 -- 少し余白を持たせる

    -- 3. 各行を整形して結合
    let formattedRows := strData.map fun rowStrArray =>
      "| " ++ (rowStrArray.foldl (fun acc cell => acc ++ padRight cell colWidth) "") ++ "|"

    let gridStr := String.intercalate "\n" formattedRows.toList

    -- 4. 最終的な出力フォーマット
    Std.Format.text s!"Matrix ({M.rows}×{M.cols}):\n{gridStr}"

namespace Matrix
  -- data だけ渡せば Matrix を作ってくれる関数
  def of (data : Array (Array Rat)) : Matrix m n :=
    { rows := m, cols := n, data := data }

  -- 零行列
  def zeroMatrix (m n : Nat) : Matrix m n := {
    rows := m
    cols := n
    data := (Array.range m).map (fun _ => Array.replicate n 0)
  }

  -- 単位行列
  def identityMatrix (n : Nat) : Matrix n n := {
    rows := n
    cols := n
    data := (Array.range n).map fun i => (Array.range n).map fun j => if i == j then 1 else 0
  }

  -- 行列の和
  def Mat_Add (A B : Matrix m n) : Matrix m n := Id.run do
    let mut data := (zeroMatrix m n).data
    -- (Array.range m).map (fun _ => Array.replicate n 0)
    for i in [:m] do
      for j in [:n] do
        let val := A.data[i]![j]! + B.data[i]![j]!
        data := data.set! i (data[i]!.set! j val)
    return { rows := m, cols := n, data := data }

  -- [+] 加算
  instance : Add (Matrix m n) where
    add := Matrix.Mat_Add

  -- 行列の差
  def Mat_Sub (A B : Matrix m n) : Matrix m n := Id.run do
    let mut data := (zeroMatrix m n).data
    -- (Array.range m).map (fun _ => Array.replicate n 0)
    for i in [:m] do
      for j in [:n] do
        let val := A.data[i]![j]! - B.data[i]![j]!
        data := data.set! i (data[i]!.set! j val)
    return { rows := m, cols := n, data := data }

  -- [-] 減算
  instance : Sub (Matrix m n) where
    sub := Matrix.Mat_Sub

  -- 行列の積
  def Mat_Mul (A : Matrix l m) (B : Matrix m n) : Matrix l n := Id.run do
    let mut data := (zeroMatrix l n).data
    -- (Array.range l).map (fun _ => Array.replicate n 0)
    for i in [:l] do
      for j in [:n] do
        let mut val := 0
        for k in [:m] do
          val := val + A.data[i]![k]! * B.data[k]![j]!
        data := data.set! i (data[i]!.set! j val)
    return { rows := l, cols := n, data := data }

  -- [•]乗算
  instance : HSMul (Matrix l m) (Matrix m n) (Matrix l n) where
    hSMul := Matrix.Mat_Mul

end Matrix
