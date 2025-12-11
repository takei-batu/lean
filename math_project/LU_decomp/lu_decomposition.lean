import MathProject.Matrix_on_Q
open Matrix

-- LU分解アルゴリズム（doolitleの方法）
def LU_decomp (n : Nat) (A : Matrix n n) : (Matrix n n) × (Matrix n n) := Id.run do
  let A_data := A.data
  let mut L := (identityMatrix n).data -- 単位行列
  let mut U := (zeroMatrix n n).data -- ゼロ行列

  -- U の 1 行目 : u_{1,i} = a_{1,i}
  U := U.set! 0 A_data[0]!

  -- L の 1 列目
  for i in [:n] do
    L := L.set! i (L[i]!.set! 0 (A_data[i]![0]! / U[0]![0]!))

  for i in [1:n] do
    -- U の i 行目（i:行インデックス, j:列インデックス）
    for j in [i:n] do
      -- sum = ∑ l_{i,m} * u_{m,j} (m = 0 to i)
      let mut sum := 0
      for m in [0:i] do
        sum := sum + L[i]![m]! * U[m]![j]!
      -- u_{i,j} = a_{i,j} - sum
      let mut u := A_data[i]![j]! - sum
      U := U.set! i (U[i]!.set! j u)

    -- L の i 列目（j:行インデックス, i:列インデックス）
    for j in [i:n] do
      -- sum = ∑ l_{j,m} * u_{m,i} (m = 0 to i)
      let mut sum := 0
      for m in [0:i] do
        sum := sum + L[j]![m]! * U[m]![i]!
      -- l_{j,i} = sum / u_{i,i}
      let mut l := (A_data[j]![i]! - sum) / U[i]![i]!
      L := L.set! j (L[j]!.set! i l)

  return (Matrix.of L, Matrix.of U)

macro "prove_lu" : tactic => `(tactic| native_decide)

-- 一次方程式を解く関数
def solv_with_LU (n : Nat) (A : Matrix n n) (b : Matrix n 1) : (Matrix n 1) := Id.run do
  let result := LU_decomp n A
  let L := result.1.data
  let U := result.2.data
  let b_data := b.data

  -- L y = b を解く
  let mut y := (zeroMatrix n 1).data -- ゼロ行列
  -- y_{1}
  y := y.set! 0 (y[0]!.set! 0 (b_data[0]![0]! / L[0]![0]!))
  -- y_{k} (k > 1)
  for i in [1:n] do
    let mut sum : Rat := 0
    for k in [0:i] do
      sum := sum + L[i]![k]! * y[k]![0]!
    let mut v := (b_data[i]![0]! - sum) / L[i]![i]!
    y := y.set! i (y[i]!.set! 0 v)

  -- U x = y を解く
  let mut x := (zeroMatrix n 1).data -- ゼロ行列
  let last := n - 1
  -- x_{1}
  x := x.set! last (x[last]!.set! 0 (y[last]![0]! / U[last]![last]!))
  -- x_{k} (k > 1)
  for j in Array.range n |>.reverse do
    -- let mut j := n - i - 1
    let mut sum : Rat := 0
    for k in [j+1:n] do
      sum := sum + U[j]![k]! * x[k]![0]!
    let mut v := (y[j]![0]! - sum) / U[j]![j]!
    x := x.set! j (x[j]!.set! 0 v)

  return Matrix.of x

section test

-- 2行目と3行目は入れ替え済み
def A : Matrix 3 3 := Matrix.of #[
  #[2, 3, 4],
  #[4, 3, 29],
  #[6, 9, 2],
]
#eval A
def result := LU_decomp 3 A
def L := result.1
def U := result.2
#eval L
#eval U

theorem lu_is_correct : A = L • U := by
  prove_lu

def b : Matrix 3 1 := Matrix.of #[
  #[6],
  #[33],
  #[5],
]
#eval b

def x := solv_with_LU 3 A b
#eval x

end test
