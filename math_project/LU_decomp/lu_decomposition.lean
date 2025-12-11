import MathProject.Matrix_on_Q
open Matrix

-- LU分解アルゴリズム（doolitleの方法）
def LU_decomp (n : Nat) (A : Matrix n n) : (Matrix n n) × (Matrix n n) := Id.run do
  -- let n := A.size -- A のサイズ
  -- let mut L : Matrix := (Array.range n).map (fun i => (Array.range n).map (fun j => if i == j then 1 else 0)) -- 単位行列
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

section test

def A : Matrix 3 3 := Matrix.of #[
  #[2, -1, -2],
  #[-4, 6, 3],
  #[-4, -2, 8]
]
#eval A
def result := LU_decomp 3 A
def L := result.1
def U := result.2
#eval L
#eval U

theorem lu_is_correct : A = L • U := by
  prove_lu

end test
