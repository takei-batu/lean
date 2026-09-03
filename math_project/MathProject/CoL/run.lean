import Mathlib.Data.Stream.Defs
import MathProject.CoL.move

inductive Run where
  | infinite (Γ : Stream' CM) : Run
  | finite (Φ : List CM) : Run

abbrev InfiniteRun := Stream' CM
abbrev Position := List CM

def Φ₀ : Position := [
  ⟨⊥, toString 0⟩,
  ⟨⊤, toString 1⟩,
]

def Φ₁ : Position := [
  ⟨⊥, toString 0⟩,
  ⟨⊥, toString 1⟩,
  ⟨⊤, toString 2⟩,
]

#eval Φ₀
#eval Φ₁
#eval Φ₀ ++ Φ₁

def Γ₀ : InfiniteRun := fun n =>
  if n % 2 == 0 then ⟨⊤, toString n⟩
  else ⟨⊥, toString n⟩

#eval Γ₀.take 0
#eval Γ₀.take 1
#eval Γ₀.take 2
#eval Γ₀.take 3
#eval Γ₀.take 4
