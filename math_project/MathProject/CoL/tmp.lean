import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Sort -- Finset を出力するため
-- import Mathlib.Order.Hom.Basic
-- import Mathlib.Order.Interval.Set.Basic

inductive Player where
  | machine
  | environment
-- deriving Repr

instance : Repr Player where
  reprPrec p _ :=
    match p with
    | Player.machine     => f!"⊤"
    | Player.environment => f!"⊥"

notation "⊤"   => Player.machine
notation "⊥"   => Player.environment

structure CM where
  player : Player
  move : String
-- deriving Repr

instance : Repr CM where
  reprPrec p _ :=
    f!"{repr p.player}{p.move}"

abbrev Run := Nat -> CM
abbrev Position (n : Nat) := Fin n -> CM

instance : HAppend (Position m) (Position n) (Position (m + n)) where
  hAppend Φ Ψ := fun (i : Fin (m + n)) =>
  if h : i < m then Φ ⟨i, h⟩
  else Ψ ⟨(i.val - m), (by omega)⟩

instance : HAppend (Position n) Run Run where
  hAppend Φ Γ := fun (i : Nat) =>
    if h : i < n then Φ ⟨i, h⟩
    else Γ (i - n)

def Γ₀ : Run := fun n =>
  if n % 2 == 0 then ⟨⊤, toString n⟩
  else ⟨⊥, toString n⟩

def Φ₀ : Position 2 := fun i =>
  match i with
  | 0 => ⟨⊥, toString 0⟩
  | 1 => ⟨⊤, toString 1⟩

def Φ₁ : Position 3 := fun i =>
  match i with
  | 0 => ⟨⊥, toString 0⟩
  | 1 => ⟨⊥, toString 1⟩
  | 2 => ⟨⊤, toString 2⟩

#eval List.ofFn Φ₀
#eval List.ofFn Φ₀

#eval List.ofFn Φ₁

#eval (List.range 10).map Γ₀

#eval List.ofFn (Φ₀ ++ Φ₁)
-- #eval (List.ofFn Φ₀Φ₁).zipIdx

#eval (List.range 10).map (Φ₀ ++ Γ₀)
-- #eval ((List.range 10).map Φ₀Γ₀).zipIdx

-- class SeqFilter (α : Type) where
--   toSet : (α → CM) → (CM → Bool) → Set α

-- instance : SeqFilter (Fin n) where
--   toSet pos mfilter := {i | mfilter (pos i) = true}

-- instance : SeqFilter Nat where
--   toSet run mfilter := {i | mfilter (run i) = true}

-- #check (SeqFilter.toSet Φ₁ GreenMove)
-- #check (SeqFilter.toSet Φ₁ RedMove)

def pos_idx (pos : Position n) (mfilter : CM → Bool) : Finset Nat :=
  ((Finset.univ : Finset (Fin n)).filter (fun i => mfilter (pos i))).image Fin.val

def GreenMove (cm : CM) : Bool :=
  match cm.player with
  | .machine => true
  | .environment => false

def RedMove (cm : CM) : Bool :=
  match cm.player with
  | .machine => false
  | .environment => true

#eval pos_idx Φ₁ GreenMove
#eval pos_idx Φ₁ RedMove

-- #check Finset.orderIsoOfFin
