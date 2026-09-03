-- import Mathlib.Data.Set.Basic
import MathProject.CoL.move
import MathProject.CoL.run
import Mathlib.Data.Finset.Basic

def IsPrefixofRun (Φ : Position) : Run → Prop
  -- | .infinite Γ => ∃ (Δ : InfiniteRun), Φ ++ₛ Δ = Γ
  | .infinite Γ => Φ = Γ.take Φ.length
  | .finite Ψ => Φ <+: Ψ

infixl:50 " ≼ " => IsPrefixofRun

def toSetRun (S : Set Position) : Set Run := { Run.finite Φ | Φ ∈ S}

def IsPrefixClosed (S : Set Run) : Prop :=
  ∀ run ∈ S, ∀ Φ : Position, Φ ≼ run → Run.finite Φ ∈ S

def IsLimitClosed (S : Set Position) : Run → Prop
  | .finite Φ => Φ ∈ S
  | .infinite Γ => ∀ n : Nat, Γ.take n ∈ S

-- def LimitClosure (S : Set Position) : Set Run := { run : Run | IsLimitClosed S run}

structure Game where
  Lp : Set Position
  Lp_proper : Lp.Nonempty ∧ IsPrefixClosed (toSetRun Lp)
  Wn : (run : Run) → Option Player
  Wn_proper : ∀ run : Run, ¬ IsLimitClosed Lp run → Wn run = none

-- def IsProper (G : Game) : Prop :=
--   G.Lp.Nonempty ∧
--   IsPrefixClosed (toSetRun G.Lp) ∧
--   ∀ run : Run, ¬ IsLimitClosed G.Lp run → G.Wn run = none

-- def IsIllegal (G : Game) (run : Run) (p : Player) : Prop :=
--   ∃ Φ Ψ : Position, ∃ h : Φ.length < Ψ.length,
--   Φ <+: Ψ ∧ Ψ ≼ run ∧ Φ ∈ G.Lp ∧ ¬ Ψ ∈ G.Lp ∧
--   (∀ Θ, Θ <+: Ψ → Φ.length < Θ.length → ¬ Θ ∈ G.Lp) ∧
--   (Ψ[Φ.length]'(h)).player = p

/-
  run is p-illegal:
  the run is illegal,
  there exists a legal run Φ and p-move λ s.t. Φ ++ [λ] is a initial segment of run and illegal.
-/
def IsIllegal (G : Game) (run : Run) (p : Player) : Prop :=
  ¬ IsLimitClosed G.Lp run ∧
  ∃ (Φ : Position) («λ» : CM),
  Φ ∈ G.Lp ∧
  (Φ ++ [«λ»]) ≼ run ∧
  (Φ ++ [«λ»]) ∉ G.Lp ∧
  «λ».player = p

def IsWonby (G : Game) (run : Run) (p : Player) : Prop := G.Wn run = some p ∨ IsIllegal G run pᶜ

structure Universe where
  Dm : Type u
  Dn : Nat -> Dm

def ArithmeticUniv : Universe := {
  Dm := Nat
  Dn := fun n => n
}

inductive Variable where
  | var (n : Nat)

abbrev valuation (Vr : Set Variable) (Dm : Type u) := Vr → Dm

structure GameFrame where
  U : Universe
  Vr : Set Variable
  G : valuation Vr U.Dm → Game

structure Function where
  U : Universe
  Vr : Set Variable
  f : valuation Vr U.Dm → U.Dm
