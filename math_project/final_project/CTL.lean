import Mathlib
set_option linter.style.longLine false

abbrev AP := String
abbrev State := Nat

inductive Formula where
  -- | bot : Formula -- ⊥
  | top : Formula -- ⊤
  | atom (name : AP) : Formula -- atomic formula
  | not : Formula → Formula -- ¬p
  | and : Formula → Formula → Formula -- p ∧ q
  | or : Formula → Formula → Formula -- p ∨ q
  | imp : Formula → Formula → Formula -- p ⇒ q
  -- | iff : Formula → Formula → Formula -- p ↔ p
  | AX : Formula → Formula -- AX p
  | EX : Formula → Formula -- EX p
  | AG : Formula → Formula -- AG p
  | EG : Formula → Formula -- EG p
  | AF : Formula → Formula -- AF p
  | EF : Formula → Formula -- EF p
  | AU : Formula → Formula → Formula -- A (p U q)
  | EU : Formula → Formula → Formula -- E (p U q)
deriving Repr, DecidableEq

structure TransitionSystem where
  states : Finset State
  trans : Finset (State × State)
  label : State → Finset Formula
-- deriving Repr

abbrev TS := TransitionSystem

-- {s | s → s'}
def next (t : TS) (s : State) : Finset State :=
  t.trans.filter (fun edge => edge.1 == s) |>.image (fun edge => edge.2)

-- Greatest Fixed Point
partial def gfp (step : Finset State → Finset State) (S : Finset State) : Finset State :=
  let fix := S ∩ step S
  if fix == S then S else gfp step fix

-- Least Fixed Point
partial def lfp (step : Finset State → Finset State) (S : Finset State) : Finset State :=
  let fix := S ∪ step S
  if fix == S then S else lfp step fix

-- s ⊨ ϕ となる s の集合を返す
def model (t : TS) (f : Formula) : Finset State :=
  open Classical in
  match f with
  | .top => t.states -- for all states
  | .atom p => t.states.filter (fun s => (.atom p) ∈ t.label s) -- {s | p ∈ L(s)}
  | .not ϕ => t.states \ (model t ϕ) -- {s | s ⊭ ϕ }
  | .and ϕ ψ => (model t ϕ) ∩ (model t ψ) -- {s | s ⊨ ϕ ∧ s ⊨ ψ}
  | .or ϕ ψ => (model t ϕ) ∪ (model t ψ) -- {s | s ⊨ ϕ ∨ s ⊨ ψ}
  | .imp ϕ ψ => (t.states \ (model t ϕ)) ∪ (model t ψ) -- {s | s ⊨ ϕ ⇒ s ⊨ ψ}
  | .AX ϕ => t.states.filter (fun s => next t s ⊆ model t ϕ) -- {s | ∀ s', s → s' ⇒ s' ⊨ ϕ} = {s | (next t s) ⊆ model t ϕ}
  | .EX ϕ => t.states.filter (fun s => (next t s ∩ model t ϕ).Nonempty) -- {s | ∃ s', s → s' ∧ s' ⊨ ϕ} = {s | (next t s) ∩ model t ϕ ≠ ∅}
  | .AG ϕ => gfp (fun S => t.states.filter (fun s => next t s ⊆ S)) (model t ϕ) -- AG ϕ ≡ ϕ ∧ AX (AG ϕ)
  | .EG ϕ => gfp (fun S => t.states.filter (fun s => (next t s ∩ S).Nonempty)) (model t ϕ) -- EG ϕ ≡ ϕ ∧ EX (EG ϕ)
  | .AF ϕ => lfp (fun S => t.states.filter (fun s => next t s ⊆ S)) (model t ϕ) -- AF ϕ ≡ ϕ ∨ AX (AF ϕ)
  | .EF ϕ => lfp (fun S => t.states.filter (fun s => (next t s ∩ S).Nonempty)) (model t ϕ) -- EF ϕ ≡ ϕ ∨ EX (EF ϕ)
  | .AU ϕ ψ => lfp (fun S => (model t ϕ).filter (fun s => next t s ⊆ S)) (model t ψ) -- A (ϕ U ψ) ≡ ψ ∧ AX (A (ϕ U ψ))
  | .EU ϕ ψ => lfp (fun S => (model t ϕ).filter (fun s => (next t s ∩ S).Nonempty)) (model t ψ) -- E (ϕ U ψ) ≡ ψ ∨ EX (E (ϕ U ψ))

-- Mutual Exclusion
def ME : TS :=
  {
    states := {0, 1, 2, 3, 4, 5 ,6 , 7, 8},
    trans := {(0,1),(1,2),(2,3),(1,4),(4,3), (4,0), (3,5), (0,5),(5,6),(6,7), (5,8), (8,7), (8,0), (7,1)},
    label := fun s : State => match s with
    | 0 => {.atom "n₁", .atom "n₂"}
    | 1 => {.atom "t₁", .atom "n₂"}
    | 2 => {.atom "t₁", .atom "t₂"}
    | 3 => {.atom "c₁", .atom "t₂"}
    | 4 => {.atom "c₁", .atom "n₂"}
    | 5 => {.atom "n₁", .atom "t₂"}
    | 6 => {.atom "t₁", .atom "t₂"}
    | 7 => {.atom "t₁", .atom "c₂"}
    | 8 => {.atom "n₁", .atom "c₂"}
    | _ => ∅
  }

def ϕ₁ : Formula := .EU (.not (.atom "c₂")) (.atom "c₁")
def ϕ₂ : Formula := .AG (.imp (.atom "t₁") (.AF (.atom "c₁)")))
def ϕ₃ : Formula := .EF (.and (.atom "c₁") (.atom "c₂"))
def ϕ₄ : Formula := .AG (.EF (.and (.atom "n₁") (.atom "n₂")))
def ϕ₅ : Formula := .EF (.atom "c₁")

#eval model ME ϕ₁
#eval model ME ϕ₂
#eval model ME ϕ₃
#eval model ME ϕ₄
#eval model ME ϕ₅
