import Std
import Mathlib.Data.Finset.Basic

inductive Var where
  | mkVar : Nat → Var
  deriving Repr, DecidableEq

open Var

inductive AExp where
  | VarExp : Var → AExp
  | NatExp : Nat → AExp
  | AddExp : AExp → AExp → AExp
  deriving Repr, DecidableEq

open AExp

def eval : AExp → (Var → Nat) → Nat
  | VarExp v, store => store v
  | NatExp i, _ => i
  | AddExp e1 e2, store => eval e1 store + eval e2 store

#check eval (AddExp (NatExp 1) (VarExp (mkVar 0))) (fun _: Var => 0)

#eval eval (AddExp (NatExp 1) (VarExp (mkVar 0))) (fun _: Var => 0)

open Finset
#check (({1,2,3} : Finset Nat) ∪ {3,4})

def fv : AExp → Finset Var
  | VarExp v => { v }
  | NatExp _ => ∅
  | AddExp e1 e2 => (fv e1) ∪ (fv e2)

theorem fv_eval (e : AExp) (store1 store2 : Var → Nat) :
  (∀ x : Var, x ∈ fv e → store1 x = store2 x) →
  eval e store1 = eval e store2 := by
  induction e with
  | VarExp x =>
    intro h
    simp only[eval]
    simp[fv] at h
    assumption
  | NatExp i =>
    intro h
    simp only[eval]
  | AddExp e1 e2 ih1 ih2 =>
    intro h
    simp only[eval]
    simp only [fv, mem_union] at h
    have : (∀ x ∈ fv e1, store1 x = store2 x) := by
      intro x h₁
      exact h x (Or.inl h₁)
    have eq1 := ih1 this
    have : (∀ x ∈ fv e2, store1 x = store2 x) := by
      intro x h₂
      exact h x (Or.inr h₂)
    have eq2 := ih2 this
    rw[eq1, eq2]

def subst (e : AExp) (x : Var) (e0 : AExp) : AExp :=
    match e with
    | VarExp y => if x = y then e0 else VarExp y
    | NatExp i => NatExp i
    | AddExp e1 e2 =>
        AddExp (subst e1 x e0) (subst e2 x e0)

theorem subst_eval (e : AExp) (x : Var) (e0 : AExp) (store : Var → Nat) :
    eval (subst e x e0) store = eval e (fun y => if y = x then eval e0 store else store y) := by
  induction e with
  | VarExp x =>
    simp only[eval,subst]
    split_ifs
    next _ => rfl
    next h₁ h₂ => rw[h₁] at h₂; contradiction
    next h₁ h₂ => rw[h₂] at h₁; contradiction
    next _ => rfl
  | NatExp i => rfl
  | AddExp e1 e2 ih1 ih2 =>
    simp only[eval,subst]
    rw[← ih1, ←ih2]
