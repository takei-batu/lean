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

@[simp] def eval : AExp → (Var → Nat) → Nat
  | (VarExp v), store => store v
  | (NatExp i), _ => i
  | (AddExp e1 e2), store => eval e1 store + eval e2 store

#check eval (AddExp (NatExp 1) (VarExp (mkVar 0))) (fun _: Var => 0)

#eval eval (AddExp (NatExp 1) (VarExp (mkVar 0))) (fun _: Var => 0)

open Finset
#check (({1,2,3} : Finset Nat) ∪ {3,4})

@[simp] def fv : AExp → Finset Var
  | (VarExp v) => { v }
  | (NatExp _) => ∅
  | (AddExp e1 e2) => (fv e1) ∪ (fv e2)

theorem fveval (e : AExp) (store1 store2 : Var → Nat) :
    (∀ x : Var, x ∈ fv e → store1 x = store2 x) →
     eval e store1 = eval e store2 := by
  induction e with
  | VarExp x =>
    intro h
    simp only [eval]
    apply h
    simp [fv]
  | NatExp i =>
    intro h
    simp [eval]
  | AddExp e1 e2 ih1 ih2 =>
    intro h
    simp only [eval]
    apply congr_arg₂
    · apply ih1
      intros x hfv1
      apply h
      simp only [fv, mem_union]
      apply Or.inl
      exact hfv1
    · apply ih2
      intros x hfv2
      apply h
      simp only [fv, mem_union]
      apply Or.inr
      exact hfv2


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
      grind [eval, subst]
  | NatExp i =>
      grind [eval, subst]
  | AddExp e1 e2 ih1 ih2 =>
      grind [eval, subst]

inductive BExp where
  | EqExp : AExp → AExp → BExp
  | NotExp : BExp → BExp
  | AndExp : BExp → BExp → BExp
  deriving Repr, DecidableEq

open BExp

def beval : BExp → (Var → Nat) → Bool
  | (EqExp e1 e2), store => eval e1 store == eval e2 store
  | (NotExp e), store => ! (beval e store)
  | (AndExp e1 e2), store => beval e1 store && beval e2 store

#check beval

inductive Stmt where
 | SkipStmt : Stmt
 | AssignStmt : Var → AExp → Stmt
 | SeqStmt : Stmt → Stmt → Stmt
 | IfStmt : BExp → Stmt → Stmt → Stmt
 | WhileStmt : BExp → Stmt → Stmt
   deriving Repr, DecidableEq

open Stmt

abbrev Store := Var → Nat

def update (st : Store) (x : Var) (v : Nat) : Store :=
  fun y => if y = x then v else st y

inductive Exec : Stmt → Store → Store → Prop where
  | SkipExec (store : Store): Exec SkipStmt store store
  | AssignExec (x : Var) (e : AExp)  (store : Store):
    Exec (AssignStmt x e) store (update store x (eval e store))
  | SeqExec (s1 s2: Stmt) (store1 store2 store3 : Store) :
    Exec s1 store1 store2 → Exec s2 store2 store3 → Exec (SeqStmt s1 s2) store1 store3
  | IfTrueExec (b : BExp) (s1 s2: Stmt) (store1 store2 : Store):
    beval b store1 →
    Exec s1 store1 store2 →
    Exec (IfStmt b s1 s2) store1 store2
  | IfFalseExec (b : BExp) (s1 s2: Stmt) (store1 store2 : Store) :
    ¬ beval b store1 →
    Exec s2 store1 store2 →
    Exec (IfStmt b s1 s2) store1 store2
  | WhileExecFalse (b : BExp) (s : Stmt) (store : Store) :
    ¬ beval b store →
    Exec (WhileStmt b s) store store
  | WhileExecTrue (b : BExp) (s : Stmt) (store1 store2 store3 : Store) :
    beval b store1 →
    Exec s store1 store2 →
    Exec (WhileStmt b s) store2 store3 →
    Exec (WhileStmt b s) store1 store3

#check Exec.SkipExec

theorem exec_deterministic (s : Stmt) (store store1 store2 : Store) :
    Exec s store store1 →
    Exec s store store2 →
    store1 = store2 := by
    intro d
    induction d generalizing store2 with
    | SkipExec store =>
      intro exec2
      cases exec2
      rfl
    | AssignExec x e store =>
      intro exec2
      cases exec2
      rfl
    | SeqExec s1 s2 store11 store12 store13 exec11 exec12 ih1 ih2 =>
      intro exec2
      cases exec2 with
      | SeqExec _ _ _ store' _ exec14 exec15 =>
        have : store12 = store' := ih1 store' exec14
        rw[←this] at exec15
        exact ih2 store2 exec15
    | IfTrueExec b s1 s2 store1' store2' exec1' exec2' ih =>
      intro exec2
      cases exec2 with
      | IfTrueExec =>
        apply ih
        assumption
      | IfFalseExec =>
        contradiction
    | IfFalseExec b s1 s2 store1' store2' exec1' exec2' ih =>
      intro exec2
      cases exec2 with
      | IfTrueExec =>
        contradiction
      | IfFalseExec =>
        apply ih
        assumption
    | WhileExecFalse b s' store' bval =>
      intro exec2
      cases exec2 with
      | WhileExecFalse =>
        rfl
      | WhileExecTrue =>
        contradiction
    | WhileExecTrue b s' store1' store2' store3' bval exec1' exec2' ih1 ih2 =>
      intro exec2
      cases exec2 with
      | WhileExecFalse =>
        contradiction
      | WhileExecTrue b' _ _ store4' _ bval' exec3' exec4' =>
        apply ih2
        have := ih1 store4' exec3'
        rw[this]
        assumption

def semEquiv (s1 s2 : Stmt) :=
  (∀ store1 store2 : Store, Exec s1 store1 store2 ↔ Exec s2 store1 store2)

#check semEquiv

infix:65 " ~ " => semEquiv

theorem sem_equiv_skip1 (s : Stmt) : SeqStmt s SkipStmt ~ s := by
  intro store1 store2
  constructor
  · intro h
    cases h with
    | SeqExec _ _ _ store' _ exec1 exec2 =>
      cases exec2
      assumption
  · intro h
    apply Exec.SeqExec s SkipStmt store1 store2 store2
    · assumption
    · apply Exec.SkipExec

-- Try other semantical equivalence
example (s₁ s₂ s₃ : Stmt) : SeqStmt (SeqStmt s₁ s₂) s₃ ~ SeqStmt s₁ (SeqStmt s₂ s₃) := by
  intro store1 store2
  constructor
  · intro h
    cases h with
    | SeqExec _ _ _ store'' _ exec1 exec2 =>
      cases exec1 with
      | SeqExec _ _ _ store' _ exec11 exec12 =>
        have : Exec (SeqStmt s₂ s₃) store' store2 := by
          apply Exec.SeqExec s₂ s₃ store' store'' store2
          · assumption
          · assumption
        apply Exec.SeqExec s₁ (SeqStmt s₂ s₃) store1 store' store2
        · assumption
        · assumption
  · intro h
    cases h with
    | SeqExec _ _ _ store' _ exec1 exec2 =>
      cases exec2 with
      | SeqExec _ _ _ store'' _ exec11 exec12 =>
        have : Exec (SeqStmt s₁ s₂) store1 store'' := by
          apply Exec.SeqExec s₁ s₂ store1 store' store''
          · assumption
          · assumption
        apply Exec.SeqExec (SeqStmt s₁ s₂) s₃ store1 store'' store2
        · assumption
        · assumption
