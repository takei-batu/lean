import Std
import Mathlib.Data.Finset.Basic

import Mathlib.Logic.Relation

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
  | (VarExp v), state => state v
  | (NatExp i), _ => i
  | (AddExp e1 e2), state => eval e1 state + eval e2 state

#check eval (AddExp (NatExp 1) (VarExp (mkVar 0))) (fun _: Var => 0)

#eval eval (AddExp (NatExp 1) (VarExp (mkVar 0))) (fun _: Var => 0)

open Finset
#check (({1,2,3} : Finset Nat) ∪ {3,4})

@[simp] def fv : AExp → Finset Var
  | (VarExp v) => { v }
  | (NatExp _) => ∅
  | (AddExp e1 e2) => (fv e1) ∪ (fv e2)

theorem fveval (e : AExp) (state1 state2 : Var → Nat) :
    (∀ x : Var, x ∈ fv e → state1 x = state2 x) →
     eval e state1 = eval e state2 := by
  induction e with
  | VarExp x =>
    intro h
    simp [eval]
    apply h
    simp [fv]
  | NatExp i =>
    intro h
    simp [eval]
  | AddExp e1 e2 ih1 ih2 =>
    intro h
    simp [eval]
    apply congr_arg₂
    · apply ih1
      intros x hfv1
      apply h
      simp [fv]
      apply Or.inl
      exact hfv1
    · apply ih2
      intros x hfv2
      apply h
      simp [fv]
      apply Or.inr
      exact hfv2

#check fveval

theorem fveval2 (e : AExp) (state1 state2 : Var → Nat) :
  (∀ x : Var, x ∈ fv e → state1 x = state2 x) →
  eval e state1 = eval e state2 := by
  induction e with
  | VarExp x =>
      intro h
      simp [eval, fv]
      exact h x (by simp [fv])
  | NatExp i =>
      intro h
      simp [eval]
  | AddExp e1 e2 ih1 ih2 =>
      intro h
      simp [eval]
      apply congr_arg₂ Nat.add
      · apply ih1
        intro x hx
        exact h x (by simp [fv, hx])
      · apply ih2
        intro x hx
        exact h x (by simp [fv, hx])

theorem fveval3 (e : AExp) (state1 state2 : Var → Nat) :
  (∀ x : Var, x ∈ fv e → state1 x = state2 x) →
  eval e state1 = eval e state2 := by
  induction e with
  | VarExp x =>
      grind [eval, fv]
  | NatExp i =>
      grind [eval]
  | AddExp e1 e2 ih1 ih2 =>
      grind [eval, fv]

def subst (e : AExp) (x : Var) (e0 : AExp) : AExp :=
    match e with
    | VarExp y => if x = y then e0 else VarExp y
    | NatExp i => NatExp i
    | AddExp e1 e2 =>
        AddExp (subst e1 x e0) (subst e2 x e0)

theorem substEval (e : AExp) (x : Var) (e0 : AExp) (state : Var → Nat) :
    eval (subst e x e0) state = eval e (fun y => if y = x then eval e0 state else state y) := by
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
  | (EqExp e1 e2), state => eval e1 state == eval e2 state
  | (NotExp e), state => ! (beval e state)
  | (AndExp e1 e2), state => beval e1 state && beval e2 state

#check beval

inductive Stmt where
 | SkipStmt : Stmt
 | AssignStmt : Var → AExp → Stmt
 | SeqStmt : Stmt → Stmt → Stmt
 | IfStmt : BExp → Stmt → Stmt → Stmt
 | WhileStmt : BExp → Stmt → Stmt
   deriving Repr, DecidableEq

open Stmt

abbrev State := Var → Nat

def update (st : State) (x : Var) (v : Nat) : State :=
  fun y => if y = x then v else st y

inductive Exec : Stmt → State → State → Prop where
  | SkipExec {state : State}: Exec SkipStmt state state
  | AssignExec (x : Var) (e : AExp)  (state : State):
    Exec (AssignStmt x e) state (update state x (eval e state))
  | IfTrueExec (b : BExp) (s1 s2: Stmt) {state1 state2 : State}:
    beval b state1 = true → Exec s1 state1 state2 →
    Exec (IfStmt b s1 s2) state1 state2
  | SeqExec (s1 s2: Stmt) {state1 state2 state3 : State} :
    Exec s1 state1 state2 → Exec s2 state2 state3 → Exec (SeqStmt s1 s2) state1 state3
  | IfFalseExec (b : BExp) (s1 s2: Stmt) {state1 state2 : State} :
    beval b state1 = false → Exec s2 state1 state2 →
    Exec (IfStmt b s1 s2) state1 state2
  | WhileExecFalse (b : BExp) (s : Stmt) {state : State} :
    beval b state = false → Exec (WhileStmt b s) state state
  | WhileExecTrue (b : BExp) (s : Stmt) {state1 state2 state3 : State} :
    beval b state1 = true → Exec s state1 state2 → Exec (WhileStmt b s) state2 state3 →
    Exec (WhileStmt b s) state1 state3

#check Exec.SkipExec

theorem exec_deterministic (s : Stmt) (state state1 state2 : State) :
    Exec s state state1 →
    Exec s state state2 →
    state1 = state2 := by
    intro d
    induction d generalizing state2 with
    | SkipExec =>
        intro exec2
        cases exec2
        rfl
    | AssignExec x e state =>
        intro exec2
        cases exec2
        apply funext
        simp [update]
    | IfTrueExec b s1 s2 htrue exec1 ih =>
        intro exec2
        cases exec2
        case IfTrueExec exec2 =>
            apply ih
            exact exec2
        case IfFalseExec hfalse _ =>
            grind
    | IfFalseExec b s1 s2 hfalse exec1 ih =>
        intro exec2
        cases exec2
        case IfTrueExec =>
            grind
        case IfFalseExec hfalse _ =>
            grind
    | WhileExecFalse b s hfalse =>
        intro exec2
        cases exec2
        · rfl
        · grind
     | WhileExecTrue b s htrue exec2 exec3 ih1 ih2 =>
        rename_i state11 state12 state13
        intro exec_2
        cases exec_2
        case WhileExecFalse =>
            grind
        case WhileExecTrue state22 htrue_2 exec_2_2 exec_2_3 =>
            have r: state12 = state22 := by
                apply ih1
                exact exec_2_2
            apply ih2
            rw [r]
            exact exec_2_3
    | SeqExec s1 s2 exec11 exec12 ih1 ih2 =>
        rename_i state11 state12 state13
        intro exec2
        cases exec2
        case SeqExec state22 exec21 exec22 =>
            have r: state12 = state22 := by
                apply ih1
                exact exec21
            apply ih2
            rw [r]
            exact exec22


def semEquiv (s1 s2 : Stmt) :=
  (∀ state1 state2 : State, Exec s1 state1 state2 ↔ Exec s2 state1 state2)

#check semEquiv

infix:65 " ~ " => semEquiv

theorem sem_equiv_skip1 (s : Stmt) : SeqStmt s SkipStmt ~ s := by
    rw [semEquiv]
    intro state1 state2
    apply Iff.intro
    · intro exec
      cases exec
      case mp.SeqExec exec1 exec2 =>
        cases exec2
        grind
    · intro exec
      apply Exec.SeqExec
      ·apply exec
      ·apply Exec.SkipExec

abbrev Conf := Stmt × State

inductive ExecOne : Conf → Conf → Prop where
    | AssignExec (x : Var) (e : AExp)  {state : State}:
        ExecOne (AssignStmt x e, state) (SkipStmt, update state x (eval e state))
    | SeqExec1 (s : Stmt) {state : State} :
        ExecOne (SeqStmt SkipStmt s, state) (s, state)
    | SeqExec2 (s1 s1' s2 : Stmt) {state state': State} :
        ExecOne (s1, state) (s1', state') →
        ExecOne (SeqStmt s1 s2, state) (SeqStmt s1' s2, state')
    | IfTrueExec (b : BExp) (s1 s2: Stmt) {state : State}:
        beval b state = true →
        ExecOne (IfStmt b s1 s2, state) (s1, state)
    | IfFalseExec (b : BExp) (s1 s2: Stmt) {state : State}:
        beval b state = false →
        ExecOne (IfStmt b s1 s2, state) (s2, state)
    | WhileExec (b : BExp) (s : Stmt) {state : State} :
    ExecOne (WhileStmt b s, state)
        (IfStmt b (SeqStmt s (WhileStmt b s)) SkipStmt, state)


lemma small_seq' (s : Stmt) (c1 c2 : Conf) :
    Relation.ReflTransGen ExecOne c1 c2
    → Relation.ReflTransGen ExecOne (SeqStmt c1.1 s, c1.2) (SeqStmt c2.1 s, c2.2) := by
  sorry

lemma small_seq (s s1 s2 : Stmt) (state1 state2 : State) :
    Relation.ReflTransGen ExecOne (s1, state1) (s2, state2)
    → Relation.ReflTransGen ExecOne (SeqStmt s1 s, state1) (SeqStmt s2 s, state2) := by
  sorry

lemma big_small (s : Stmt) (state state' : State) : Exec s state state' →
    Relation.ReflTransGen ExecOne (s, state) (SkipStmt, state') := by
    intro exec_big
    induction exec_big with
    | SkipExec =>
        apply Relation.ReflTransGen.refl
    | AssignExec x e state =>
        apply Relation.ReflTransGen.single
        apply ExecOne.AssignExec
    | SeqExec s1 s2 exec1 exec2 ih1 ih2 =>
      sorry
    | IfTrueExec b s1 s2 htrue exec1 ih =>
        apply Relation.ReflTransGen.head
        · apply ExecOne.IfTrueExec
          exact htrue
        · apply ih
    | IfFalseExec b s1 s2 hfalse exec1 ih =>
        apply Relation.ReflTransGen.head
        · apply ExecOne.IfFalseExec
          exact hfalse
        · apply ih
    | WhileExecFalse b s hfalse =>
      sorry
    | WhileExecTrue b s htrue =>
      sorry

def RelIter (R : α → α → Prop) : Nat → α → α → Prop
| 0     => Eq
| n + 1 => Relation.Comp R (RelIter R n)

#check Relation.Comp


lemma seq_small (s1 s2 : Stmt) (state1 state2 : State) (n : Nat) :
    RelIter ExecOne n (SeqStmt s1 s2, state1) (SkipStmt, state2) →
    ∃ l m state, RelIter ExecOne l (s1, state1) (SkipStmt, state) ∧
                 RelIter ExecOne m (s2, state) (SkipStmt, state2) ∧
                 n = l + m + 1:= by
    induction n generalizing s1 s2 state1 state2 with
    | zero  =>
        intro h
        simp[RelIter] at h
    | succ n ih =>
        intro h
        simp only [RelIter, Relation.Comp, Prod.exists] at h
        obtain ⟨s', state', r1,  r2⟩  := h
        cases r1 with
        | SeqExec1 =>
            have f1 : RelIter ExecOne 0 (SkipStmt, state1) (SkipStmt, state1) :=
                by simp[RelIter]
            have f2 : n+1 = 0+n+1 := by simp
            exact ⟨0, n, state1, f1, r2, f2⟩
        | SeqExec2 =>
            sorry


lemma skip_not (n : Nat) (state state' : State) :
     ¬ RelIter ExecOne (n+1) (SkipStmt, state) (SkipStmt, state') := by
    sorry


lemma skip_0 (n : Nat) (state state' : State) :
    RelIter ExecOne n (SkipStmt, state) (SkipStmt, state') → n = 0 ∧ state' = state := by
    cases n with
    | zero =>
        simp [RelIter]
        tauto
    | succ n' =>
        intro h
        exfalso
        exact skip_not n' state state' h

lemma small_big (n : Nat) (s : Stmt) (state state' : State) :
    RelIter ExecOne n (s, state) (SkipStmt, state') →
    Exec s state state' := by
    induction n using Nat.strong_induction_on generalizing s state state' with
    | h n ih =>
        cases n with
        | zero =>
           simp only [RelIter, Prod.mk.injEq, and_imp]
           intros h1 h2
           simp only [h1, h2]
           apply Exec.SkipExec
        | succ n' =>
            cases s with
            | SkipStmt =>
                intro h
                exfalso
                exact skip_not n' state state' h
            | AssignStmt x e =>
                sorry
            | SeqStmt s1 s2 =>
                intro h
                have f1 : ∃ l m state'', RelIter ExecOne l (s1, state) (SkipStmt, state'') ∧
                 RelIter ExecOne m (s2, state'') (SkipStmt, state') ∧
                 n' + 1 = l + m + 1 := by
                    apply seq_small
                    exact h
                obtain ⟨l, m, state'', r1, r2, _⟩ := f1
                sorry
            | IfStmt b s1 s2 =>
                sorry
            | WhileStmt b s =>
                intro h
                simp only [RelIter, Relation.Comp, Prod.exists] at h
                obtain ⟨s', state'', r1, r2⟩ := h
                sorry
