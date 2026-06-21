import Lean

namespace prop

inductive Formula where
  | atom : String → Formula -- atomic formula
  | bot : Formula -- ⊥
  | imp : Formula → Formula → Formula -- A → B
  -- | not : Formula → Formula -- ¬A
  -- | and : Formula → Formula → Formula -- A ∧ B
  -- | or : Formula → Formula → Formula -- A ∨ B
deriving Repr, DecidableEq

notation "⊥"   => Formula.bot

def Formula.not (A : Formula) : Formula := A.imp ⊥
def Formula.or (A B : Formula) : Formula := (A.not).imp B
def Formula.and (A B : Formula) : Formula := .not (.or (.not A) (.not B))
def Formula.iff (A B : Formula) : Formula := .not (.and (.imp A B) (.imp B A))

end prop

namespace fol

structure Signature where
  Func : Type            -- 関数記号の型
  FuncArity : Func → Nat -- 各関数記号のアリティ
  Pred : Type            -- 述語記号の型
  PredArity : Pred → Nat -- 各述語記号のアリティ

inductive Term (S : Signature) where
  | var : Nat → Term S
  | app : (f : S.Func) → (Fin (S.FuncArity f) → Term S) → Term S

inductive Formula (S : Signature) where
  | atom : (R : S.Pred) → (Fin (S.PredArity R) → Term S) → Formula S
  | bot : Formula S
  | imp : Formula S → Formula S → Formula S
  | forall_ : Formula S → Formula S

def Formula.not (A : Formula S) : Formula S := .imp A .bot
def Formula.or (A B : Formula S) : Formula S := .imp (.not A) B
def Formula.and (A B : Formula S) : Formula S := .not (.or (.not A) (.not B))
def Formula.iff (A B : Formula S) : Formula S := .not (.and (.imp A B) (.imp B A))
def Formula.exist_ (A : Formula S) : Formula S := .not (.forall_ (.not A))

end fol
