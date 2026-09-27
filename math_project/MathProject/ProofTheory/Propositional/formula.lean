inductive Formula where
  | atom : String → Formula -- atomic formula
  | bot : Formula
  | imp : Formula → Formula → Formula
  -- | not : Formula → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
deriving Repr, DecidableEq

local notation "⊥"   => Formula.bot

namespace Formula

def not (A : Formula) : Formula := A.imp ⊥
def top  : Formula := .not ⊥
-- def or (A B : Formula) : Formula := (A.not).imp B
-- def and (A B : Formula) : Formula := .not (.or (.not A) (.not B))
def iff (A B : Formula) : Formula := .not (.and (.imp A B) (.imp B A))

end Formula

local notation "⊤"   => Formula.top
