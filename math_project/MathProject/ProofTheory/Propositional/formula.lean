inductive Formula where
  | atom : String → Formula -- atomic formula
  | bot : Formula
  | top : Formula
  | imp : Formula → Formula → Formula
  -- | not : Formula → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
deriving Repr, DecidableEq


namespace Formula

def not (A : Formula) : Formula := A.imp bot
def iff (A B : Formula) : Formula := .not (.and (.imp A B) (.imp B A))

end Formula

local notation "⊤"   => Formula.top
local notation "⊥"   => Formula.bot
