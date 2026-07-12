import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import MathProject.MyEx1.DFA
import MathProject.MyEx1.NFA

#check DFA.hat
#check NFA.hat

variable {α β : Type} [DecidableEq β]

def step (transition : β → α → Finset β) (qs : Finset β) (a : α) : Finset β :=
  qs.biUnion (fun q => transition q a)

variable [Fintype α] [Fintype β]

#check Finset.filter

#check DFA α (Finset β)

#check (Finset.univ : Finset (Finset β))

-- Correct the following definition.
def NFAToDFA (nfa : NFA α β) : DFA α (Finset β) :=
  DFA.mk {nfa.initial}
    Finset.univ
     (step nfa.transition)

#check NFA.accept

-- Create lemmas to prove the following theorem.

theorem correct_comnplement (nfa : NFA α β) (xs : List α) :
    DFA.accept (NFAToDFA nfa) xs ↔ NFA.accept nfa xs := by
    sorry
