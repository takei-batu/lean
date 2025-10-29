#check And

#check Or

#check Not

def Implies (p q : Prop) : Prop := p → q
#check Implies

variable (p q r : Prop)
#check And p q
#check Or (And p q) r
#check And (Implies p q) (Implies q p)

structure Proof (p : Prop) : Type where
  proof : p
#check Proof

axiom and_commute (p q : Prop) : Proof (Implies (And p q) (And p q))
#check and_commute p q
#check (and_commute p q).proof

-- MP
axiom modus_ponens (p q : Prop) : Proof (Implies p q) → Proof p → Proof q

-- DR
axiom implies_intro (p q : Prop) : (Proof p → Proof q) → Proof (Implies p q)
