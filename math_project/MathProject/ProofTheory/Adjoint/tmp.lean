class inductive MyMem {α : Type} (a : α) : List α → Type where
  | head (as : List α)   : MyMem a (a :: as)
  | tail (b : α) (as : List α) : MyMem a as → MyMem a (b :: as)
