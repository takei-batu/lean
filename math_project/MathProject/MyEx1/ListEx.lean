
variable {α : Type}

def rev : List α → List α
| [] => []
| x :: xs => rev xs ++ [x]

theorem rev_distrib (xs ys: List α) :
  rev (xs ++ ys) = rev ys ++ rev xs := by
  induction xs with
  | nil => simp[rev]
  | cons x xs ih =>
    simp[rev]
    rw[ih]
    rw[List.append_assoc]

theorem rev_rev (xs : List α) :
  rev (rev xs) = xs := by
  induction xs with
  | nil => simp[rev]
  | cons x xs ih =>
    simp[rev]
    rw[rev_distrib]
    simp[rev]
    assumption


def interperse (x : α ): List α → List α
  | [] => []
  | [y] => [y]
  | y0 :: y1 :: ys => y0 :: x :: interperse x (y1 :: ys)

variable {β  : Type}

-- Use fun_induction
theorem interperse_map (x : α ) (ys : List α) (f : α → β ) :
  List.map f (interperse x ys) = interperse (f x) (List.map f ys) := by
  fun_induction interperse x ys with
  | case1 => simp[interperse]
  | case2 => simp[interperse]
  | case3 _ _ _ h =>
    simp[interperse]
    rw[h]
    rfl
