structure Signature where
  Func : Nat → Type
  Rel  : Nat → Type

def DefaultSig : Signature := {
  Func := fun _ => String  -- 任意のアリティ n に対して、文字列で関数記号を作れる
  Rel := fun _ => String  -- 任意のアリティ n に対して、文字列で述語記号を作れる
}

inductive Term (𝒮 : Signature) where
| bvar (idx : Nat) : Term 𝒮 -- bounded variable
| fvar (name : String) : Term 𝒮 -- free variable
| func {n : Nat} (f : 𝒮.Func n) (args : Fin n → Term 𝒮) : Term 𝒮 -- n-ary function

namespace Term

-- bounded variables : #0, #1, ...
scoped notation:max "#" idx => Term.bvar idx

-- free variable : $"x", $"y", ...
scoped notation:max "$" name => Term.fvar name

/-- lift :
  · bounded variable => incrementing by delta.
  · free variable => do nothing.
  · function => inductively applying to args of func.
-/
def lift {𝒮 : Signature} (cutoff : Nat) (delta : Nat) : Term 𝒮 → Term 𝒮
  | bvar i =>
      if i ≥ cutoff then
        bvar (i + delta)
      else
        bvar i
  | fvar x => fvar x
  | func f args =>
      func f (fun i => lift cutoff delta (args i))

/-- instantiation for a bounded variable :
  · bounded variable => replacing it with t.
  · free variable => do nothing.
  · function => inductively applying to args of func.
-/
def inst {𝒮 : Signature} (idx : Nat) (t : Term 𝒮) : Term 𝒮 → Term 𝒮
  | bvar i =>
      if i == idx then
        t
      else if i > idx then
        bvar (i - 1)
      else
        bvar i
  | fvar x => fvar x
  | func f args =>
      func f (fun i => inst idx t (args i))

/-- substitution for a free variable :
  · bounded variable => do nothing.
  · free variable => replacing it with a.
  · function => inductively applying to args of func.
-/
def subst {𝒮 : Signature} (name : String) (a : Term 𝒮) : Term 𝒮 → Term 𝒮
  | bvar i => bvar i
  | fvar x =>
      if x == name then
        a
      else
        fvar x
  | func f args =>
      func f (fun i => subst name a (args i))

def has_fvar {𝒮 : Signature} (x : String) : Term 𝒮 → Bool
  | bvar _ => false
  | fvar y => x == y
  | func (n := n) _ args => (List.finRange n).any (fun i => has_fvar x (args i))

end Term
