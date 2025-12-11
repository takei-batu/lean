/- Simple Type Theory -/

-- Define some constants.
def m : Nat := 1       -- m is a natural number
def n : Nat := 0
def b1 : Bool := true  -- b1 is a Boolean
def b2 : Bool := false

-- Check their types.
#check m
#check n
#check n + 0
#check m * (n + 0)
#check b1
#check (0, 0)
#check false
#check False

-- "&&" is the Boolean and
#check b1 && b2

-- Boolean or
#check b1 || b2

-- Boolean "true"/"false"
#check true
#check false

-- Evaluate
#eval 5 * 4
#eval m + 2
#eval b1 && b2

/- Types as objects -/
#check Nat
#check Bool
#check Nat → Bool
#check Nat × Bool
#check Nat → Nat
#check Nat × Nat → Nat
#check Nat →  Nat → Nat
#check Nat →  (Nat → Nat)
#check Nat →  Nat → Bool
#check (Nat →  Nat) → Nat

-- Define some types
def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α
#check F α
#check F Nat
#check List α
#check List Nat
#check G α
#check G α β
#check Prod α β
#check α × β

-- what type does Type itself have?
#check Type
#check Type 1
#check Type 2
#check Type 3
#check Type 4
#check Type 0 -- Type abbreviation for Type 0

#check List
#check Prod

/- Function Abstraction and Evaluation -/

-- λ and fun mean the same thing
#check fun (x : Nat) => x + 5
#check λ (x : Nat) => x + 5
-- The type Nat can be inferred in this example:
#check fun x => x + 5
#check λ x => x + 5

-- Lambda function evaluation
#eval (λ x : Nat => x + 5) 10

-- more examples(same expression)
#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2 -- infer the type of x and y

def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check fun x : Nat => x -- the identity function on Nat
set_option linter.unusedVariables false
#check fun x : Nat => true --  the constant function that always returns true
#check fun x : Nat => g (f x) --  the composition of f and g
#check fun x => g (f x) -- infer the type of lamda function from definition

--  shortcut above implemtation
#check fun (g : String → Bool) (f : Nat → String) (x : Nat) => g (f x)

/- Definitions -/

def double (x : Nat) : Nat := x + x
#eval double 3

#eval (fun x => x + x) 3

-- def double : Nat → Nat := fun x => x + x
-- #eval double 3

def add (x y : Nat) :=
  x + y
#eval add 3 2

-- def add (x : Nat) (y : Nat) := x + y
#eval add (double 3) (7 + 9)

def doTwice (f : Nat → Nat) (x : Nat) : Nat := f (f x)
#eval doTwice double 2

def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
def square (x : Nat) : Nat :=
  x * x
#eval compose Nat Nat Nat double square 3

/- Local Definitions -/

#check let y := 2 + 2; y * y
#eval  let y := 2 + 2; y * y

def twice_double (x : Nat) : Nat := let y := x + x; y * y
#eval twice_double 2

#check let y := 2 + 2; let z := y + y; z * z
#eval  let y := 2 + 2; let z := y + y; z * z
