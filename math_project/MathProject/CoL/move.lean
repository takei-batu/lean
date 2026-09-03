import Mathlib.Order.Basic

-- def alphabet : List Char := ['0', '1', '2','3', '4', '5', '6', '7', '8', '9', '.', ':', '♠']
-- def isValid (s : String) : Bool := s.toList.all (fun c => alphabet.contains c)
-- def Move : Type := { s : String // isValid s = true } deriving DecidableEq

-- inductive Move_alphabet where
-- | zero
-- | one
-- | two
-- | three
-- | four
-- | five
-- | six
-- | seven
-- | eight
-- | nine
-- | dot
-- | colon
-- | spade
-- deriving DecidableEq

-- instance : Repr Move_alphabet where
--   reprPrec x _ :=
--     match x with
--     | .zero => "0"
--     | .one => "1"
--     | .two => "2"
--     | .three => "3"
--     | .four => "4"
--     | .five => "5"
--     | .six => "6"
--     | .seven => "7"
--     | .eight => "8"
--     | .nine => "9"
--     | .dot => "."
--     | .colon => ":"
--     | .spade => "♠"

-- def Move := List Move_alphabet deriving DecidableEq

-- instance : Repr Move where
--   reprPrec α _ := Std.Format.join (α.map repr)
--   reprPrec α _ := α.val

abbrev Move := String

inductive Player where
  | machine
  | environment
deriving DecidableEq

instance : Repr Player where
  reprPrec p _ :=
    match p with
    | Player.machine => f!"⊤"
    | Player.environment => f!"⊥"

instance : Compl Player where
  compl
    | .machine     => .environment
    | .environment => .machine

notation (name := player_machine) "⊤"   => Player.machine
notation (name := player_environment) "⊥"   => Player.environment

#check ⊤
#check ⊥
#check ⊥ᶜ
#check ⊤ᶜ
#eval ⊥ᶜ
#eval ⊤ᶜ

structure CM where
  player : Player
  move : Move
deriving DecidableEq

instance : Repr CM where
  reprPrec l _ := f!"{repr l.player}{repr l.move}"
