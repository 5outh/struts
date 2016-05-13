module Struts

data Rat : Nat -> Nat -> Type where
  MkRat : (a : Nat) -> (b : Nat) -> Rat a b

multRat : Rat a b -> Rat c d -> Rat (a*c) (b*d)
multRat (MkRat a b) (MkRat c d) = MkRat (a*c) (b*d)

divRat : Rat a b -> Rat c d -> Rat (a*d) (b*c)
divRat (MkRat a b) (MkRat c d) = MkRat (a*d) (b*c)

addRat : Rat a b -> Rat c d -> Rat (a*d + b*c) (b*d)
addRat (MkRat a b) (MkRat c d) = MkRat (a*d + b*c) (b*d)

simplify : Rat a b -> Rat (divNat a (gcd a b)) (divNat b (gcd a b))
simplify (MkRat a b) = MkRat (divNat a (gcd a b)) (divNat b (gcd a b))

fromNat : (n : Nat) -> Rat n 1
fromNat n = MkRat n 1

data Pitch = A | B | C | D | E | F | G

data Note : (r : Rat a b) -> Type where
  MkNote : Pitch -> Note r

quarter : Pitch -> Note (MkRat 1 4)
quarter = MkNote

data NoteSequence : (r : Rat a b) -> Type where
  Empty : NoteSequence (fromNat 0)
  Append : Note s -> NoteSequence r -> NoteSequence (addRat s r)

data Measure : (r : Rat a b) -> Type where
  MkMeasure : NoteSequence r -> Measure r

fin : NoteSequence (fromNat 0)
fin = Empty

infixr 10 ~>

(~>) : Note s -> NoteSequence r -> NoteSequence (addRat s r)
(~>) = Append

beatMeasure : Measure (MkRat 1 4)
beatMeasure = MkMeasure (quarter C ~> fin)

