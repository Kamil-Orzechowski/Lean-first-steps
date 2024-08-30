set_option diagnostics true
set_option diagnostics.threshold 100

#check Add
#check Add.add

def double (s : Add a) (x : a) : a :=
  s.add x x

#check double

#eval double {add := Nat.add} 20
#eval double {add := Nat.mul} 20

#check Inhabited

#check toString
#check ToString

structure Person where
  name : String
  age  : Nat

instance : ToString Person where
  toString p := p.name ++ "@" ++ toString p.age

#eval toString {name := "Kamil", age := 33 : Person}
#eval toString ({ name := "Daniel", age := 18 : Person }, "hello")

structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

instance : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#eval (2 : Rational)
