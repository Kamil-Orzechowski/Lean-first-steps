#check Acc
#print Acc
#print Acc.intro

#print WellFounded
#print WellFounded.fix
#print WellFounded.fixF

#check WellFounded.fix
#reduce WellFounded.fix

#check WellFounded Nat.le
#check WellFounded.fix

def natToBin : Nat → List Nat
  | 0     => [0]
  | 1     => [1]
  | n + 2 =>
    natToBin ((n + 2) / 2) ++ [n % 2]

#eval natToBin 15

def div (x y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    div (x - y) y + 1
  else
    0

#eval div 3 4

-- Course-of-values recursion

inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

def head : {n : Nat} → Vector α (n+1) → α
  | _, Vector.cons a _ => a

def courseOfValues (step : (n : Nat) → Vector α n → α) (arg : Nat) : Vector α arg :=
  match arg with
  | 0 => Vector.nil
  | n+1 => let prev := courseOfValues step n;
    Vector.cons (step n prev) prev

def recursive (step : (n : Nat) → Vector α n → α) (arg : Nat) : α :=
  let vec := courseOfValues step (arg+1); head vec
