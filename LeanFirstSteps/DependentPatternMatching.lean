inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

namespace Vector

#check Vector.casesOn

-- def tailAux (v : Vector α m) : m = n + 1 → Vector α n :=
--   Vector.casesOn (motive := fun x _ => x = n + 1 → Vector α n) v
--     (fun h : 0 = n + 1 => Nat.noConfusion h)
--     (fun (a : α) (m : Nat) (as : Vector α m) =>
--      fun (h : m + 1 = n + 1) =>
--        Nat.noConfusion h (fun h1 : m = n => h1 ▸ as))

-- def tail (v : Vector α (n+1)) : Vector α n :=
--   tailAux v rfl

def head : {n : Nat} → Vector α (n+1) → α
  | n, cons a as => a

def tail : {n : Nat} → Vector α (n+1) → Vector α n
  | n, cons a as => as

theorem eta : ∀ {n : Nat} (v : Vector α (n+1)), cons (head v) (tail v) = v
  | n, cons a as => rfl

def zip : {n : Nat} → Vector α n → Vector β n → Vector (α × β) n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (a, b) (zip as bs)

def map (f : α → β → γ) : {n : Nat} → Vector α n → Vector β n → Vector γ n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (f a b) (map f as bs)





def append_one (a : α) (v : Vector α n) : Vector α (n+1) :=
  cons a v

--  def append : (Vector α n1) →  (Vector α n2) → Vector α (n1+n2)
--   | nil, v2 =>
--   | cons a v, v2 => cons a (append v v2)


def append {α : Type} {n1 n2 : Nat} : Vector α n1 → Vector α n2 → Vector α (n1 + n2)
  | nil, v2 => by
    rw [Nat.zero_add]
    exact v2
  | cons a v, v2 => by
    rw[Nat.add_right_comm]
    exact cons a (append v v2)

#print append
variable (a b : Nat)
#reduce append (cons a nil) (cons b nil)

  -- | a, nil => cons a nil
  -- | a, cons b bs => cons a




end Vector
