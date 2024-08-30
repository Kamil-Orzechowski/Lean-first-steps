#check propext
#check funext

def Set (α : Type u) := α → Prop

namespace Set

def mem (x : α) (a : Set α) := a x

infix:50 (priority := high) "∈" => mem

theorem setext {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
  funext (fun x => propext (h x))

end Set

def empty : Set α :=
  fun x : α => False

def inter (a b : Set α) : Set α :=
  fun x : α => x ∈ a ∧ x ∈ b

infix:70 " ∩ " => inter

theorem inter_self (a : Set α) : a ∩ a = a :=
  funext (fun x : α =>
    show (a ∩ a) x = a x from
       by rw[inter, Set.mem, and_self]
       )

theorem inter_self₂ (a : Set α) : a ∩ a = a :=
  have h : ∀ x, x ∈ a ∩ a ↔ x ∈ a :=
  fun x =>
    Iff.intro
    (fun ⟨p, _⟩ => p)
    (fun h => ⟨h, h⟩)
  Set.setext h

def f (x : Nat) := x
def g (x : Nat) := 0 + x

theorem f_eq_g : f = g :=
  funext fun x => (Nat.zero_add x).symm

def val : Nat :=
  Eq.recOn (motive := fun _ _ => Nat) f_eq_g 0

-- does not reduce to 0
#reduce val

-- evaluates to 0
#eval val

#check Eq.recOn
