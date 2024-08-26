inductive mynat : Type
| zero : mynat
| succ : mynat → mynat

open mynat

def two : mynat := succ (succ zero)

def pred (n : mynat) : mynat :=
match n with
| zero => zero
| succ m => m


def add : mynat → mynat → mynat :=
  λ n m =>
  match m with
  | zero => n
  | succ m' => succ (add n m')


inductive myeq : ∀ {α : Type}, α → α → Prop
| myrefl : ∀ {α : Type} {a : α}, myeq a a

open myeq

def this_is_free : myeq (succ zero) (succ zero) :=
  myrefl

theorem this_is_almost_free :
  myeq (add two zero) (add zero two) :=
myrefl


theorem cong : ∀ (f : mynat → mynat) (n m : mynat),
  myeq n m → myeq (f n) (f m) := by

intro f n m hnm
cases hnm
apply myrefl


theorem add_n_zero : ∀ n : mynat, myeq (add n zero) n :=
by
apply myrefl

theorem add_zero_n : ∀ n : mynat, myeq (add zero n) n := by
intro n
induction n with
| zero => apply myrefl
| succ n' ihn' =>
rw[add]
apply cong
exact ihn'
