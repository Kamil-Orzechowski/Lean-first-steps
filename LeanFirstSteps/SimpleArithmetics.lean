inductive myNat where
| zero : myNat
| succ : myNat → myNat

open myNat

def add (m n : myNat) : myNat :=
match n with
| zero => m
| succ k => (add m k).succ

def one : myNat := zero.succ
def two : myNat := one.succ
def four : myNat := two.succ.succ

theorem two_plus_two_is_four : add two two = four := by
rw[four]
rw[two]
rw[one]
rw[add]
rw[add]
rw[add]
