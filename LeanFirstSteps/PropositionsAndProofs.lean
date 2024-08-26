open Classical

variable (p q : Prop)

def and_is_commutative : p∧q ↔ q∧p :=
Iff.intro
(fun (hpq: p∧q) => And.intro hpq.right hpq.left)
(fun (hpq: q∧p) => And.intro hpq.right hpq.left)

#check and_is_commutative

#check em
#check em p

#check absurd

theorem dne (h : ¬¬p) : p :=
Or.elim (em p)
(fun hp : p => hp)
(fun hnp : ¬p => absurd hnp h)

#check dne

theorem dne_implies_em (h : ¬¬p → p) : p ∨ ¬p :=
sorry

theorem dne_by_cases (h : ¬¬p) : p :=
byCases
  (fun hp : p => hp)
  (fun hnp : ¬p => absurd hnp h)

example (h : ¬¬p) : p :=
  byContradiction
    (fun h1 : ¬p =>
     show False from h h1)

example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  Or.elim (em p)
    (fun hp : p =>
      Or.inr
        (show ¬q from
          fun hq : q =>
          h ⟨hp, hq⟩))
    (fun hp : ¬p =>
      Or.inl hp)

example : ¬(p → q) → p ∧ ¬q :=
  fun h : ¬(p → q) =>
    And.intro
      (byContradiction
        (fun hnp : ¬p =>
          have hpq : p → q := fun hp : p => absurd hp hnp
          show False from h hpq))
      (byContradiction
        (fun hnq : ¬¬q =>
          have hq : q := not_not.mp hnq
          have hpq : p → q := fun _ => hq
          show False from h hpq))
