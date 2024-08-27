section

#check Exists

example : ∃ x : Nat, x > 0 :=
have h : 1 > 0 := Nat.zero_lt_one
Exists.intro 1 h

example : ∃ x : Nat, x > 0 :=
have h : 1 > 0 := Nat.zero_lt_one
⟨1, h⟩

variable (g : Nat → Nat → Nat)
variable (hg : g 0 0 = 0)

theorem gex1 : ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 : ∃ x, g x 0 = x := ⟨0, hg⟩
theorem gex3 : ∃ x, g 0 0 = x := ⟨0, hg⟩
theorem gex4 : ∃ x, g x x = 0 := ⟨0, hg⟩

set_option pp.explicit true  -- display implicit arguments
#print gex1
#print gex2
#print gex3
#print gex4

end section

variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
Exists.elim
  h
  fun x : α => fun h₂ : p x ∧ q x => ⟨ x, And.intro h₂.right h₂.left⟩

def is_even (a : Nat) := ∃ b, a = 2 * b

theorem even_plus_even (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
match h1 with
| ⟨k1, ass1⟩ =>
  match h2 with
  | ⟨k2, ass2⟩ =>
    ⟨k1 + k2, show a + b = 2 * (k1 + k2) by
      rw[ass1, ass2, Nat.mul_add]⟩

end section

section

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r :=
fun h : (∃ x : α, r) =>
  match h with
  | ⟨x, px⟩ => px

example (a : α) : r → (∃ x : α, r) :=
  fun t : r => ⟨a, t⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    fun h : (∃ x, p x ∧ r) =>
      match h with
      | ⟨x, t⟩ => ⟨⟨x, t.left⟩, t.right⟩
    fun h : (∃ x, p x) ∧ r =>
      match h.left with
      | ⟨x, t⟩ => ⟨x, ⟨t, h.right⟩⟩

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    fun h : (∃ x, p x ∨ q x) =>
      match h with
      | ⟨x, t⟩ => Or.elim t
                        (fun h₁ : p x => Or.inl ⟨x, h₁⟩)
                        (fun h₂ : q x => Or.inr ⟨x, h₂⟩)
    fun h : (∃ x, p x) ∨ (∃ x, q x) =>
      Or.elim h
              fun h₁ : (∃ x, p x) =>
                match h₁ with
                | ⟨x, t⟩ => ⟨x, Or.inl t⟩
              fun h₂ : (∃ x, q x) =>
                match h₂ with
                | ⟨x, t⟩ => ⟨x, Or.inr t⟩


theorem first_impl : (∀ x, p x) →  ¬ (∃ x, ¬ p x) :=
    fun h : (∀ x, p x) =>
      fun h₂ : (∃ x, ¬ p x) =>
        match h₂ with
        | ⟨x, t⟩ => t (h x)

theorem second_impl : ¬ (∃ x, ¬ p x) → (∀ x, p x) :=
  fun h : ¬ (∃ x, ¬ p x) =>
      fun x  =>
        Or.elim
                (Classical.em (p x))
                (fun hpx : p x => hpx)
                (fun hnpx : ¬ p x => False.elim (h ⟨x, hnpx⟩))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
    (fun h : (∀ x, p x) =>
      fun h₂ : (∃ x, ¬ p x) =>
        match h₂ with
        | ⟨x, t⟩ => t (h x))
    (fun h : ¬ (∃ x, ¬ p x) =>
      fun x  =>
        Or.elim
                (Classical.em (p x))
                (fun hpx : p x => hpx)
                (fun hnpx : ¬ p x => False.elim (h ⟨x, hnpx⟩)))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro (first_impl α p) (second_impl α p)

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun h : (∃ x, p x → r) =>
      match h with
      | ⟨x₀, pxr⟩ => fun h₁ : (∀ x, p x) => pxr (h₁ x₀))
    (fun h : (∀ x, p x) → r =>
      Or.elim
        (Classical.em (∀ x, p x))
        (fun h₁ : (∀ x, p x) => ⟨a, (fun hpa : p a => h h₁)⟩)
        (fun h₂ : ¬ (∀ x, p x) =>
          have aux : (∃ x ,¬ p x) := Classical.not_forall.mp h₂
          match aux with
          | ⟨x₀, t⟩ => ⟨x₀, fun hp : p x₀ => False.elim (t hp)⟩))
