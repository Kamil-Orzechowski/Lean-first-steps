def length (l : List α) : Nat :=
  match l with
  | List.nil => 0
  | List.cons _ l' => 1 + length l'

#eval length [2, 4, 8]

def reverse (l : List α) : List α :=
  match l with
  | List.nil => List.nil
  | List.cons a l' => (reverse l') ++ [a]

#eval reverse ["a", "b", "c"]

theorem length_add : ∀ (s t : List α), length (s ++ t) = length s + length t :=
  fun (s t : List α) =>
    match s with
    | List.nil =>
      have h1 : length ([] ++ t) = length t := rfl
      have h2 : length [] = 0  := rfl
      by rw[h1, h2, Nat.zero_add]
    | List.cons a l' =>
      have h1 : length (a :: l' ++ t) = 1 + length (l' ++ t) := rfl
      have h2 : length (l' ++ t) = length l' + length t := length_add l' t
      have h3 : length (a :: l') = 1 + length l' := rfl
      by rw[h1, h2, h3, Nat.add_assoc]

theorem length_add_2 : ∀ (s t : List α), length (s ++ t) = length s + length t :=
  fun (s t : List α) =>
    match s with
    | List.nil =>
      calc length ([] ++ t) = length t := by rw[List.nil_append]
      _ = 0 + length t  := by rw[Nat.zero_add]
      _ = length [] + length t := rfl
    | List.cons a l' =>
      calc length (a :: l' ++ t) = 1 + length (l' ++ t) := rfl
      _ = 1 + length l' + length t := by rw[length_add_2, Nat.add_assoc]
      _ = length (a :: l') + length t := rfl

theorem length_add_3 : ∀ (s t : List α), length (s ++ t) = length s + length t := by
  intro s t
  cases s with
  | nil =>
    rw[List.nil_append, length, Nat.zero_add]
  | cons a l' =>
    rw[List.cons_append, length, length, length_add_3, Nat.add_assoc]

theorem len_rev : length (reverse t) = length t := by
  cases t with
  | nil =>
    rw[reverse]
  | cons a l' =>
    rw[reverse, length, length_add, len_rev, length, length, Nat.add_zero, Nat.add_comm]

theorem reverse_append (l₁ l₂ : List α) : reverse (l₁ ++ l₂) = reverse l₂ ++ reverse l₁ := by
  induction l₁ with
  | nil =>
      -- Base case: when `l₁` is `nil`, `reverse (nil ++ l₂) = reverse l₂`.
      rw [reverse, List.nil_append, List.append_nil]
  | cons a l₁' ih =>
      -- Inductive step: assume the lemma holds for `l₁'`, and prove it for `a :: l₁'`.
      rw [List.cons_append, reverse, reverse, ih]
      -- Simplify to reach the final goal.
      rw [List.append_assoc]

theorem involution (t : List α) : reverse (reverse t) = t := by
  cases t with
  | nil =>
      -- Base case: when `t` is `nil`, the reverse of an empty list is itself.
      rw [reverse, reverse]
  | cons a l =>
      -- Inductive step: assume the theorem holds for `l`, and prove it for `a :: l`.
      -- The goal is to show that `reverse (reverse (a :: l)) = a :: l`.
      -- We can rewrite `reverse (a :: l)` using the definition of `reverse`.
      rw [reverse, reverse_append, involution, reverse, reverse, List.nil_append]
      calc [a] ++ l = a :: l := rfl
