/- GID: D5/S0/Tower/Tribonacci/Names
   generality: I
   mirror-B: D5/B/S0/Tower/Tribonacci/Names
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Binary strings without three consecutive true digits have Tribonacci cardinality. -/

import Mathlib

namespace D5.S0.Tower.Tribonacci.Names

/-- The Tribonacci sequence with initial values `0, 1, 1`. -/
def tribonacci : Nat -> Nat
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n + 3 => tribonacci (n + 2) + tribonacci (n + 1) + tribonacci n

/-- The defining three-term recurrence for `tribonacci`. -/
theorem tribonacci_add_three (n : Nat) :
    tribonacci (n + 3) =
      tribonacci (n + 2) + tribonacci (n + 1) + tribonacci n := by
  simp [tribonacci]

/-- A binary word is Tribonacci-admissible when it contains no three consecutive `true` digits. -/
def TribonacciAdmissible : (Q : Nat) -> (Fin Q -> Bool) -> Prop
  | 0, _ => True
  | 1, _ => True
  | 2, _ => True
  | n + 3, word =>
      (¬ (word 0 ∧ word 1 ∧ word 2)) ∧
        TribonacciAdmissible (n + 2) (Fin.tail word)

instance tribonacciAdmissibleDecidable :
    (Q : Nat) -> (word : Fin Q -> Bool) -> Decidable (TribonacciAdmissible Q word)
  | 0, _ => isTrue trivial
  | 1, _ => isTrue trivial
  | 2, _ => isTrue trivial
  | n + 3, word =>
      have : Decidable (TribonacciAdmissible (n + 2) (Fin.tail word)) :=
        tribonacciAdmissibleDecidable (n + 2) (Fin.tail word)
      inferInstanceAs (Decidable
        ((¬ (word 0 ∧ word 1 ∧ word 2)) ∧
          TribonacciAdmissible (n + 2) (Fin.tail word)))

/-- Length-`Q` Tribonacci names are admissible binary words of length `Q`. -/
def TribonacciName (Q : Nat) :=
  {word : Fin Q -> Bool // TribonacciAdmissible Q word}

instance (Q : Nat) : Fintype (TribonacciName Q) := Subtype.fintype _

theorem admissible_add_three_iff (n : Nat) (word : Fin (n + 3) -> Bool) :
    TribonacciAdmissible (n + 3) word ↔
      (¬ (word 0 ∧ word 1 ∧ word 2)) ∧
        TribonacciAdmissible (n + 2) (Fin.tail word) := by
  simp only [TribonacciAdmissible]

theorem admissible_tail (n : Nat) (word : Fin (n + 1) -> Bool)
    (hadmissible : TribonacciAdmissible (n + 1) word) :
    TribonacciAdmissible n (Fin.tail word) := by
  match n with
  | 0 => trivial
  | 1 => trivial
  | 2 => exact (admissible_add_three_iff 0 word).1 hadmissible |>.2
  | k + 3 => exact (admissible_add_three_iff (k + 1) word).1 hadmissible |>.2

theorem admissible_cons_false (n : Nat) (word : Fin n -> Bool) :
    TribonacciAdmissible (n + 1) (Fin.cons false word) ↔
      TribonacciAdmissible n word := by
  match n with
  | 0 => simp [TribonacciAdmissible]
  | 1 => simp [TribonacciAdmissible]
  | k + 2 =>
      simp [TribonacciAdmissible, Fin.tail_cons, Fin.cons_zero]

theorem admissible_cons_true_false (n : Nat) (word : Fin n -> Bool) :
    TribonacciAdmissible (n + 2) (Fin.cons true (Fin.cons false word)) ↔
      TribonacciAdmissible n word := by
  match n with
  | 0 => simp [TribonacciAdmissible]
  | k + 1 =>
      rw [admissible_add_three_iff k]
      simp [Fin.tail_cons, Fin.cons_zero, admissible_cons_false]

@[simp] theorem fin_cons_one {n : Nat} (head : Bool) (tail : Fin (n + 1) -> Bool) :
    (Fin.cons head tail : Fin (n + 2) -> Bool) (1 : Fin (n + 2)) = tail 0 := by
  rw [show (1 : Fin (n + 2)) = Fin.succ 0 from (Fin.succ_zero_eq_one).symm,
    Fin.cons_succ]

@[simp] theorem fin_cons_two {n : Nat} (head : Bool) (tail : Fin (n + 2) -> Bool) :
    (Fin.cons head tail : Fin (n + 3) -> Bool) (2 : Fin (n + 3)) = tail 1 := by
  rw [show (2 : Fin (n + 3)) = Fin.succ 1 by ext; simp, Fin.cons_succ]

theorem admissible_cons_true_true_false (n : Nat) (word : Fin n -> Bool) :
    TribonacciAdmissible (n + 3)
        (Fin.cons true (Fin.cons true (Fin.cons false word))) ↔
      TribonacciAdmissible n word := by
  rw [admissible_add_three_iff n]
  simp [Fin.tail_cons, Fin.cons_zero, fin_cons_two,
    admissible_cons_true_false]

/-- Splitting on the initial block `0`, `10`, or `110` gives the Tribonacci recurrence. -/
def tribonacciNameSplitEquiv (n : Nat) :
    TribonacciName (n + 3) ≃
      (TribonacciName (n + 2) ⊕ (TribonacciName (n + 1) ⊕ TribonacciName n)) where
  toFun name :=
    match name.1 0 with
    | true =>
      match name.1 1 with
      | true =>
        Sum.inr (Sum.inr
          ⟨Fin.tail (Fin.tail (Fin.tail name.1)),
            admissible_tail n (Fin.tail (Fin.tail name.1))
                (admissible_tail (n + 1) (Fin.tail name.1)
                  (admissible_tail (n + 2) name.1 name.2))⟩)
      | false =>
        Sum.inr (Sum.inl
          ⟨Fin.tail (Fin.tail name.1),
            admissible_tail (n + 1) (Fin.tail name.1)
              (admissible_tail (n + 2) name.1 name.2)⟩)
    | false =>
      Sum.inl
        ⟨Fin.tail name.1, admissible_tail (n + 2) name.1 name.2⟩
  invFun := fun split =>
    match split with
    | Sum.inl name =>
        ⟨Fin.cons false name.1, (admissible_cons_false (n + 2) name.1).2 name.2⟩
    | Sum.inr (Sum.inl name) =>
        ⟨Fin.cons true (Fin.cons false name.1),
          (admissible_cons_true_false (n + 1) name.1).2 name.2⟩
    | Sum.inr (Sum.inr name) =>
        ⟨Fin.cons true (Fin.cons true (Fin.cons false name.1)),
          (admissible_cons_true_true_false n name.1).2 name.2⟩
  left_inv := by
    rintro ⟨name, hadmissible⟩
    cases h0 : name 0 with
    | false =>
      simp only [h0]
      apply Subtype.ext
      change Fin.cons false (Fin.tail name) = name
      calc
        Fin.cons false (Fin.tail name) = Fin.cons (name 0) (Fin.tail name) := by
          simp [h0]
        _ = name := Fin.cons_self_tail name
    | true =>
      cases h1 : name 1 with
      | true =>
        simp only [h0, h1]
        apply Subtype.ext
        have h2 : name 2 = false := by
          cases hvalue : name 2 with
          | false => rfl
          | true =>
              have hforbidden := (admissible_add_three_iff n name).1 hadmissible |>.1
              simp [h0, h1, hvalue] at hforbidden
        have rebuild2 :
            Fin.cons false (Fin.tail (Fin.tail (Fin.tail name))) = Fin.tail (Fin.tail name) := by
          calc
            _ = Fin.cons ((Fin.tail (Fin.tail name)) 0)
                (Fin.tail (Fin.tail (Fin.tail name))) := by simp [Fin.tail, h2]
            _ = Fin.tail (Fin.tail name) := Fin.cons_self_tail (Fin.tail (Fin.tail name))
        have rebuild1 : Fin.cons true (Fin.tail (Fin.tail name)) = Fin.tail name := by
          calc
            _ = Fin.cons ((Fin.tail name) 0) (Fin.tail (Fin.tail name)) := by
              simp [Fin.tail, h1]
            _ = Fin.tail name := Fin.cons_self_tail (Fin.tail name)
        have rebuild0 : Fin.cons true (Fin.tail name) = name := by
          calc
            _ = Fin.cons (name 0) (Fin.tail name) := by simp [h0]
            _ = name := Fin.cons_self_tail name
        change Fin.cons true (Fin.cons true (Fin.cons false
          (Fin.tail (Fin.tail (Fin.tail name))))) = name
        calc
          _ = Fin.cons true (Fin.cons true (Fin.tail (Fin.tail name))) := by
            rw [rebuild2]
          _ = Fin.cons true (Fin.tail name) := by rw [rebuild1]
          _ = name := rebuild0
      | false =>
        simp only [h0, h1]
        apply Subtype.ext
        have rebuild1 : Fin.cons false (Fin.tail (Fin.tail name)) = Fin.tail name := by
          calc
            _ = Fin.cons ((Fin.tail name) 0) (Fin.tail (Fin.tail name)) := by
              simp [Fin.tail, h1]
            _ = Fin.tail name := Fin.cons_self_tail (Fin.tail name)
        have rebuild0 : Fin.cons true (Fin.tail name) = name := by
          calc
            _ = Fin.cons (name 0) (Fin.tail name) := by simp [h0]
            _ = name := Fin.cons_self_tail name
        change Fin.cons true (Fin.cons false (Fin.tail (Fin.tail name))) = name
        calc
          _ = Fin.cons true (Fin.tail name) := by rw [rebuild1]
          _ = name := rebuild0
  right_inv := by
    rintro (name | (name | name))
    · congr 1
    · congr 1
    · congr 1

/-- Counts at length `n+3` split into the three preceding name layers. -/
theorem tribonacci_name_card_add_three (n : Nat) :
    Fintype.card (TribonacciName (n + 3)) =
      Fintype.card (TribonacciName (n + 2)) +
        Fintype.card (TribonacciName (n + 1)) +
          Fintype.card (TribonacciName n) := by
  rw [Fintype.card_congr (tribonacciNameSplitEquiv n), Fintype.card_sum,
    Fintype.card_sum]
  omega

example : Fintype.card (TribonacciName 0) = 1 := by decide
example : Fintype.card (TribonacciName 1) = 2 := by decide
example : Fintype.card (TribonacciName 2) = 4 := by decide
example : Fintype.card (TribonacciName 3) = 7 := by decide
example : Fintype.card (TribonacciName 4) = 13 := by decide

/-- There are exactly `tribonacci (Q+2)` length-`Q` Tribonacci names. -/
theorem tribonacci_name_card (Q : Nat) :
    Fintype.card (TribonacciName Q) = tribonacci (Q + 2) := by
  induction Q using Nat.strong_induction_on with
  | h Q ih =>
      match Q with
      | 0 => decide
      | 1 => decide
      | 2 => decide
      | n + 3 =>
          rw [tribonacci_name_card_add_three n,
            ih (n + 2) (by omega), ih (n + 1) (by omega), ih n (by omega)]
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (tribonacci_add_three (n + 2)).symm

/-- Tribonacci names identify with the explicit initial interval of the same cardinality. -/
noncomputable def tribonacciNameEquiv (Q : Nat) :
    Fin (tribonacci (Q + 2)) ≃ TribonacciName Q :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, tribonacci_name_card])

end D5.S0.Tower.Tribonacci.Names
