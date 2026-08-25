/- GID: D5/S0/Tower/DBonacci/Names
   generality: I
   mirror-B: D5/B/S0/Tower/DBonacci/Names
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Binary words avoiding d consecutive true digits have d-bonacci cardinality. -/

import D5.S0.Tower.Tribonacci.Names

namespace D5.S0.Tower.DBonacci.Names

/-- The d-bonacci sequence, normalized so the length-`Q` name layer occurs at `Q + 2`. -/
def dbonacci (d n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | q + 2 =>
      if q < d then 2 ^ q
      else ∑ i : Fin d, dbonacci d (q - d + i + 2)
termination_by n
decreasing_by omega

/-- Once the initial powers of two are exhausted, `dbonacci` sums its preceding `d` terms. -/
theorem dbonacci_add_two_of_le (d q : Nat) (horder : d ≤ q) :
    dbonacci d (q + 2) =
      ∑ i : Fin d, dbonacci d (q - d + i + 2) := by
  rw [dbonacci]
  exact if_neg (Nat.not_lt_of_ge horder)

@[simp] theorem dbonacci_zero (d : Nat) : dbonacci d 0 = 0 := by
  rw [dbonacci]

@[simp] theorem dbonacci_one (d : Nat) : dbonacci d 1 = 1 := by
  rw [dbonacci]

theorem dbonacci_add_two_of_lt (d q : Nat) (hshort : q < d) :
    dbonacci d (q + 2) = 2 ^ q := by
  rw [dbonacci]
  exact if_pos hshort

/-- Scan a word with `fuel` further consecutive `true` digits available before failure. -/
def runAdmissible (maxTrue : Nat) :
    (fuel Q : Nat) -> (Fin Q -> Bool) -> Bool
  | _, 0, _ => true
  | 0, q + 1, word =>
      if word 0 then false else runAdmissible maxTrue maxTrue q (Fin.tail word)
  | fuel + 1, q + 1, word =>
      if word 0 then
        runAdmissible maxTrue fuel q (Fin.tail word)
      else
        runAdmissible maxTrue maxTrue q (Fin.tail word)

/-- A length-`Q` word is d-bonacci-admissible exactly when no run reaches `d` true digits. -/
def DBonacciAdmissible (d Q : Nat) (word : Fin Q -> Bool) : Prop :=
  match d with
  | 0 => False
  | maxTrue + 1 => runAdmissible maxTrue maxTrue Q word = true

instance dbonacciAdmissibleDecidable (d Q : Nat) (word : Fin Q -> Bool) :
    Decidable (DBonacciAdmissible d Q word) := by
  unfold DBonacciAdmissible
  split <;> infer_instance

/-- Length-`Q` d-bonacci names are Boolean words without `d` consecutive true digits. -/
def DBonacciName (d Q : Nat) :=
  {word : Fin Q -> Bool // DBonacciAdmissible d Q word}

instance (d Q : Nat) : Fintype (DBonacciName d Q) := Subtype.fintype _

/-- Auxiliary name layers with an explicit current true-run budget. -/
def BoundedRunName (maxTrue fuel Q : Nat) :=
  {word : Fin Q -> Bool // runAdmissible maxTrue fuel Q word = true}

instance (maxTrue fuel Q : Nat) : Fintype (BoundedRunName maxTrue fuel Q) :=
  Subtype.fintype _

theorem runAdmissible_eq_true_of_length_le (maxTrue fuel Q : Nat)
    (word : Fin Q -> Bool) (hlength : Q ≤ fuel) (hbudget : fuel ≤ maxTrue) :
    runAdmissible maxTrue fuel Q word = true := by
  induction Q generalizing fuel with
  | zero => simp [runAdmissible]
  | succ q ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          cases hhead : word 0 with
          | false =>
              simp only [runAdmissible, hhead, Bool.false_eq_true, ↓reduceIte]
              exact ih maxTrue (Fin.tail word) (by omega) le_rfl
          | true =>
              simp only [runAdmissible, hhead, ↓reduceIte]
              exact ih fuel (Fin.tail word) (by omega) (by omega)

/-- A positive d-bonacci layer is the full-budget bounded-run layer. -/
def dbonacciNameBoundedEquiv (maxTrue Q : Nat) :
    DBonacciName (maxTrue + 1) Q ≃ BoundedRunName maxTrue maxTrue Q where
  toFun name := ⟨name.1, by simpa [DBonacciAdmissible] using name.2⟩
  invFun name := ⟨name.1, by simpa [DBonacciAdmissible] using name.2⟩
  left_inv name := by cases name; rfl
  right_inv name := by cases name; rfl

/-- With zero true budget, the next digit is forced to be false. -/
def boundedRunNameZeroEquiv (maxTrue q : Nat) :
    BoundedRunName maxTrue 0 (q + 1) ≃ BoundedRunName maxTrue maxTrue q where
  toFun name := ⟨Fin.tail name.1, by
    cases hhead : name.1 0 with
    | false => simpa [runAdmissible, hhead] using name.2
    | true =>
        have hfalse : False := by
          simpa [runAdmissible, hhead] using name.2
        exact False.elim hfalse⟩
  invFun name := ⟨Fin.cons false name.1, by
    simpa [runAdmissible, Fin.cons_zero, Fin.tail_cons] using name.2⟩
  left_inv := by
    intro name
    cases hhead : name.1 0 with
    | false =>
        apply Subtype.ext
        simpa [hhead] using Fin.cons_self_tail name.1
    | true =>
        have hfalse : False := by
          simpa [runAdmissible, hhead] using name.2
        exact False.elim hfalse
  right_inv := by
    intro name
    apply Subtype.ext
    simp [Fin.tail_cons]

/-- A positive budget splits according to whether the next digit is false or true. -/
def boundedRunNameSplitEquiv (maxTrue fuel q : Nat) :
    BoundedRunName maxTrue (fuel + 1) (q + 1) ≃
      (BoundedRunName maxTrue maxTrue q ⊕ BoundedRunName maxTrue fuel q) where
  toFun name :=
    if hhead : name.1 0 = false then
      Sum.inl ⟨Fin.tail name.1, by
        simpa [runAdmissible, hhead] using name.2⟩
    else
      Sum.inr ⟨Fin.tail name.1, by
        have htrue : name.1 0 = true := by
          cases hvalue : name.1 0 <;> simp_all
        simpa [runAdmissible, htrue] using name.2⟩
  invFun split :=
    match split with
    | Sum.inl name => ⟨Fin.cons false name.1, by
        simpa [runAdmissible, Fin.cons_zero, Fin.tail_cons] using name.2⟩
    | Sum.inr name => ⟨Fin.cons true name.1, by
        simpa [runAdmissible, Fin.cons_zero, Fin.tail_cons] using name.2⟩
  left_inv := by
    intro name
    by_cases hhead : name.1 0 = false
    · simp only [dif_pos hhead]
      apply Subtype.ext
      simpa [hhead] using Fin.cons_self_tail name.1
    · have htrue : name.1 0 = true := by
        cases hvalue : name.1 0 <;> simp_all
      simp only [dif_neg hhead]
      apply Subtype.ext
      simpa [htrue] using Fin.cons_self_tail name.1
  right_inv := by
    rintro (name | name)
    · simp <;>
      apply congrArg Sum.inl <;>
      apply Subtype.ext <;>
      rfl
    · simp <;>
      apply congrArg Sum.inr <;>
      apply Subtype.ext <;>
      rfl

theorem bounded_run_name_card_zero (maxTrue q : Nat) :
    Fintype.card (BoundedRunName maxTrue 0 (q + 1)) =
      Fintype.card (BoundedRunName maxTrue maxTrue q) :=
  Fintype.card_congr (boundedRunNameZeroEquiv maxTrue q)

theorem bounded_run_name_card_succ (maxTrue fuel q : Nat) :
    Fintype.card (BoundedRunName maxTrue (fuel + 1) (q + 1)) =
      Fintype.card (BoundedRunName maxTrue maxTrue q) +
        Fintype.card (BoundedRunName maxTrue fuel q) := by
  rw [Fintype.card_congr (boundedRunNameSplitEquiv maxTrue fuel q),
    Fintype.card_sum]

/-- Iterating the budget split expresses a layer as the preceding `fuel+1` full-budget layers. -/
theorem bounded_run_name_card_unroll (maxTrue fuel n : Nat) :
    Fintype.card (BoundedRunName maxTrue fuel (n + fuel + 1)) =
      ∑ i ∈ Finset.range (fuel + 1),
        Fintype.card (BoundedRunName maxTrue maxTrue (n + i)) := by
  induction fuel generalizing n with
  | zero =>
      simpa using bounded_run_name_card_zero maxTrue n
  | succ fuel ih =>
      calc
        Fintype.card
            (BoundedRunName maxTrue (fuel + 1) (n + (fuel + 1) + 1)) =
            Fintype.card (BoundedRunName maxTrue maxTrue (n + fuel + 1)) +
              Fintype.card (BoundedRunName maxTrue fuel (n + fuel + 1)) := by
                simpa only [Nat.add_assoc] using
                  bounded_run_name_card_succ maxTrue fuel (n + fuel + 1)
        _ = Fintype.card (BoundedRunName maxTrue maxTrue (n + fuel + 1)) +
              ∑ i ∈ Finset.range (fuel + 1),
                Fintype.card (BoundedRunName maxTrue maxTrue (n + i)) := by
              rw [ih n]
        _ = ∑ i ∈ Finset.range (fuel + 1 + 1),
              Fintype.card (BoundedRunName maxTrue maxTrue (n + i)) := by
              conv_rhs =>
                rw [show fuel + 1 + 1 = (fuel + 1) + 1 by omega,
                  Finset.sum_range_succ]
              rw [show n + fuel + 1 = n + (fuel + 1) by omega]
              ac_rfl

theorem dbonacci_name_card_eq_bounded (maxTrue Q : Nat) :
    Fintype.card (DBonacciName (maxTrue + 1) Q) =
      Fintype.card (BoundedRunName maxTrue maxTrue Q) :=
  Fintype.card_congr (dbonacciNameBoundedEquiv maxTrue Q)

/-- At length `n+d`, splitting at the first false digit gives the d-term recurrence. -/
theorem dbonacci_name_card_recurrence (d n : Nat) (hpositive : 0 < d) :
    Fintype.card (DBonacciName d (n + d)) =
      ∑ i ∈ Finset.range d, Fintype.card (DBonacciName d (n + i)) := by
  cases d with
  | zero => omega
  | succ maxTrue =>
      simp only [dbonacci_name_card_eq_bounded]
      rw [show n + (maxTrue + 1) = n + maxTrue + 1 by omega]
      exact bounded_run_name_card_unroll maxTrue maxTrue n

/-- Before a run of length `d` can fit, every Boolean word is admissible. -/
theorem dbonacci_name_card_of_lt (d Q : Nat) (hlength : Q < d) :
    Fintype.card (DBonacciName d Q) = 2 ^ Q := by
  let allWordsEquiv : DBonacciName d Q ≃ (Fin Q -> Bool) :=
    { toFun := fun name => name.1
      invFun := fun word => ⟨word, by
        cases d with
        | zero => omega
        | succ maxTrue =>
            exact runAdmissible_eq_true_of_length_le maxTrue maxTrue Q word
              (by omega) le_rfl⟩
      left_inv := fun name => by cases name; rfl
      right_inv := fun word => rfl }
  calc
    Fintype.card (DBonacciName d Q) = Fintype.card (Fin Q -> Bool) :=
      Fintype.card_congr allWordsEquiv
    _ = 2 ^ Q := by simp

/-- There are exactly `dbonacci d (Q+2)` admissible length-`Q` Boolean words. -/
theorem dbonacci_name_card (d Q : Nat) :
    Fintype.card (DBonacciName d Q) = dbonacci d (Q + 2) := by
  induction Q using Nat.strong_induction_on with
  | h Q ih =>
      by_cases hshort : Q < d
      · rw [dbonacci_name_card_of_lt d Q hshort, dbonacci, if_pos hshort]
      · have horder : d ≤ Q := Nat.le_of_not_gt hshort
        cases d with
        | zero =>
            let emptyEquiv : DBonacciName 0 Q ≃ Empty :=
              { toFun := fun name => False.elim name.2
                invFun := fun empty => nomatch empty
                left_inv := fun name => False.elim name.2
                right_inv := fun empty => nomatch empty }
            calc
              Fintype.card (DBonacciName 0 Q) = Fintype.card Empty :=
                Fintype.card_congr emptyEquiv
              _ = 0 := Fintype.card_empty
              _ = dbonacci 0 (Q + 2) := by
                rw [dbonacci]
                simp
        | succ maxTrue =>
            let n := Q - (maxTrue + 1)
            have hdecompose : Q = n + (maxTrue + 1) := by
              dsimp [n]
              omega
            calc
              Fintype.card (DBonacciName (maxTrue + 1) Q) =
                  Fintype.card
                    (DBonacciName (maxTrue + 1) (n + (maxTrue + 1))) := by
                rw [hdecompose]
              _ = ∑ i ∈ Finset.range (maxTrue + 1),
                    Fintype.card (DBonacciName (maxTrue + 1) (n + i)) :=
                dbonacci_name_card_recurrence (maxTrue + 1) n (by omega)
              _ = ∑ i ∈ Finset.range (maxTrue + 1),
                    dbonacci (maxTrue + 1) (n + i + 2) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [ih (n + i) (by
                  have hirange := Finset.mem_range.mp hi
                  omega)]
              _ = dbonacci (maxTrue + 1) (Q + 2) := by
                symm
                rw [dbonacci_add_two_of_le (maxTrue + 1) Q horder,
                  Finset.sum_fin_eq_sum_range]
                apply Finset.sum_congr rfl
                intro i hi
                have hirange := Finset.mem_range.mp hi
                simp [hirange, n]

example : Fintype.card (DBonacciName 2 0) = 1 := by decide
example : Fintype.card (DBonacciName 2 1) = 2 := by decide
example : Fintype.card (DBonacciName 2 2) = 3 := by decide
example : Fintype.card (DBonacciName 2 3) = 5 := by decide
example : Fintype.card (DBonacciName 2 4) = 8 := by decide

example : Fintype.card (DBonacciName 3 0) = 1 := by decide
example : Fintype.card (DBonacciName 3 1) = 2 := by decide
example : Fintype.card (DBonacciName 3 2) = 4 := by decide
example : Fintype.card (DBonacciName 3 3) = 7 := by decide
example : Fintype.card (DBonacciName 3 4) = 13 := by decide

example : Fintype.card (DBonacciName 4 0) = 1 := by decide
example : Fintype.card (DBonacciName 4 1) = 2 := by decide
example : Fintype.card (DBonacciName 4 2) = 4 := by decide
example : Fintype.card (DBonacciName 4 3) = 8 := by decide
example : Fintype.card (DBonacciName 4 4) = 15 := by decide

/-- The order-three specialization satisfies the frozen Tribonacci recurrence. -/
theorem dbonacci_three_add_three (n : Nat) :
    dbonacci 3 (n + 3) =
      dbonacci 3 (n + 2) + dbonacci 3 (n + 1) + dbonacci 3 n := by
  match n with
  | 0 => norm_num [dbonacci_add_two_of_lt]
  | 1 => norm_num [dbonacci_add_two_of_lt]
  | n + 2 =>
      rw [show n + 2 + 3 = n + 3 + 2 by omega,
        dbonacci_add_two_of_le 3 (n + 3) (by omega),
        Finset.sum_fin_eq_sum_range]
      norm_num [Finset.sum_range_succ]
      ac_rfl

/-- The order-two specialization satisfies the Fibonacci recurrence. -/
theorem dbonacci_two_add_two (n : Nat) :
    dbonacci 2 (n + 2) = dbonacci 2 n + dbonacci 2 (n + 1) := by
  match n with
  | 0 => norm_num [dbonacci_add_two_of_lt]
  | 1 => norm_num [dbonacci_add_two_of_lt]
  | n + 2 =>
      rw [dbonacci_add_two_of_le 2 (n + 2) (by omega),
        Finset.sum_fin_eq_sum_range]
      norm_num [Finset.sum_range_succ]

/-- The general sequence has the frozen Tribonacci sequence as its order-three specialization. -/
theorem dbonacci_three_eq_tribonacci (n : Nat) :
    dbonacci 3 n = D5.S0.Tower.Tribonacci.Names.tribonacci n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      match n with
      | 0 => norm_num [D5.S0.Tower.Tribonacci.Names.tribonacci]
      | 1 => norm_num [D5.S0.Tower.Tribonacci.Names.tribonacci]
      | 2 => norm_num [dbonacci_add_two_of_lt,
          D5.S0.Tower.Tribonacci.Names.tribonacci]
      | n + 3 =>
          rw [dbonacci_three_add_three n,
            D5.S0.Tower.Tribonacci.Names.tribonacci_add_three n,
            ih (n + 2) (by omega), ih (n + 1) (by omega), ih n (by omega)]

/-- The order-two specialization is mathlib's Fibonacci sequence. -/
theorem dbonacci_two_eq_fib (n : Nat) : dbonacci 2 n = Nat.fib n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      match n with
      | 0 => norm_num
      | 1 => norm_num
      | n + 2 =>
          rw [dbonacci_two_add_two n, Nat.fib_add_two,
            ih n (by omega), ih (n + 1) (by omega)]

end D5.S0.Tower.DBonacci.Names
