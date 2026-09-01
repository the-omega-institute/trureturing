/- GID: D5/S0/Tower/DBonacci/Values
   generality: I
   mirror-B: D5/B/S0/Tower/DBonacci/Values
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: D-bonacci names acquire ordered real values from the Perron root. -/

import D5.S0.Tower.DBonacci.Names
import D5.S0.Tower.DBonacci.PerronRoot
import Mathlib.Data.List.OfFn

namespace D5.S0.Tower.DBonacci.Values

open D5.S0.Tower.DBonacci.Names
open D5.S0.Tower.DBonacci.PerronRoot

/-- The real value of a Boolean word, with its first digit weighted by `beta_d^-1`. -/
noncomputable def dbonacciWordValue (d Q : Nat) (word : Fin Q -> Bool) : Real :=
  ∑ i, if word i then (dbonacciPerronRoot d)⁻¹ ^ (i.1 + 1) else 0

/-- Read a d-bonacci-admissible word as a real base-`beta_d` expansion. -/
noncomputable def dbonacciNameValue (d Q : Nat) (name : DBonacciName d Q) : Real :=
  dbonacciWordValue d Q name.1

theorem dbonacciWordValue_cons (d Q : Nat) (head : Bool) (tail : Fin Q -> Bool) :
    dbonacciWordValue d (Q + 1) (Fin.cons head tail) =
      (if head then (dbonacciPerronRoot d)⁻¹ else 0) +
        (dbonacciPerronRoot d)⁻¹ * dbonacciWordValue d Q tail := by
  unfold dbonacciWordValue
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, zero_add, pow_one]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : tail i
  · simp only [hi, ↓reduceIte]
    rw [Fin.val_succ]
    ring_nf
  · simp [hi]

/-- Order three uses exactly the frozen Tribonacci word-value function. -/
theorem dbonacciWordValue_three_eq_tribonacciWordValue (Q : Nat)
    (word : Fin Q -> Bool) :
    dbonacciWordValue 3 Q word =
      D5.S0.Tower.Tribonacci.Values.tribonacciWordValue Q word := by
  unfold dbonacciWordValue D5.S0.Tower.Tribonacci.Values.tribonacciWordValue
  rw [dbonacciPerronRoot_three_eq_tribonacciConstant]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : word i
  · simp only [hi, ↓reduceIte]
    rw [zpow_neg, zpow_natCast]
    exact inv_pow _ _
  · simp [hi]

/-- Explicit common-word bridge between the general and frozen order-three name values. -/
theorem dbonacciNameValue_three_eq_tribonacciNameValue (Q : Nat)
    (dname : DBonacciName 3 Q)
    (tname : D5.S0.Tower.Tribonacci.Names.TribonacciName Q)
    (hword : dname.1 = tname.1) :
    dbonacciNameValue 3 Q dname =
      D5.S0.Tower.Tribonacci.Values.tribonacciNameValue Q tname := by
  unfold dbonacciNameValue D5.S0.Tower.Tribonacci.Values.tribonacciNameValue
  rw [dbonacciWordValue_three_eq_tribonacciWordValue, hword]

/-- Prefix-order enumeration of a bounded-run layer. -/
noncomputable def boundedRunIndexEquiv :
    (maxTrue fuel Q : Nat) ->
      Fin (Fintype.card (BoundedRunName maxTrue fuel Q)) ≃
        BoundedRunName maxTrue fuel Q
  | maxTrue, fuel, 0 => Fintype.equivOfCardEq (Fintype.card_fin _)
  | maxTrue, 0, q + 1 =>
      (finCongr (bounded_run_name_card_zero maxTrue q)).trans
        ((boundedRunIndexEquiv maxTrue maxTrue q).trans
          (boundedRunNameZeroEquiv maxTrue q).symm)
  | maxTrue, fuel + 1, q + 1 =>
      (finCongr (bounded_run_name_card_succ maxTrue fuel q)).trans
        ((finSumFinEquiv
          (m := Fintype.card (BoundedRunName maxTrue maxTrue q))
          (n := Fintype.card (BoundedRunName maxTrue fuel q))).symm.trans
            ((Equiv.sumCongr (boundedRunIndexEquiv maxTrue maxTrue q)
              (boundedRunIndexEquiv maxTrue fuel q)).trans
                (boundedRunNameSplitEquiv maxTrue fuel q).symm))
termination_by _ _ Q => Q

/-- The recursive prefix enumeration transferred to the frozen d-bonacci cardinality. -/
noncomputable def dbonacciIndexEquiv :
    (d Q : Nat) -> Fin (dbonacci d (Q + 2)) ≃ DBonacciName d Q
  | 0, Q => Fintype.equivOfCardEq (by
      rw [Fintype.card_fin, dbonacci_name_card])
  | maxTrue + 1, Q =>
      have hcount : dbonacci (maxTrue + 1) (Q + 2) =
          Fintype.card (BoundedRunName maxTrue maxTrue Q) :=
        (dbonacci_name_card (maxTrue + 1) Q).symm.trans
          (dbonacci_name_card_eq_bounded maxTrue Q)
      (finCongr hcount).trans
        ((boundedRunIndexEquiv maxTrue maxTrue Q).trans
          (dbonacciNameBoundedEquiv maxTrue Q).symm)

/-- The value at a bounded-run prefix-order index. -/
noncomputable def boundedIndexedNameValue (maxTrue fuel Q : Nat)
    (i : Fin (Fintype.card (BoundedRunName maxTrue fuel Q))) : Real :=
  dbonacciWordValue (maxTrue + 1) Q (boundedRunIndexEquiv maxTrue fuel Q i).1

/-- The value of the `i`th d-bonacci name in canonical prefix order. -/
noncomputable def indexedNameValue (d Q : Nat) (i : Fin (dbonacci d (Q + 2))) : Real :=
  dbonacciNameValue d Q (dbonacciIndexEquiv d Q i)

theorem indexedNameValue_succ_eq_bounded (maxTrue Q : Nat)
    (i : Fin (dbonacci (maxTrue + 1) (Q + 2))) :
    indexedNameValue (maxTrue + 1) Q i =
      boundedIndexedNameValue maxTrue maxTrue Q
        (Fin.cast
          ((dbonacci_name_card (maxTrue + 1) Q).symm.trans
            (dbonacci_name_card_eq_bounded maxTrue Q)) i) := by
  unfold indexedNameValue dbonacciNameValue boundedIndexedNameValue
  simp only [dbonacciIndexEquiv, Equiv.trans_apply, finCongr_apply]
  have hword :
      ((dbonacciNameBoundedEquiv maxTrue Q).symm
        (boundedRunIndexEquiv maxTrue maxTrue Q
          (Fin.cast
            ((dbonacci_name_card (maxTrue + 1) Q).symm.trans
              (dbonacci_name_card_eq_bounded maxTrue Q)) i))).1 =
        (boundedRunIndexEquiv maxTrue maxTrue Q
          (Fin.cast
            ((dbonacci_name_card (maxTrue + 1) Q).symm.trans
              (dbonacci_name_card_eq_bounded maxTrue Q)) i)).1 := rfl
  rw [hword]

/-- The all-false word is accepted at every run budget. -/
theorem runAdmissible_all_false (maxTrue fuel Q : Nat) :
    runAdmissible maxTrue fuel Q (fun _ => false) = true := by
  induction Q generalizing fuel with
  | zero => simp [runAdmissible]
  | succ Q ih =>
      cases fuel <;> simp only [runAdmissible, Bool.false_eq_true, ↓reduceIte]
      · rw [show Fin.tail (fun _ : Fin (Q + 1) => false) =
            (fun _ : Fin Q => false) by funext i; simp [Fin.tail]]
        exact ih maxTrue
      · rw [show Fin.tail (fun _ : Fin (Q + 1) => false) =
            (fun _ : Fin Q => false) by funext i; simp [Fin.tail]]
        exact ih maxTrue

/-- Every bounded-run layer contains the all-false word. -/
theorem bounded_run_level_pos (maxTrue fuel Q : Nat) :
    0 < Fintype.card (BoundedRunName maxTrue fuel Q) := by
  rw [Fintype.card_pos_iff]
  exact ⟨⟨fun _ => false, runAdmissible_all_false maxTrue fuel Q⟩⟩

/-- The general d-bonacci layer is nonempty for positive order. -/
theorem dbonacci_level_pos (d Q : Nat) (hd : 0 < d) : 0 < dbonacci d (Q + 2) := by
  rw [← dbonacci_name_card]
  exact Fintype.card_pos_iff.mpr ⟨⟨fun _ => false, by
    cases d with
    | zero => omega
    | succ maxTrue =>
        change runAdmissible maxTrue maxTrue Q (fun _ => false) = true
        exact runAdmissible_all_false maxTrue maxTrue Q⟩⟩

@[simp] theorem boundedIndexedNameValue_level_zero (maxTrue fuel : Nat) :
    boundedIndexedNameValue maxTrue fuel 0 ⟨0, bounded_run_level_pos _ _ _⟩ = 0 := by
  unfold boundedIndexedNameValue dbonacciWordValue
  exact Finset.sum_empty

theorem boundedIndexedNameValue_zero_budget (maxTrue q : Nat)
    (i : Fin (Fintype.card (BoundedRunName maxTrue 0 (q + 1)))) :
    boundedIndexedNameValue maxTrue 0 (q + 1) i =
      (dbonacciPerronRoot (maxTrue + 1))⁻¹ *
        boundedIndexedNameValue maxTrue maxTrue q
          (Fin.cast (bounded_run_name_card_zero maxTrue q) i) := by
  unfold boundedIndexedNameValue
  simp only [boundedRunIndexEquiv, Equiv.trans_apply, finCongr_apply]
  have hword :
      ((boundedRunNameZeroEquiv maxTrue q).symm
        (boundedRunIndexEquiv maxTrue maxTrue q
          (Fin.cast (bounded_run_name_card_zero maxTrue q) i))).1 =
        Fin.cons false (boundedRunIndexEquiv maxTrue maxTrue q
          (Fin.cast (bounded_run_name_card_zero maxTrue q) i)).1 := rfl
  rw [hword]
  rw [dbonacciWordValue_cons]
  simp

theorem boundedIndexedNameValue_lower (maxTrue fuel q : Nat)
    (i : Fin (Fintype.card (BoundedRunName maxTrue (fuel + 1) (q + 1))))
    (hi : i.1 < Fintype.card (BoundedRunName maxTrue maxTrue q)) :
    boundedIndexedNameValue maxTrue (fuel + 1) (q + 1) i =
      (dbonacciPerronRoot (maxTrue + 1))⁻¹ *
        boundedIndexedNameValue maxTrue maxTrue q ⟨i.1, hi⟩ := by
  unfold boundedIndexedNameValue
  have hcast : Fin.cast (bounded_run_name_card_succ maxTrue fuel q) i =
      Fin.castAdd (Fintype.card (BoundedRunName maxTrue fuel q)) ⟨i.1, hi⟩ := by
    apply Fin.ext
    simp
  simp only [boundedRunIndexEquiv, Equiv.trans_apply, finCongr_apply]
  rw [hcast, finSumFinEquiv_symm_apply_castAdd]
  simp only [Equiv.sumCongr_apply, Sum.map_inl]
  have hword :
      ((boundedRunNameSplitEquiv maxTrue fuel q).symm
        (Sum.inl (boundedRunIndexEquiv maxTrue maxTrue q ⟨i.1, hi⟩))).1 =
        Fin.cons false (boundedRunIndexEquiv maxTrue maxTrue q ⟨i.1, hi⟩).1 := rfl
  rw [hword]
  rw [dbonacciWordValue_cons]
  simp

theorem boundedIndexedNameValue_upper (maxTrue fuel q : Nat)
    (i : Fin (Fintype.card (BoundedRunName maxTrue (fuel + 1) (q + 1))))
    (hi : Fintype.card (BoundedRunName maxTrue maxTrue q) ≤ i.1) :
    boundedIndexedNameValue maxTrue (fuel + 1) (q + 1) i =
      (dbonacciPerronRoot (maxTrue + 1))⁻¹ +
        (dbonacciPerronRoot (maxTrue + 1))⁻¹ *
          boundedIndexedNameValue maxTrue fuel q
            ⟨i.1 - Fintype.card (BoundedRunName maxTrue maxTrue q), by
              have htotal : i.1 <
                  Fintype.card (BoundedRunName maxTrue maxTrue q) +
                    Fintype.card (BoundedRunName maxTrue fuel q) := by
                calc
                  i.1 < Fintype.card
                      (BoundedRunName maxTrue (fuel + 1) (q + 1)) := i.2
                  _ = _ := bounded_run_name_card_succ maxTrue fuel q
              omega⟩ := by
  let j : Fin (Fintype.card (BoundedRunName maxTrue fuel q)) :=
    ⟨i.1 - Fintype.card (BoundedRunName maxTrue maxTrue q), by
      have htotal : i.1 <
          Fintype.card (BoundedRunName maxTrue maxTrue q) +
            Fintype.card (BoundedRunName maxTrue fuel q) := by
        calc
          i.1 < Fintype.card
              (BoundedRunName maxTrue (fuel + 1) (q + 1)) := i.2
          _ = _ := bounded_run_name_card_succ maxTrue fuel q
      omega⟩
  unfold boundedIndexedNameValue
  have hcast : Fin.cast (bounded_run_name_card_succ maxTrue fuel q) i =
      Fin.natAdd (Fintype.card (BoundedRunName maxTrue maxTrue q)) j := by
    apply Fin.ext
    simp [j]
    omega
  simp only [boundedRunIndexEquiv, Equiv.trans_apply, finCongr_apply]
  rw [hcast, finSumFinEquiv_symm_apply_natAdd]
  simp only [Equiv.sumCongr_apply, Sum.map_inr]
  have hword :
      ((boundedRunNameSplitEquiv maxTrue fuel q).symm
        (Sum.inr (boundedRunIndexEquiv maxTrue fuel q j))).1 =
        Fin.cons true (boundedRunIndexEquiv maxTrue fuel q j).1 := rfl
  rw [hword]
  rw [dbonacciWordValue_cons]
  simp [j]

/-- The first value in every bounded-run prefix layer is zero. -/
theorem boundedIndexedNameValue_zero (maxTrue fuel Q : Nat) :
    boundedIndexedNameValue maxTrue fuel Q
      ⟨0, bounded_run_level_pos maxTrue fuel Q⟩ = 0 := by
  induction Q generalizing fuel with
  | zero => exact boundedIndexedNameValue_level_zero maxTrue fuel
  | succ Q ih =>
      cases fuel with
      | zero =>
          rw [boundedIndexedNameValue_zero_budget]
          have hindex :
              Fin.cast (bounded_run_name_card_zero maxTrue Q)
                  ⟨0, bounded_run_level_pos maxTrue 0 (Q + 1)⟩ =
                ⟨0, bounded_run_level_pos maxTrue maxTrue Q⟩ := by
            apply Fin.ext
            simp
          rw [hindex, ih maxTrue]
          ring
      | succ fuel =>
          rw [boundedIndexedNameValue_lower maxTrue fuel Q
            ⟨0, bounded_run_level_pos maxTrue (fuel + 1) (Q + 1)⟩
            (bounded_run_level_pos maxTrue maxTrue Q)]
          have hindex :
              (⟨0, bounded_run_level_pos maxTrue maxTrue Q⟩ :
                Fin (Fintype.card (BoundedRunName maxTrue maxTrue Q))) =
              ⟨0, bounded_run_level_pos maxTrue maxTrue Q⟩ := by
            apply Fin.ext
            simp
          rw [hindex, ih maxTrue]
          ring

end D5.S0.Tower.DBonacci.Values
