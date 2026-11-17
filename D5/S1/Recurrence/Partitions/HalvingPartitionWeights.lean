/- GID: D5/S1/Recurrence/Partitions/HalvingPartitionWeights
   generality: I
   mirror-B: D5/B/S1/Recurrence/Partitions/HalvingPartitionWeights
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual-list even-predecessor weights and joint dyadic length-weight polynomial. -/

import D5.S1.Recurrence.Partitions.HalvingPartitionProfile

/-! Actual-list weights retain the sum constraint and all terminal repetitions. -/

namespace D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity

/-- Counts precisely the positions where the manuscript digit p-2q+1 equals one.
The equality p=2q is expressed in naturals without truncated subtraction. -/
def evenSteps : ℕ → List ℕ → ℕ
  | _, [] => 0
  | previous, next :: rest =>
      (if previous = 2 * next then 1 else 0) + evenSteps next rest

/-- Exact identification with the manuscript's integer digit, on every step. -/
theorem digit_one_iff (previous next : ℕ) :
    (previous : ℤ) - 2 * next + 1 = 1 ↔ previous = 2 * next := by omega

/-- The manuscript's integer digits, with the virtual predecessor retained. -/
def stepDigits : ℕ → List ℕ → List ℤ
  | _, [] => []
  | previous, next :: rest =>
      ((previous : ℤ) - 2 * next + 1) :: stepDigits next rest

/-- The recursively counted exponent equals the literal number of digit ones. -/
theorem evenSteps_eq_count (previous : ℕ) (parts : List ℕ) :
    evenSteps previous parts = (stepDigits previous parts).count 1 := by
  induction parts generalizing previous with
  | nil => rfl
  | cons next rest ih =>
    simp only [evenSteps, stepDigits, List.count_cons, ih]
    simp only [beq_iff_eq, digit_one_iff]
    split_ifs <;> omega

/-- The source weight is summed over the independently defined actual lists. -/
noncomputable def weightedCount {R : Type*} [CommSemiring R] (t : R) (n : ℕ) : R :=
  ∑ p : SourceLists n, t ^ (stepDigits n p.val).count 1

/-- Length and weight are read from the same actual partition. -/
noncomputable def weightedLengthPolynomial {R : Type*} [CommSemiring R]
    (t : R) (n : ℕ) : Polynomial R :=
  ∑ p : SourceLists n, Polynomial.C (t ^ (stepDigits n p.val).count 1) *
    Polynomial.X ^ p.val.length

private theorem powerWord_steps (m l : ℕ) :
    evenSteps (2 ^ m) (powerWord m l) = min m l := by
  induction l generalizing m with
  | zero => simp [evenSteps, powerWord]
  | succ l ih =>
    cases m with
    | zero =>
      simpa [powerWord, evenSteps] using ih 0
    | succ m =>
      have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; omega
      simp [powerWord, evenSteps, hp, ih, Nat.add_comm]

private theorem oddWord_steps (m j l : ℕ) (hj : j < m) (hl : j ≤ l) :
    evenSteps (2 ^ m + 1) (oddWord m j l) = min (m - j - 1) (l - j - 1) := by
  induction j generalizing m l with
  | zero =>
    cases l with
    | zero => simp [oddWord, evenSteps]
    | succ l =>
      cases m with
      | zero => omega
      | succ m =>
        have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; omega
        have hn : 2 ^ (m + 1) + 1 ≠ 2 * 2 ^ m := by omega
        simp [oddWord, evenSteps, hn, powerWord_steps]
  | succ j ih =>
    cases l with
    | zero => omega
    | succ l =>
      cases m with
      | zero => omega
      | succ m =>
        have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; omega
        have hn : 2 ^ (m + 1) + 1 ≠ 2 * (2 ^ m + 1) := by omega
        simp only [oddWord, evenSteps, if_neg hn, zero_add]
        rw [ih m l (by omega) (by omega)]
        simp only [Nat.succ_sub_succ_eq_sub]

/-- Every code's weight exponent, with the m=2 boundary retained. -/
theorem codeSource_steps (m : ℕ) (hm : 2 ≤ m) (c : DyadicCode m) :
    evenSteps (2 ^ m + 1) (codeSource m hm c).val =
      match c with
      | .inl i => if i = 0 then m - 3 else if i = 1 then m - 2 else m - 1
      | .inr r => m - r.val.val - 2 ^ r.val.val - 2 := by
  change evenSteps (2 ^ m + 1)
    (oddWord m (codeParams m c).2 (codeParams m c).1) = _
  rcases c with i | r
  · fin_cases i
    · by_cases hm2 : m = 2
      · subst m
        norm_num [codeParams, oddWord, evenSteps]
      · change evenSteps (2 ^ m + 1) (oddWord m 2 m) = m - 3
        rw [oddWord_steps m 2 m (by omega) (by omega)]
        simp only [min_self]
        omega
    · change evenSteps (2 ^ m + 1) (oddWord m 1 (m + 1)) = m - 2
      rw [oddWord_steps m 1 (m + 1) (by omega) (by omega)]
      omega
    · change evenSteps (2 ^ m + 1) (oddWord m 0 (m + 2)) = m - 1
      rw [oddWord_steps m 0 (m + 2) (by omega) (by omega)]
      omega
  · have hr := r.prop
    have hp : 0 < (2 : ℕ) ^ r.val.val := by positivity
    simp only [codeParams]
    rw [oddWord_steps m (2 ^ r.val.val + 1) (m - r.val.val) (by omega) (by omega)]
    omega

/-- The complete joint polynomial for all m at least two and every ring parameter. -/
theorem weightedLengthPolynomial_dyadic {R : Type*} [CommRing R]
    (t : R) (m : ℕ) (hm : 2 ≤ m) :
    weightedLengthPolynomial t (2 ^ m + 1) =
      Polynomial.X ^ m * Polynomial.C (t ^ (m - 3)) +
      Polynomial.X ^ (m + 1) * Polynomial.C (t ^ (m - 2)) +
      Polynomial.X ^ (m + 2) * Polynomial.C (t ^ (m - 1)) +
      ∑ r : Threshold m, Polynomial.X ^ (m - r.val.val) *
        Polynomial.C (t ^ (m - r.val.val - 2 ^ r.val.val - 2)) := by
  classical
  unfold weightedLengthPolynomial
  simp only [← evenSteps_eq_count]
  rw [sum_source_dyadic m hm, Fintype.sum_sum_type, Fin.sum_univ_three]
  simp [codeSource_steps, codeSource_length, codeParams]
  ring

/-- The complete dyadic weighted count, before factoring the m=2 endpoint away. -/
theorem weightedCount_dyadic {R : Type*} [CommRing R]
    (t : R) (m : ℕ) (hm : 2 ≤ m) :
    weightedCount t (2 ^ m + 1) =
      t ^ (m - 3) + t ^ (m - 2) + t ^ (m - 1) +
        ∑ r : Threshold m, t ^ (m - r.val.val - 2 ^ r.val.val - 2) := by
  classical
  have he : (weightedLengthPolynomial t (2 ^ m + 1)).eval 1 =
      weightedCount t (2 ^ m + 1) := by
    simp [weightedLengthPolynomial, weightedCount, Polynomial.eval_finsetSum]
  rw [← he, weightedLengthPolynomial_dyadic t m hm]
  simp [Polynomial.eval_finsetSum]

/-- Empty input has exactly the unique empty list and weight one. -/
theorem weightedCount_zero {R : Type*} [CommRing R] (t : R) : weightedCount t 0 = 1 := by
  classical
  have he (p : SourceLists 0) : p.val = [] := by
    exact (Composition.blocks_eq_nil (sourceEquiv 0 p).1).mpr rfl
  have hs : Subsingleton (SourceLists 0) := ⟨fun p q => Subtype.ext ((he p).trans (he q).symm)⟩
  let p : SourceLists 0 := ⟨[], by simp [Follows]⟩
  letI : Unique (SourceLists 0) := ⟨⟨p⟩, fun q => Subsingleton.elim q p⟩
  simp [weightedCount, he, stepDigits]

/-- Weight one recovers the single actual source count in any coefficient ring. -/
theorem weightedCount_one {R : Type*} [CommRing R] (n : ℕ) :
    weightedCount (1 : R) n = (count n : R) := by
  classical
  by_cases hn : n = 0
  · subst n
    rw [weightedCount_zero, result.2.2.2.2.2]
    simp
  · simp [weightedCount, count, Nat.card_eq_fintype_card]

end D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity
