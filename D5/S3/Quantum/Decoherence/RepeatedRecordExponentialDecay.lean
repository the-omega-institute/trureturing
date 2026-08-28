/- GID: D5/S3/Quantum/Decoherence/RepeatedRecordExponentialDecay
   generality: G
   mirror-B: D5/B/S3/Quantum/Decoherence/RepeatedRecordExponentialDecay
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Repeated finite records contract cross-class coherence at the uniform Gram rate. -/

import D5.S3.Quantum.Decoherence.EnvironmentMarginalChannel

/- Library-search audit trail (2026-08-27):
   * `SingletonRecordClassicality.recordGram` and `recordChannel` are the canonical
     arbitrary finite record primitives and are reused directly.
   * `EnvironmentMarginalChannel.environment_marginal_channel` connects this channel
     to the controlled-record environment marginal but does not iterate it.
   * `LedgerEnvironmentBridge.finite_record_channel_is_iterated_decoherence` and
     `QubitWitnesses.phaseDampingIterate_apply` cover only the two-dimensional case.
   * Pinned Mathlib supplies `Matrix.frobenius_norm_def` and the scoped Frobenius
     instances, but no complete record-class pinching contraction theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate Matrix.Norms.Frobenius

namespace D5.S3.Quantum.Decoherence.RepeatedRecordExponentialDecay

open D5.S3.Quantum.FixedAlgebra.SingletonRecordClassicality

/-- The projector onto the system addresses carrying one environment record vector. -/
noncomputable def recordClassProjector {d e : Nat}
    (record : Fin d -> Fin e -> ℂ) (label : Set.range record) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun i j => if i = j ∧ record i = label.1 then 1 else 0

private theorem record_pinching_apply {d e : Nat}
    (record : Fin d -> Fin e -> ℂ)
    (rho : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    (∑ label : Set.range record,
        recordClassProjector record label * rho * recordClassProjector record label) i j =
      if record i = record j then rho i j else 0 := by
  classical
  have hProjectorEntry (label : Set.range record) :
      (recordClassProjector record label * rho * recordClassProjector record label) i j =
        if record i = label.1 ∧ record j = label.1 then rho i j else 0 := by
    have hLeft (M : Matrix (Fin d) (Fin d) ℂ) (row column : Fin d) :
        (recordClassProjector record label * M) row column =
          if record row = label.1 then M row column else 0 := by
      rw [Matrix.mul_apply]
      by_cases hrow : record row = label.1
      · rw [if_pos hrow]
        calc
          (∑ k, recordClassProjector record label row k * M k column) =
              recordClassProjector record label row row * M row column := by
            apply Finset.sum_eq_single row
            · intro k _ hk
              have hrk : row ≠ k := fun hrk => hk hrk.symm
              simp [recordClassProjector, hrk]
            · simp
          _ = M row column := by simp [recordClassProjector, hrow]
      · rw [if_neg hrow]
        apply Finset.sum_eq_zero
        intro k _
        by_cases hrk : row = k
        · subst k
          simp [recordClassProjector, hrow]
        · simp [recordClassProjector, hrk]
    have hRight (M : Matrix (Fin d) (Fin d) ℂ) (row column : Fin d) :
        (M * recordClassProjector record label) row column =
          if record column = label.1 then M row column else 0 := by
      rw [Matrix.mul_apply]
      by_cases hcolumn : record column = label.1
      · rw [if_pos hcolumn]
        calc
          (∑ k, M row k * recordClassProjector record label k column) =
              M row column * recordClassProjector record label column column := by
            apply Finset.sum_eq_single column
            · intro k _ hk
              simp [recordClassProjector, hk]
            · simp
          _ = M row column := by simp [recordClassProjector, hcolumn]
      · rw [if_neg hcolumn]
        apply Finset.sum_eq_zero
        intro k _
        by_cases hkc : k = column
        · subst k
          simp [recordClassProjector, hcolumn]
        · simp [recordClassProjector, hkc]
    rw [hRight, hLeft]
    by_cases hi : record i = label.1 <;>
      by_cases hj : record j = label.1 <;> simp [hi, hj]
  simp only [Matrix.sum_apply, hProjectorEntry]
  by_cases hij : record i = record j
  · rw [if_pos hij]
    let target : Set.range record := ⟨record i, ⟨i, rfl⟩⟩
    calc
      (∑ label : Set.range record,
          if record i = label.1 ∧ record j = label.1 then rho i j else 0) =
          (if record i = target.1 ∧ record j = target.1 then rho i j else 0) := by
        apply Finset.sum_eq_single target
        · intro label _ hlabel
          rw [if_neg]
          intro hboth
          apply hlabel
          apply Subtype.ext
          exact hboth.1.symm
        · simp
      _ = rho i j := by simp [target, hij]
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro label _
    rw [if_neg]
    intro hboth
    exact hij (hboth.1.trans hboth.2.symm)

private theorem record_channel_iterate_apply {d e : Nat}
    (record : Fin d -> Fin e -> ℂ) (N : Nat)
    (rho : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    ((recordChannel record)^[N] rho) i j =
      recordGram record i j ^ N * rho i j := by
  induction N generalizing rho with
  | zero => simp
  | succ N ih =>
      rw [Function.iterate_succ_apply, ih]
      change recordGram record i j ^ N * (recordGram record i j * rho i j) = _
      rw [pow_succ]
      ring

private theorem gram_self_of_normalized {d e : Nat}
    (record : Fin d -> Fin e -> ℂ)
    (hNormalized : ∀ i, ∑ a, ‖record i a‖ ^ 2 = 1) (i : Fin d) :
    recordGram record i i = 1 := by
  rw [recordGram]
  calc
    ∑ a, record i a * star (record i a) =
        ∑ a, (‖record i a‖ ^ 2 : ℂ) := by
      apply Finset.sum_congr rfl
      intro a ha
      change record i a * (starRingEnd ℂ) (record i a) = _
      rw [RCLike.mul_conj]
      norm_cast
    _ = (↑(∑ a, ‖record i a‖ ^ 2) : ℂ) := by norm_cast
    _ = 1 := by rw [hNormalized i]; norm_num

private theorem record_channel_frobenius_contraction {d e : Nat}
    (record : Fin d -> Fin e -> ℂ)
    (hNormalized : ∀ i, ∑ a, ‖record i a‖ ^ 2 = 1)
    (q : Set.Ico (0 : ℝ) 1)
    (hBound : ∀ i j, record i ≠ record j -> ‖recordGram record i j‖ ≤ (q : ℝ))
    (N : Nat) (rho : Matrix (Fin d) (Fin d) ℂ) :
    ‖(recordChannel record)^[N] rho -
        ∑ label : Set.range record,
          recordClassProjector record label * rho * recordClassProjector record label‖ ≤
      (q : ℝ) ^ N *
        ‖rho - ∑ label : Set.range record,
          recordClassProjector record label * rho * recordClassProjector record label‖ := by
  rw [Matrix.frobenius_norm_def, Matrix.frobenius_norm_def]
  have hq0 : 0 ≤ (q : ℝ) := q.2.1
  have hsum :
      (∑ i, ∑ j,
          ‖(((recordChannel record)^[N] rho -
            ∑ label : Set.range record,
              recordClassProjector record label * rho *
                recordClassProjector record label) i j)‖ ^ (2 : ℝ)) ≤
        ((q : ℝ) ^ N) ^ 2 *
          (∑ i, ∑ j,
            ‖((rho - ∑ label : Set.range record,
              recordClassProjector record label * rho *
                recordClassProjector record label) i j)‖ ^ (2 : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    change
      ‖((recordChannel record)^[N] rho) i j -
          (∑ label : Set.range record,
            recordClassProjector record label * rho *
              recordClassProjector record label) i j‖ ^ 2 ≤
        ((q : ℝ) ^ N) ^ 2 *
          ‖rho i j - (∑ label : Set.range record,
            recordClassProjector record label * rho *
              recordClassProjector record label) i j‖ ^ 2
    rw [record_channel_iterate_apply, record_pinching_apply]
    by_cases hij : record i = record j
    · rw [if_pos hij]
      have hGram : recordGram record i j = 1 := by
        simpa [recordGram, hij] using
          gram_self_of_normalized record hNormalized i
      simp [hGram]
    · rw [if_neg hij]
      simp only [sub_zero]
      rw [norm_mul, norm_pow]
      have hpower : ‖recordGram record i j‖ ^ N ≤ (q : ℝ) ^ N :=
        pow_le_pow_left₀ (norm_nonneg _) (hBound i j hij) N
      have hentry :
          ‖recordGram record i j‖ ^ N * ‖rho i j‖ ≤
            (q : ℝ) ^ N * ‖rho i j‖ :=
        mul_le_mul_of_nonneg_right hpower (norm_nonneg _)
      rw [Real.rpow_two, Real.rpow_two]
      calc
        (‖recordGram record i j‖ ^ N * ‖rho i j‖) ^ 2 ≤
            ((q : ℝ) ^ N * ‖rho i j‖) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hentry 2
        _ = ((q : ℝ) ^ N) ^ 2 * ‖rho i j‖ ^ 2 := by ring
  calc
    (∑ i, ∑ j,
        ‖(((recordChannel record)^[N] rho -
          ∑ label : Set.range record,
            recordClassProjector record label * rho *
              recordClassProjector record label) i j)‖ ^ (2 : ℝ)) ^
        (1 / 2 : ℝ) ≤
      (((q : ℝ) ^ N) ^ 2 *
        (∑ i, ∑ j,
          ‖((rho - ∑ label : Set.range record,
            recordClassProjector record label * rho *
              recordClassProjector record label) i j)‖ ^ (2 : ℝ))) ^
          (1 / 2 : ℝ) := by
      exact Real.rpow_le_rpow (by positivity) hsum (by norm_num)
    _ = (q : ℝ) ^ N *
        (∑ i, ∑ j,
          ‖((rho - ∑ label : Set.range record,
            recordClassProjector record label * rho *
              recordClassProjector record label) i j)‖ ^ (2 : ℝ)) ^
          (1 / 2 : ℝ) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
      have hqpow : 0 ≤ (q : ℝ) ^ N := pow_nonneg hq0 N
      rw [show (((q : ℝ) ^ N) ^ 2) ^ (1 / 2 : ℝ) = (q : ℝ) ^ N by
        rw [← Real.sqrt_eq_rpow]
        exact Real.sqrt_sq hqpow]

/- A two-address copied record witnesses simultaneous normalization and a zero
cross-class Gram bound, so the theorem's hypotheses are jointly inhabited. -/
example :
    ∃ (record : Fin 2 -> Fin 2 -> ℂ) (q : Set.Ico (0 : ℝ) 1),
      (∀ i, ∑ a, ‖record i a‖ ^ 2 = 1) ∧
      (∀ i j, record i ≠ record j -> ‖recordGram record i j‖ ≤ (q : ℝ)) := by
  let record : Fin 2 -> Fin 2 -> ℂ := fun i a => if i = a then 1 else 0
  let q : Set.Ico (0 : ℝ) 1 := ⟨0, by constructor <;> norm_num⟩
  refine ⟨record, q, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [record, Fin.sum_univ_two]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [record, recordGram, q] at hij ⊢

/-- Repeating one normalized finite environment record multiplies each matrix
entry by the corresponding Gram coefficient to the repetition count. The
canonical sum of record-class projectors retains exactly the within-class
entries, and all remaining Hilbert--Schmidt coherence contracts at rate `q^N`. -/
theorem repeated_record_exponential_decay {d e : Nat}
    (record : Fin d -> Fin e -> ℂ)
    (hNormalized : ∀ i, ∑ a, ‖record i a‖ ^ 2 = 1)
    (q : Set.Ico (0 : ℝ) 1)
    (hBound : ∀ i j, record i ≠ record j -> ‖recordGram record i j‖ ≤ (q : ℝ)) :
    let pinching := fun rho : Matrix (Fin d) (Fin d) ℂ =>
      ∑ label : Set.range record,
        recordClassProjector record label * rho * recordClassProjector record label
    (∀ N rho i j,
        ((recordChannel record)^[N] rho) i j =
          recordGram record i j ^ N * rho i j) ∧
      (∀ rho i j,
        pinching rho i j = if record i = record j then rho i j else 0) ∧
      ∀ N rho,
        ‖(recordChannel record)^[N] rho - pinching rho‖ ≤
          (q : ℝ) ^ N * ‖rho - pinching rho‖ := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · exact record_channel_iterate_apply record
  · exact record_pinching_apply record
  · exact record_channel_frobenius_contraction record hNormalized q hBound

#print axioms repeated_record_exponential_decay

end D5.S3.Quantum.Decoherence.RepeatedRecordExponentialDecay
