/- GID: D5/S1/Depth/ContinuedFractions/FiniteTerminationApproximation
   generality: G
   mirror-B: D5/B/S1/Depth/ContinuedFractions/FiniteTerminationApproximation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Rational finite errors vanish; irrational errors stay positive but approach zero. -/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Topology.Order.LiminfLimsup

/- Library-search audit trail (2026-09-02):
   * Repository searches for finite denominator minima, nearest-integer errors, and irrational
     liminf approximation found no theorem exposing all three clauses.
   * Pinned Mathlib has no exact whole-statement theorem.  The `round_le` law validates the
     nearest-integer encoding; the proof directly applies Dirichlet approximation,
     finite-infimum lemmas, `tendsto_one_div_add_atTop_nhds_zero_nat`, and liminf of a limit. -/

namespace D5.S1.Depth.ContinuedFractions.FiniteTerminationApproximation

/-- The error in approximating `q * x` by its nearest integer. -/
noncomputable def integerApproximationError (q : ℕ) (x : ℝ) : ℝ :=
  |(q : ℝ) * x - (round ((q : ℝ) * x) : ℝ)|

/-- The least nearest-integer error among the positive denominators at most `Q`.
The zero branch totalizes the source quantity outside its positive-level domain. -/
noncomputable def finiteApproximationError (Q : ℕ) (x : ℝ) : ℝ :=
  if hQ : 0 < Q then
    (Finset.Icc 1 Q).inf'
      ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hQ⟩⟩
      (fun q => integerApproximationError q x)
  else 0

/-- A real is rational exactly when its finite approximation error vanishes at some positive
level.  For an irrational real every positive finite-level error is strict, although the errors
converge to zero and hence have liminf zero. -/
theorem finite_termination_and_infinite_approximation (x : ℝ) :
    (x ∈ Set.range ((↑) : ℚ → ℝ) ↔
      ∃ Q : ℕ, 0 < Q ∧ finiteApproximationError Q x = 0) ∧
    (Irrational x → ∀ Q : ℕ, 0 < Q → 0 < finiteApproximationError Q x) ∧
    Filter.liminf (fun Q : ℕ => finiteApproximationError Q x) Filter.atTop = 0 := by
  have error_nonneg (Q : ℕ) : 0 ≤ finiteApproximationError Q x := by
    by_cases hQ : 0 < Q
    · rw [finiteApproximationError, dif_pos hQ]
      apply Finset.le_inf' ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hQ⟩⟩
      intro q _
      exact abs_nonneg _
    · simp [finiteApproximationError, hQ]
  have error_pos_of_irrational (hx : Irrational x) (Q : ℕ) (hQ : 0 < Q) :
      0 < finiteApproximationError Q x := by
    have hset : (Finset.Icc 1 Q).Nonempty :=
      ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hQ⟩⟩
    obtain ⟨q, hq, hmin⟩ :=
      Finset.exists_mem_eq_inf' hset (fun q => integerApproximationError q x)
    have hqpos : 0 < q := (Finset.mem_Icc.mp hq).1
    have hne : integerApproximationError q x ≠ 0 := by
      intro hzero
      have hproduct : (q : ℝ) * x = (round ((q : ℝ) * x) : ℝ) := by
        exact sub_eq_zero.mp (abs_eq_zero.mp hzero)
      have hqne : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hqpos.ne'
      apply hx.ne_rational (round ((q : ℝ) * x)) (q : ℤ)
      apply (eq_div_iff (by exact_mod_cast hqne)).2
      simpa [mul_comm] using hproduct
    have herror_ne : finiteApproximationError Q x ≠ 0 := by
      rw [finiteApproximationError, dif_pos hQ, hmin]
      exact hne
    exact lt_of_le_of_ne (error_nonneg Q) herror_ne.symm
  have error_le (Q : ℕ) (hQ : 0 < Q) :
      finiteApproximationError Q x ≤ 1 / ((Q : ℝ) + 1) := by
    obtain ⟨q, hqpos, hqle, hqbound⟩ :=
      Real.exists_nat_abs_mul_sub_round_le x hQ
    rw [finiteApproximationError, dif_pos hQ]
    calc
      (Finset.Icc 1 Q).inf'
          ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hQ⟩⟩
          (fun q => integerApproximationError q x)
          ≤ integerApproximationError q x :=
            Finset.inf'_le _ (Finset.mem_Icc.mpr ⟨hqpos, hqle⟩)
      _ ≤ 1 / ((Q : ℝ) + 1) := by
        simpa [integerApproximationError] using hqbound
  have error_tendsto_zero :
      Filter.Tendsto (fun Q : ℕ => finiteApproximationError Q x)
        Filter.atTop (nhds 0) := by
    apply squeeze_zero
    · exact error_nonneg
    · intro Q
      by_cases hQ : 0 < Q
      · exact error_le Q hQ
      · have hQzero : Q = 0 := Nat.eq_zero_of_not_pos hQ
        subst Q
        norm_num [finiteApproximationError]
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
  constructor
  · constructor
    · rintro ⟨r, rfl⟩
      refine ⟨r.den, r.pos, ?_⟩
      apply le_antisymm
      · rw [finiteApproximationError, dif_pos r.pos]
        calc
          (Finset.Icc 1 r.den).inf'
              ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, r.pos⟩⟩
              (fun q => integerApproximationError q (r : ℝ))
              ≤ integerApproximationError r.den (r : ℝ) :=
                Finset.inf'_le _ (Finset.mem_Icc.mpr ⟨r.pos, le_rfl⟩)
          _ = 0 := by
            have hden : (r.den : ℝ) * (r : ℝ) = (r.num : ℝ) := by
              rw [Rat.cast_def]
              field_simp
            simp [integerApproximationError, hden]
      · exact error_nonneg r.den
    · rintro ⟨Q, hQ, hzero⟩
      by_contra hx
      have hpositive := error_pos_of_irrational hx Q hQ
      linarith
  · exact ⟨error_pos_of_irrational, error_tendsto_zero.liminf_eq⟩

#print axioms integerApproximationError
#print axioms finiteApproximationError
#print axioms finite_termination_and_infinite_approximation

end D5.S1.Depth.ContinuedFractions.FiniteTerminationApproximation
