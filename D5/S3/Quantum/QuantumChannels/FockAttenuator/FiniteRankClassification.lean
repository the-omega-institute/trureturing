/- GID: D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteRankClassification
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/FockAttenuator/FiniteRankClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Completed finite-rank characterization for the owner's actual balanced two-photon attenuator. -/

import D5.S3.Quantum.QuantumChannels.FockAttenuator.RankSeparation
import D5.S3.Quantum.QuantumChannels.FockAttenuator.CompletedKernel
import D5.S3.Quantum.QuantumChannels.FockAttenuator.ExponentialPolynomialFock
import D5.S3.Quantum.QuantumChannels.FockAttenuator.Attenuator
import D5.S3.Analytic.Entire.WeightedHankelLowerRank
import D5.S3.Analytic.Entire.PolynomialKernelRank

/-! Cardinal rank statements on the existing balanced two-photon physical channel. -/

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal NNReal

namespace D5.S3.Quantum.QuantumChannels.FockAttenuator.Bargmann
open BeamSplitter DisplacementCovariance Attenuator D5.S3.Analytic.Entire

/-- An actual point-mass ProbabilityVector in the channel's existing domain. -/
def pointMassEnvironment (n : ℕ) : ProbabilityVector where
  weight j := if j = n then 1 else 0
  nonneg j := by split_ifs <;> norm_num
  normalized := hasSum_ite_eq n 1

/-- The channel's double-index ensemble reduces to its actual completed
pure partial trace for a point-mass environment. -/
theorem point_mass_pure_attenuator (η : ℝ) (hη : η ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) (a : Fock) :
    pureAttenuatorOperator η hη (pointMassEnvironment n) a =
      purePartialTrace (beamSplitter η hη (tensor a (lp.single 2 n (1 : ℂ)))) := by
  classical
  let V := beamSplitter η hη (tensor a (lp.single 2 n (1 : ℂ)))
  let v := pureOutputVector η hη (pointMassEnvironment n) a
  have he (q : ℕ × ℕ) : v q = if q.1 = n then V q.2 else 0 := by
    by_cases hq : q.1 = n
    · simp [v, pureOutputVector, pointMassEnvironment, hq, V]
    · simp only [v, pureOutputVector, pointMassEnvironment, if_neg hq,
        Real.sqrt_zero, Complex.ofReal_zero, zero_smul]
  have hV : Summable (fun j : ℕ => ‖V j‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) V).summable
  have hnorm : Summable (fun q : ℕ × ℕ => if q.1 = n then ‖V q.2‖ ^ 2 else 0) := by
    rw [summable_prod_of_nonneg (by
      intro q
      change (0 : ℝ) ≤ if q.1 = n then ‖V q.2‖ ^ 2 else 0
      split_ifs <;> positivity)]
    constructor
    · intro i
      by_cases hi : i = n
      · simpa [hi] using hV
      · simpa only [if_neg hi] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
    · have hrow (i : ℕ) : (∑' j : ℕ, if i = n then ‖V j‖ ^ 2 else 0) =
          if i = n then ∑' j : ℕ, ‖V j‖ ^ 2 else 0 := by
        by_cases hi : i = n <;> simp only [hi, if_true, if_false, tsum_zero]
      simp only [hrow]
      exact (hasSum_ite_eq n _).summable
  have hnormv : Summable (fun q : ℕ × ℕ => ‖v q‖ ^ 2) := by
    simpa only [he, apply_ite norm, norm_zero, ite_pow, zero_pow (by decide : 2 ≠ 0)] using hnorm
  have hR : Summable (fun q : ℕ × ℕ => InnerProductSpace.rankOne ℂ (v q) (v q)) := by
    apply Summable.of_norm
    simpa only [InnerProductSpace.norm_rankOne, ← sq] using hnormv
  change (∑' q : ℕ × ℕ, InnerProductSpace.rankOne ℂ (v q) (v q)) =
    ∑' j : ℕ, InnerProductSpace.rankOne ℂ (V j) (V j)
  rw [hR.tsum_prod]
  have hrow (i : ℕ) :
      (∑' j : ℕ, InnerProductSpace.rankOne ℂ (v (i, j)) (v (i, j))) =
        if i = n then ∑' j : ℕ, InnerProductSpace.rankOne ℂ (V j) (V j) else 0 := by
    by_cases hi : i = n <;> simp only [he, hi, if_true, if_false,
      map_zero, ContinuousLinearMap.zero_apply, tsum_zero]
  simp only [hrow, tsum_ite_eq]

theorem balanced_kernel_separated_iff (a : Fock)
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) :
    SeparatedLE k (kernel (beamSplitter (1 / 2) hHalf
      (tensor a (lp.single 2 2 (1 : ℂ))))) ↔
        SeparatedLE k (weightedHankel (transform a)) := by
  let s : ℂ := Real.sqrt 2
  have hs : s ^ 2 = 2 := by
    dsimp only [s]
    norm_cast
    exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide : 2 ≠ 0)] at hs
    norm_num at hs
  constructor
  · intro h
    have h' := (h.linear_precomp s s).const_mul s
    convert h' using 1
    funext z w
    rw [balanced_two_photon_kernel]
    change (z - w) ^ 2 * transform a (z + w) =
      s * (transform a ((s * z + s * w) / s) * (s * w - s * z) ^ 2 / (2 * s))
    rw [show (s * z + s * w) / s = z + w by field_simp]
    rw [show s * w - s * z = s * (w - z) by ring, mul_pow, hs]
    field_simp
    <;> ring
  · intro h
    have h' := (h.linear_precomp s⁻¹ s⁻¹).const_mul s⁻¹
    convert h' using 1
    funext z w
    rw [balanced_two_photon_kernel]
    change transform a ((z + w) / s) * (w - z) ^ 2 / (2 * s) =
      s⁻¹ * ((s⁻¹ * z - s⁻¹ * w) ^ 2 * transform a (s⁻¹ * z + s⁻¹ * w))
    rw [show s⁻¹ * z + s⁻¹ * w = (z + w) / s by ring]
    rw [show s⁻¹ * z - s⁻¹ * w = (z - w) / s by ring, div_pow, hs]
    ring

theorem balanced_kernel_finite_separated_iff (a : Fock)
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    FiniteSeparated (kernel (beamSplitter (1 / 2) hHalf
      (tensor a (lp.single 2 2 (1 : ℂ))))) ↔
        FiniteSeparated (weightedHankel (transform a)) := by
  exact exists_congr (fun k => balanced_kernel_separated_iff a hHalf k)

/-- Every nonzero completed Fock input has actual output range dimension
at least three. No finite-rank or finite-support assumption is imposed. -/
theorem actual_rank_lower_bound (a : Fock) (ha : a ≠ 0)
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    (3 : Cardinal) ≤ rangeRank (pureAttenuatorOperator (1 / 2) hHalf
      (pointMassEnvironment 2) a) := by
  have hf0 : transform a ≠ 0 := by
    intro h
    apply ha
    apply injective
    funext z
    rw [congrFun h z]
    simp only [Pi.zero_apply, transform, inner_zero_right]
  have hnot := not_separated_two_weighted_hankel (entire a).continuous hf0
  have hr : ¬ rangeRank (pureAttenuatorOperator (1 / 2) hHalf
      (pointMassEnvironment 2) a) ≤ (2 : Cardinal) := by
    intro h
    rw [point_mass_pure_attenuator] at h
    have hsep := (reduced_rank_le_iff_separated _ 2).mp h
    exact hnot ((balanced_kernel_separated_iff a hHalf 2).mp hsep)
  calc
    (3 : Cardinal) = ((2 : ℕ) : Cardinal)+1 := by norm_num
    _ ≤ _ := Cardinal.natCast_add_one_le_iff.mpr (lt_of_not_ge hr)

/-- Both proposed equality profiles attain actual Cardinal range rank three.
This is the sufficiency direction; the converse requires a separate
classification of the finite exponential-polynomial blocks. -/
theorem actual_rank_three_of_profile (a : Fock) (ha : a ≠ 0)
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (hprofile : ∃ c α : ℂ, c ≠ 0 ∧
      (transform a = (fun z => c * Complex.exp (α * z)) ∨
        ∃ β : ℂ, transform a =
          (fun z => c * Complex.exp (α * z) * (z - β) ^ 2))) :
    rangeRank (pureAttenuatorOperator (1 / 2) hHalf
      (pointMassEnvironment 2) a) = (3 : Cardinal) := by
  apply le_antisymm
  · rw [point_mass_pure_attenuator]
    apply (reduced_rank_le_iff_separated _ 3).mpr
    apply (balanced_kernel_separated_iff a hHalf 3).mpr
    obtain ⟨c, α, _, h | ⟨β, h⟩⟩ := hprofile
    · rw [h]
      exact separated_three_exponential c α
    · rw [h]
      exact separated_three_exponential_square c α β
  · exact actual_rank_lower_bound a ha hHalf

/-- Finite cardinal rank of the actual physical operator is equivalent to
an exponential-polynomial Bargmann transform, with arbitrary infinite
support and arbitrary complex coefficients. No rank-three or entropy claim
is included in this theorem. -/
theorem actual_finite_rank_iff_exponential_polynomial (a : Fock)
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    (∃ k : ℕ, rangeRank (pureAttenuatorOperator (1 / 2) hHalf
      (pointMassEnvironment 2) a) ≤ (k : Cardinal)) ↔
        ExponentialPolynomial (transform a) := by
  rw [point_mass_pure_attenuator]
  simp_rw [reduced_rank_le_iff_separated]
  change FiniteSeparated (kernel (beamSplitter (1 / 2) hHalf
    (tensor a (lp.single 2 2 (1 : ℂ))))) ↔ _
  rw [balanced_kernel_finite_separated_iff]
  exact finite_weighted_separation_iff_exponential_polynomial (entire a)

/-- Exact Cardinal range-rank-three classification for every nonzero
completed Fock input of the actual balanced two-photon attenuator. -/
theorem actual_rank_three_iff_profile (a : Fock) (ha : a ≠ 0)
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    rangeRank (pureAttenuatorOperator (1 / 2) hHalf (pointMassEnvironment 2) a) =
        (3 : Cardinal) ↔
      ∃ c α : ℂ, c ≠ 0 ∧
        (transform a = (fun z => c*Complex.exp (α*z)) ∨
          ∃ β : ℂ, transform a = (fun z => c*Complex.exp (α*z)*(z-β)^2)) := by
  constructor
  · intro hrank
    have hf0 : transform a ≠ 0 := by
      intro h
      apply ha
      apply injective
      funext z
      rw [congrFun h z]
      simp only [Pi.zero_apply, transform, inner_zero_right]
    apply (separated_three_iff_profile (entire a) hf0).mp
    apply (balanced_kernel_separated_iff a hHalf 3).mp
    apply (reduced_rank_le_iff_separated _ 3).mp
    rw [← point_mass_pure_attenuator, hrank]
    exact le_rfl
  · exact actual_rank_three_of_profile a ha hHalf

#print axioms point_mass_pure_attenuator
#print axioms actual_rank_lower_bound
#print axioms actual_rank_three_of_profile
#print axioms actual_finite_rank_iff_exponential_polynomial
#print axioms actual_rank_three_iff_profile

end D5.S3.Quantum.QuantumChannels.FockAttenuator.Bargmann
