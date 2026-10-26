/- GID: D5/S3/Quantum/QuantumChannels/FockAttenuator/TwoCopyEnvironment
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/FockAttenuator/TwoCopyEnvironment
   mirror-E: none(waiver:exact-environment-compression)
   anchors: []
   utility: none
   digest: Actual balanced rotation of the two-copy two-photon environment. -/

import D5.S3.Quantum.QuantumChannels.FockAttenuator.CompletedCoefficientOperator

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder

namespace D5.S3.Quantum.QuantumChannels.FockAttenuator.TwoCopyEnvironment
open BeamSplitter DisplacementCovariance CompletedCoefficientOperator

private def e (n : ℕ) : H := lp.single 2 n 1

/-- The environment state after the actual center/difference rotation. -/
def rotatedEnvironment : H2 :=
  beamSplitter (1 / 2) (by norm_num) (fockPair 2 2)

private theorem balanced_square : Real.sqrt (1 / 2 : ℝ) ^ 2 = 1 / 2 :=
  Real.sq_sqrt (by norm_num)

private theorem sqrt_twenty_four : Real.sqrt (24 : ℝ) = 2 * Real.sqrt 6 := by
  rw [show (24 : ℝ) = 4 * 6 by norm_num, Real.sqrt_mul (by norm_num)]
  norm_num

/-- This finite expansion is inside the completed beam-splitter space, with the
same sign convention as `beamUnitary_fock`. -/
theorem rotated_environment_expansion :
    rotatedEnvironment = ((Real.sqrt 6 / 4 : ℝ) : ℂ) • fockPair 4 0 -
      (1 / 2 : ℂ) • fockPair 2 2 +
      ((Real.sqrt 6 / 4 : ℝ) : ℂ) • fockPair 0 4 := by
  unfold rotatedEnvironment beamSplitter
  rw [beamUnitary_fock]
  norm_num [fockExpansion, Fin.sum_univ_succ, Nat.choose]
  have h2 : (Real.sqrt (1 / 2 : ℝ) : ℂ) ^ 2 = 1 / 2 := by
    exact_mod_cast balanced_square
  have hf2 : (Real.sqrt (2 : ℝ) : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hfne : (Real.sqrt (2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  simp only [sqrt_twenty_four]
  push_cast
  match_scalars <;> field_simp
  all_goals ring_nf
  all_goals simp_all only [show (4 : ℕ) = 2 * 2 by omega, pow_mul]
  all_goals norm_num

private theorem environment_slice (n : ℕ) :
    rotatedEnvironment n =
      if n = 0 then ((Real.sqrt 6 / 4 : ℝ) : ℂ) • e 4
      else if n = 2 then (-1 / 2 : ℂ) • e 2
      else if n = 4 then ((Real.sqrt 6 / 4 : ℝ) : ℂ) • e 0
      else 0 := by
  rw [rotated_environment_expansion]
  by_cases h0 : n = 0
  · subst n
    simp [fockPair, tensor, e, lp.single_apply]
  by_cases h2 : n = 2
  · subst n
    simp [fockPair, tensor, e, lp.single_apply]
  by_cases h4 : n = 4
  · subst n
    simp [fockPair, tensor, e, lp.single_apply]
  simp [fockPair, tensor, e, lp.single_apply, h0, h2, h4]

private theorem real_scaled_rankOne (c : ℝ) (v : H) :
    InnerProductSpace.rankOne ℂ ((c : ℂ) • v) ((c : ℂ) • v) =
      ((c ^ 2 : ℝ) : ℂ) • InnerProductSpace.rankOne ℂ v v := by
  ext x
  simp only [InnerProductSpace.rankOne_apply, inner_smul_left,
    Complex.conj_ofReal, ContinuousLinearMap.smul_apply, smul_smul,
    ← Complex.ofReal_pow]
  module

/-- The actual center marginal has precisely the three weights used by the
two-copy swap compression. There is no input vector in this computation. -/
theorem environment_marginal :
    purePartialTrace rotatedEnvironment =
      (3 / 8 : ℂ) • InnerProductSpace.rankOne ℂ (e 0) (e 0) +
      (1 / 4 : ℂ) • InnerProductSpace.rankOne ℂ (e 2) (e 2) +
      (3 / 8 : ℂ) • InnerProductSpace.rankOne ℂ (e 4) (e 4) := by
  unfold purePartialTrace mixture
  rw [tsum_eq_sum (s := ({0, 2, 4} : Finset ℕ)) (fun n hn => by
    have h0 : n ≠ 0 := fun h => hn (by simp [h])
    have h2 : n ≠ 2 := fun h => hn (by simp [h])
    have h4 : n ≠ 4 := fun h => hn (by simp [h])
    simp [environment_slice, h0, h2, h4])]
  norm_num only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    Finset.sum_singleton, environment_slice, ite_true, ite_false]
  rw [show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by norm_num]
  simp only [real_scaled_rankOne]
  have hs : (Real.sqrt (6 : ℝ) : ℂ) ^ 2 = 6 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)
  push_cast
  match_scalars <;> ring_nf
  all_goals simp_all only [hs]
  all_goals norm_num

/-- The compression bound is an operator inequality on the whole completed
one-mode space. The three occupied modes do not impose an input cutoff. -/
theorem environment_marginal_le :
    purePartialTrace rotatedEnvironment ≤
      (3 / 8 : ℂ) • ContinuousLinearMap.id ℂ H := by
  apply ContinuousLinearMap.le_def.mpr
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro x
  have hdiag (n : ℕ) :
      inner ℂ (InnerProductSpace.rankOne ℂ (e n) (e n) x) x =
        (‖x n‖ ^ 2 : ℂ) := by
    simp only [InnerProductSpace.rankOne_apply, inner_smul_left, e,
      lp.inner_single_left, RCLike.inner_apply, map_one, mul_one,
      one_mul, RCLike.conj_mul]
    norm_cast
  have hform :
      inner ℂ (((3 / 8 : ℂ) • ContinuousLinearMap.id ℂ H -
        purePartialTrace rotatedEnvironment) x) x =
      ((3 / 8 * ‖x‖ ^ 2 - 3 / 8 * ‖x 0‖ ^ 2 -
        1 / 4 * ‖x 2‖ ^ 2 - 3 / 8 * ‖x 4‖ ^ 2 : ℝ) : ℂ) := by
    rw [environment_marginal]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      inner_sub_left, inner_add_left, inner_smul_left, hdiag,
      inner_self_eq_norm_sq_to_K]
    push_cast
    norm_num
    ring
  rw [hform]
  have hb := lp.sum_rpow_le_norm_rpow (p := (2 : ℝ≥0∞))
    (by norm_num) x ({0, 2, 4} : Finset ℕ)
  norm_num [ENNReal.toReal_ofNat, Real.rpow_two] at hb
  constructor
  · simp
  · simp only [Complex.ofReal_re]
    nlinarith [sq_nonneg ‖x 2‖]

#print axioms rotated_environment_expansion
#print axioms environment_marginal
#print axioms environment_marginal_le

end D5.S3.Quantum.QuantumChannels.FockAttenuator.TwoCopyEnvironment
