/- GID: D5/S3/Quantum/QuantumChannels/FockAttenuator/TwoCopyEnvironment
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/FockAttenuator/TwoCopyEnvironment
   mirror-E: none(waiver:exact-environment-compression)
   anchors: []
   utility: none
   digest: Actual balanced rotation of the two-copy two-photon environment. -/

import D5.S3.Quantum.QuantumChannels.FockAttenuator.CompletedCoefficientOperator

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder ENNReal NNReal
set_option backward.isDefEq.respectTransparency false

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
    calc
      _ = ((Real.sqrt (1 / 2 : ℝ) ^ 2 : ℝ) : ℂ) := (Complex.ofReal_pow _ _).symm
      _ = ((1 / 2 : ℝ) : ℂ) := congrArg Complex.ofReal balanced_square
      _ = _ := by norm_num
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
    simp [fockPair, tensor, e, lp.single_apply, ← neg_smul, neg_div]
  by_cases h4 : n = 4
  · subst n
    simp [fockPair, tensor, e, lp.single_apply]
  simp [fockPair, tensor, e, lp.single_apply, h0, h2, h4]

private theorem real_scaled_rankOne (c : ℝ) (v : H) :
    InnerProductSpace.rankOne ℂ ((c : ℂ) • v) ((c : ℂ) • v) =
      ((c ^ 2 : ℝ) : ℂ) • InnerProductSpace.rankOne ℂ v v := by
  apply ContinuousLinearMap.ext
  intro x
  have hconj : (starRingEnd ℂ) (c : ℂ) = (c : ℂ) := Complex.conj_ofReal c
  simp only [InnerProductSpace.rankOne_apply, inner_smul_left,
    hconj, ContinuousLinearMap.smul_apply, smul_smul,
    Complex.ofReal_pow]
  congr 1
  ring

/-- The actual center marginal has precisely the three weights used by the
two-copy swap compression. There is no input vector in this computation. -/
theorem environment_marginal :
    purePartialTrace rotatedEnvironment =
      (3 / 8 : ℂ) • InnerProductSpace.rankOne ℂ (e 0) (e 0) +
      (1 / 4 : ℂ) • InnerProductSpace.rankOne ℂ (e 2) (e 2) +
      (3 / 8 : ℂ) • InnerProductSpace.rankOne ℂ (e 4) (e 4) := by
  change (∑' n : ℕ, InnerProductSpace.rankOne ℂ
    (rotatedEnvironment n) (rotatedEnvironment n)) = _
  rw [tsum_eq_sum (s := ({0, 2, 4} : Finset ℕ)) (fun n hn => by
    have h0 : n ≠ 0 := fun h => hn (by simp [h])
    have h2 : n ≠ 2 := fun h => hn (by simp [h])
    have h4 : n ≠ 4 := fun h => hn (by simp [h])
    simp [environment_slice, h0, h2, h4])]
  rw [Finset.sum_insert (by decide : (0 : ℕ) ∉ ({2, 4} : Finset ℕ)),
    Finset.sum_insert (by decide : (2 : ℕ) ∉ ({4} : Finset ℕ)),
    Finset.sum_singleton]
  have h0 : rotatedEnvironment 0 = ((Real.sqrt 6 / 4 : ℝ) : ℂ) • e 4 := by
    simp [environment_slice]
  have h2 : rotatedEnvironment 2 = ((-1 / 2 : ℝ) : ℂ) • e 2 := by
    norm_num [environment_slice]
  have h4 : rotatedEnvironment 4 = ((Real.sqrt 6 / 4 : ℝ) : ℂ) • e 0 := by
    simp [environment_slice]
  have hc : (Real.sqrt 6 / 4 : ℝ) ^ 2 = 3 / 8 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [h0, h2, h4, real_scaled_rankOne, real_scaled_rankOne,
    real_scaled_rankOne, hc]
  norm_num
  abel

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
    norm_num [map_div₀, map_ofNat]
    ring
  rw [hform]
  simp only [RCLike.ofReal_re]
  have hb := lp.sum_rpow_le_norm_rpow (p := (2 : ℝ≥0∞))
    (by norm_num) x ({0, 2, 4} : Finset ℕ)
  norm_num [ENNReal.toReal_ofNat, Real.rpow_two] at hb
  constructor
  · rfl
  · change 0 ≤ (3 / 8 * ‖x‖ ^ 2 - 3 / 8 * ‖x 0‖ ^ 2 -
      1 / 4 * ‖x 2‖ ^ 2 - 3 / 8 * ‖x 4‖ ^ 2 : ℝ)
    nlinarith [sq_nonneg ‖x 2‖]

#print axioms rotated_environment_expansion
#print axioms environment_marginal
#print axioms environment_marginal_le

end D5.S3.Quantum.QuantumChannels.FockAttenuator.TwoCopyEnvironment
