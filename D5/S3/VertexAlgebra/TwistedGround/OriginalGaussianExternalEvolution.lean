/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEvolution
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEvolution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual radial rank-one evolution of the literal external square resolvent. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadial

/-! The full square resolvent includes its identity contribution at every external mode. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Topology ENNReal
open Filter
namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEvolution
open OriginalGaussianMatrix OriginalGaussianResolvent OriginalGaussianWeightedResolvent
open OriginalGaussianAllIndexResolvent OriginalGaussianDifferentiation
open OriginalGaussianExternalResolvent OriginalGaussianExternalFrequency
open OriginalGaussianBilinearTranspose OriginalGaussianExternalDisplacement
open OriginalGaussianExternalRadial
open OriginalGaussianExternalMoments

lemma square_half {z : ℂ} (hz : ‖z‖ < 1) :
    squareResolvent z = (1 / 2 : ℂ) • (resolvent z + oppositeResolvent z) := by
  rw [(signed_square_factorization hz).1, (signed_square_factorization hz).2]
  have he : (1 + operator z) * squareResolvent z +
      (1 - operator z) * squareResolvent z = (2 : ℂ) • squareResolvent z := by
    rw [two_smul]
    noncomm_ring
  rw [he, smul_smul]
  norm_num

lemma opposite_bilinear_transpose {z : ℂ} (hz : ‖z‖ < 1) (x y : H) :
    sourceBilinearFunctional x (oppositeResolvent z y) =
      sourceBilinearFunctional (oppositeResolvent z x) y := by
  have he (k : ℕ) : sourceBilinearFunctional x (((-operator z) ^ k) y) =
      sourceBilinearFunctional (((-operator z) ^ k) x) y := by
    induction k generalizing x y with
    | zero => rfl
    | succ k ih =>
      nth_rw 1 [pow_succ]
      rw [mul_apply_eq_comp, ih]
      nth_rw 1 [pow_succ']
      rw [mul_apply_eq_comp]
      simp only [neg_apply, map_neg]
      rw [operator_bilinear_transpose hz]
      rw [sourceBilinearFunctional_comm (-(operator z) (((-operator z) ^ k) x)) y, map_neg]
      rw [sourceBilinearFunctional_comm]
  have hs : Summable (fun k : ℕ => (-operator z) ^ k) :=
    summable_geometric_of_norm_lt_one (by simpa using operator_norm_lt_one hz)
  let L := (sourceBilinearFunctional x).comp (ContinuousLinearMap.apply ℂ H y)
  let M := (sourceBilinearFunctional y).comp (ContinuousLinearMap.apply ℂ H x)
  change L (∑' k : ℕ, (-operator z) ^ k) = _
  rw [L.map_tsum hs]
  have hm : (∑' k : ℕ, L ((-operator z) ^ k)) = ∑' k : ℕ, M ((-operator z) ^ k) := by
    apply tsum_congr
    intro k
    exact (he k).trans (sourceBilinearFunctional_comm _ _)
  rw [hm, ← M.map_tsum hs]
  exact sourceBilinearFunctional_comm _ _

private lemma opposite_hasDerivAt {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt oppositeResolvent
      (-(oppositeResolvent z * operatorDerivative z * oppositeResolvent z)) z := by
  have hV := (opposite_differentiable hz).hasDerivAt
  have hprod := ((hasDerivAt_const z (1 : H →L[ℂ] H)).add
    (hasDerivAt_operator hz)).mul hV
  have hunit (w : ℂ) (hw : ‖w‖ < 1) : (1 + operator w) * oppositeResolvent w = 1 := by
    simpa only [oppositeResolvent, sub_neg_eq_add] using
      (summable_geometric_of_norm_lt_one
        (by simpa using operator_norm_lt_one hw : ‖-operator w‖ < 1)).one_sub_mul_tsum_pow
  have he := hprod.congr_of_eventuallyEq (show
      (fun w : ℂ => (1 : H →L[ℂ] H)) =ᶠ[𝓝 z]
        (fun w => (1 + operator w) * oppositeResolvent w) from by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with w hw
    exact (hunit w hw).symm)
  have hd := he.unique (hasDerivAt_const z (1 : H →L[ℂ] H))
  have hv : oppositeResolvent z * (1 + operator z) = 1 := by
    simpa only [oppositeResolvent, sub_neg_eq_add] using
      (summable_geometric_of_norm_lt_one
        (by simpa using operator_norm_lt_one hz : ‖-operator z‖ < 1)).tsum_pow_mul_one_sub
  have ht := congrArg (fun A : H →L[ℂ] H => oppositeResolvent z * A) hd
  simp only [zero_add, Pi.add_apply, mul_add, mul_zero, ← mul_assoc, hv, one_mul] at ht
  apply hV.congr_deriv
  exact eq_neg_of_add_eq_zero_right ht

private lemma radial_square_derivative {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt (fun u : ℝ => squareResolvent (Real.sqrt u : ℂ))
      ((1 / 2 : ℂ) •
        (resolvent (Real.sqrt r : ℂ) * radialOperatorDerivative r *
          resolvent (Real.sqrt r : ℂ) -
        oppositeResolvent (Real.sqrt r : ℂ) * radialOperatorDerivative r *
          oppositeResolvent (Real.sqrt r : ℂ))) r := by
  have hR := (hasDerivAt_resolvent (radial_norm_lt_one hr1)).scomp r
    (Real.hasDerivAt_sqrt hr.ne').ofReal_comp
  have hV := (opposite_hasDerivAt (radial_norm_lt_one hr1)).scomp r
    (Real.hasDerivAt_sqrt hr.ne').ofReal_comp
  have h := (hR.add hV).const_smul (1 / 2 : ℂ)
  have he : (fun u : ℝ => squareResolvent (Real.sqrt u : ℂ)) =ᶠ[𝓝 r]
      (fun u : ℝ => (1 / 2 : ℂ) •
        (resolvent (Real.sqrt u : ℂ) + oppositeResolvent (Real.sqrt u : ℂ))) := by
    filter_upwards [isOpen_Iio.mem_nhds hr1] with u hu
    exact square_half (radial_norm_lt_one hu)
  apply (h.congr_of_eventuallyEq he).congr_deriv
  simp only [radialOperatorDerivative, smul_add, smul_neg, smul_smul,
    Algebra.smul_mul_assoc, Algebra.mul_smul_comm, sub_eq_add_neg]

/-- Radial evolution of the literal all-mode T, including its original identity term. -/
theorem externalT_radial_equation (out : Bool) (p : ℕ) (out' : Bool) (q : ℕ)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt (fun u : ℝ => externalT out p out' q (Real.sqrt u : ℂ))
      ((modeFrequency out p (fun e k => externalT e k out' q (Real.sqrt r : ℂ)) +
        modeFrequency out' q (fun e k => externalT out p e k (Real.sqrt r : ℂ)) +
        (1 - (r : ℂ)) / 2 *
          (sourceJetMoment out p r * sourceJetMoment out' q r -
            sourceMoment out p r * sourceMoment out' q r)) / (2 * (r : ℂ))) r := by
  let z : ℂ := Real.sqrt r
  let X := externalVector out p z
  let Y := externalVector out' q z
  let DX := frequencyVector out p z
  let DY := frequencyVector out' q z
  let w := weightedSource r hr.le hr1
  let Kd := radialOperatorDerivative r
  let Rd := resolvent z * Kd * resolvent z
  let Vd := oppositeResolvent z * Kd * oppositeResolvent z
  let Sd := (1 / 2 : ℂ) • (Rd - Vd)
  have hz : ‖z‖ < 1 := radial_norm_lt_one hr1
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hX := hasDerivAt_radial_externalVector out p hr hr1
  have hY := hasDerivAt_radial_externalVector out' q hr hr1
  have hS := radial_square_derivative hr hr1
  have hSreal := (ContinuousLinearMap.restrictScalarsL ℂ H H ℝ ℝ).hasFDerivAt.comp_hasDerivAt r hS
  have hSY := hSreal.clm_apply hY
  have hd := hX.star.inner ℂ hSY
  have he : (fun u : ℝ => externalT out p out' q (Real.sqrt u : ℂ)) =ᶠ[𝓝 r]
      (fun u : ℝ => sourceBilinearFunctional (externalVector out p (Real.sqrt u : ℂ))
        (squareResolvent (Real.sqrt u : ℂ) (externalVector out' q (Real.sqrt u : ℂ)))) := by
    filter_upwards [isOpen_Iio.mem_nhds hr1] with u hu
    exact (external_contractions_explicit out p out' q (radial_norm_lt_one hu)).2.2.2.1.symm
  apply (hd.congr_of_eventuallyEq he).congr_deriv
  change sourceBilinearFunctional X (Sd Y + squareResolvent z
      ((1 / (2 * (r : ℂ))) • DY)) +
      sourceBilinearFunctional ((1 / (2 * (r : ℂ))) • DX) (squareResolvent z Y) = _
  have hj (e : Bool) (k : ℕ) (f : Bool) (l : ℕ) :
      sourceBilinearFunctional (externalVector e k z)
        (squareResolvent z (externalVector f l z)) = externalT e k f l z :=
    (external_contractions_explicit e k f l hz).2.2.2.1
  have hl : sourceBilinearFunctional DX (squareResolvent z Y) =
      modeFrequency out p (fun e k => externalT e k out' q z) := by
    dsimp only [DX, frequencyVector]
    rw [sourceBilinearFunctional_smul_left,
      sourceBilinearFunctional_comm, map_sub]
    simp only [sourceBilinearFunctional_comm _ (externalVector _ _ z), hj, Y, modeFrequency]
  have hright : sourceBilinearFunctional X (squareResolvent z DY) =
      modeFrequency out' q (fun e k => externalT out p e k z) := by
    dsimp only [DY, frequencyVector]
    simp only [map_smul, map_sub, smul_eq_mul, X, hj, modeFrequency]
  have hp := congrArg (fun A : H →L[ℂ] H =>
    sourceBilinearFunctional X (resolvent z (A (resolvent z Y))))
      (radial_operator_derivative_rankOne hr hr1)
  have hm := congrArg (fun A : H →L[ℂ] H =>
    sourceBilinearFunctional X (oppositeResolvent z (A (oppositeResolvent z Y))))
      (radial_operator_derivative_rankOne hr hr1)
  simp only [smul_apply, ContinuousLinearMap.smulRight_apply,
    map_smul, smul_eq_mul] at hp hm
  change (r : ℂ) * sourceBilinearFunctional X (Rd Y) =
    (1 / 2 : ℂ) * (sourceBilinearFunctional w (resolvent z Y) *
      sourceBilinearFunctional X (resolvent z w)) at hp
  change (r : ℂ) * sourceBilinearFunctional X (Vd Y) =
    (1 / 2 : ℂ) * (sourceBilinearFunctional w (oppositeResolvent z Y) *
      sourceBilinearFunctional X (oppositeResolvent z w)) at hm
  rw [resolvent_bilinear_transpose hz, sourceBilinearFunctional_comm _ Y] at hp
  rw [opposite_bilinear_transpose hz, sourceBilinearFunctional_comm _ Y] at hm
  have hscale : 4 * (r : ℂ) * sourceBilinearFunctional X (Sd Y) =
      sourceBilinearFunctional X (resolvent z w) *
        sourceBilinearFunctional Y (resolvent z w) -
      sourceBilinearFunctional X (oppositeResolvent z w) *
        sourceBilinearFunctional Y (oppositeResolvent z w) := by
    change 4 * (r : ℂ) * sourceBilinearFunctional X
      ((1 / 2 : ℂ) • (Rd Y - Vd Y)) = _
    rw [map_smul, map_sub]
    simp only [smul_eq_mul]
    linear_combination 2 * (hp - hm)
  rw [(source_moment_pairings out p hr hr1).1,
    (source_moment_pairings out p hr hr1).2,
    (source_moment_pairings out' q hr hr1).1,
    (source_moment_pairings out' q hr hr1).2] at hscale
  have hc : (Real.sqrt (1 - r) : ℂ) ^ 2 = 1 - (r : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by linarith : 0 ≤ 1 - r)
  rw [map_add, map_smul, map_smul, sourceBilinearFunctional_smul_left,
    hl, hright]
  simp only [smul_eq_mul]
  apply (eq_div_iff (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hr0)).mpr
  rw [← hc]
  field_simp [hr0]
  linear_combination hscale

/-- The negative input-zero row is fixed by the actual vector v(-,0) = -w. -/
theorem external_negative_zero_boundary (out : Bool) (p : ℕ)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    externalJ false 0 out p (Real.sqrt r : ℂ) =
      (Real.sqrt (1 - r) : ℂ) *
        (sourceJetMoment out p r - sourceMoment out p r) / 2 ∧
    externalT false 0 out p (Real.sqrt r : ℂ) =
      (Real.sqrt (1 - r) : ℂ) *
        (sourceJetMoment out p r + sourceMoment out p r) / 2 := by
  let z : ℂ := Real.sqrt r
  let Y := externalVector out p z
  let w := weightedSource r hr.le hr1
  have hz : ‖z‖ < 1 := radial_norm_lt_one hr1
  have hw : externalVector false 0 z = -w := by
    rw [externalVector_negative_zero hz, sourceFamily_one_eq_weightedSource hr.le hr1]
  have hR : sourceBilinearFunctional w (resolvent z Y) =
      -(Real.sqrt (1 - r) : ℂ) * sourceJetMoment out p r := by
    rw [resolvent_bilinear_transpose hz, sourceBilinearFunctional_comm]
    exact (source_moment_pairings out p hr hr1).2
  have hV : sourceBilinearFunctional w (oppositeResolvent z Y) =
      -(Real.sqrt (1 - r) : ℂ) * sourceMoment out p r := by
    rw [opposite_bilinear_transpose hz, sourceBilinearFunctional_comm]
    exact (source_moment_pairings out p hr hr1).1
  have h := external_contractions_explicit false 0 out p hz
  constructor
  · rw [← h.2.2.1, hw]
    change sourceBilinearFunctional (-w) (oddResolvent z Y) = _
    rw [sourceBilinearFunctional_comm, map_neg,
      sourceBilinearFunctional_comm, odd_eq_half_difference hz]
    simp only [smul_apply, ContinuousLinearMap.sub_apply,
      map_smul, map_sub, smul_eq_mul, hR, hV]
    ring
  · rw [← h.2.2.2.1, hw]
    change sourceBilinearFunctional (-w) (squareResolvent z Y) = _
    rw [sourceBilinearFunctional_comm, map_neg,
      sourceBilinearFunctional_comm, square_half hz]
    simp only [smul_apply, ContinuousLinearMap.add_apply,
      map_smul, map_add, smul_eq_mul, hR, hV]
    ring

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEvolution
