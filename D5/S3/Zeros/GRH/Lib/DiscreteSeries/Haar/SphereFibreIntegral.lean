/- GID: D5/S3/Zeros/GRH/Lib/DiscreteSeries/Haar/SphereFibreIntegral
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/DiscreteSeries/Haar/SphereFibreIntegral
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.DiscreteSeries.Haar.SphereFibreIntegral. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/DiscreteSeries/Haar/SphereFibreIntegral.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.Haar.HaarColumnChart
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Haar measure of U(J) in Cayley coordinates, volume of U(n), polynomial volume growth
(known result; see Lib.DiscreteSeries.Haar.RegularRepL2).

This file: Integrating one row and column of the Cayley density gives sphere volume. -/

open Matrix MeasureTheory Real Complex Fintype Haar Subtype

/-- For J = 1, integrating Cayley's density `cayleyDensity` over the coordinates θ of row and column
k₀, the complementary block η being fixed, gives 2πⁿ/(n−1)! times the density of η in size
n−1; both sides are divided by 2πⁿa/(n−1)!, a > 0. -/
lemma lintegral_cayleyDensity_skewColumnEquiv {n} [Fintype n] (k₀ : n) η {a} (_ : 0 < a) : ∫⁻ θ,
  .ofReal (cayleyDensity 1 (skewColumnEquiv k₀ (θ, η)) / (sphereDensity (card n) 1 * a)) =
  .ofReal (cayleyDensity 1 η / a) := by
  obtain ⟨⟨k⟩⟩ := Nat.exists_eq_add_of_lt (@card_pos _ _ ⟨k₀⟩), det_cayleyDenom_one_ne_zero η
  choose x e using (canLift.1 (star _) <| neg_eq_zero.2 <|
    IsHermitian.im_star_dotProduct_mulVec_self (skewAdjoint.negISMul ⟨_,
    conjTranspose_skewOfReal η⟩).2 ·)
  erw [lintegral_prod_symm, lintegral_eq_det_mul (ofReal 2 • _) (by simpa), lintegral_congr fun w ↦
    ?e, lintegral_mul_const, lintegral_inv_add_rpow one_pos,
    ← @doublingGamma_eq_Gamma (2 * k.succ - 1)]
  case' e => rw [lintegral_congr fun _ ↦ ?p, lintegral_mul_const (.ofReal
    (rpow ‖-I / 2 * (cayleyDenom 1 η).det‖ _ / _)), lintegral_norm_add_rpow ⟨-x w, (_ + _) * 2⟩,
    mul_rpow, rpow_neg_eq_inv_rpow, mul_left_comm, ENNReal.ofReal_mul, mul_assoc]
  case' p => erw [← ENNReal.ofReal_mul, mul_div, ← mul_rpow, ← norm_mul, ← mul_assoc]; simp [
    cayleyDensity, rpow_neg, rpow_mul, -norm_mul, -Complex.norm_mul, -Nat.cast_add]; congr
  any_goals first | fun_prop | finiteness | simp [*] <;> grind
  convert det_updateCol_sum _ k₀ (val.extend w 1) ▸ twoBlockTriangular_det₀ _ (· = k₀)
    (Subtype.forall'.2 _); aesop
  repeat simp [*, toSquareBlockProp, entrywise, mk_eq_add_mul_I,
    sum_eq_add_sum_subtype_ne _ k₀, ← Finset.mul_sum, conj_mul', mul_assoc, mul_comm (w _), default,
    cayleyDenom, sub_mul, val_inj] <;> grind [I_sq]
  simp (disch := positivity) [← ENNReal.ofReal_mul, doublingGamma, ← add_sub, rpow_add,
    ← Real.Gamma_nat_eq_factorial, *, rpow_neg, field, two_mul, mul_pow]; ring
