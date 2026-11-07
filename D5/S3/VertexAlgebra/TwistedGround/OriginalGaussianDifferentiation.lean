/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual Gaussian operator, source-family, column, radial rank-one, and negative weighted resolvent derivatives. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianWeightedResolvent
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section
open scoped BigOperators Topology ENNReal
open Filter

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation

open OriginalGaussianMatrix
open OriginalGaussianResolvent
open OriginalGaussianWeightedResolvent
open D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection


/- All sums below are in the original complex H or its bounded-operator algebra.
   The auxiliary j is a coordinate weight on explicitly summable vectors;
   no diagonal frequency map on H is defined. -/

private lemma derivative_shifted_geometric {R : ℝ} (hR : 0 < R) (hR1 : R < 1)
    (j : ℕ) : Summable (fun n : ℕ => (n + 1 : ℝ) ^ j * R ^ n) := by
  have hg := summable_pow_mul_geometric_of_norm_lt_one j (r := R)
    (by simpa [Real.norm_eq_abs, abs_of_pos hR] using hR1)
  have hs := ((summable_nat_add_iff 1).mpr hg).mul_left R⁻¹
  convert hs using 1
  funext n
  simp only [Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp [hR.ne']
  <;> ring

private lemma derivative_pair_majorant {R : ℝ} (hR : 0 < R) (hR1 : R < 1) :
    Summable (fun p : ℕ × ℕ =>
      (((p.1 + 1) + (p.2 + 1) : ℕ) : ℝ) * R ^ (p.1 + p.2)) := by
  have hg := summable_geometric_of_lt_one hR.le hR1
  have hn := derivative_shifted_geometric hR hR1 1
  have h₁ := hn.mul_of_nonneg hg (fun _ => by positivity) (fun _ => by positivity)
  have h₂ := hg.mul_of_nonneg hn (fun _ => by positivity) (fun _ => by positivity)
  convert h₁.add h₂ using 1
  funext p
  simp only [pow_one, Nat.cast_add, Nat.cast_one, pow_add]
  ring

private lemma derivative_term_factor (z : ℂ) (p : ℕ × ℕ) :
    term z p = z ^ ((p.1 + 1) + (p.2 + 1)) • term 1 p := by
  simp only [term, matrixEntry, one_pow, mul_one, smul_smul]
  congr 1
  ring

private lemma derivative_term_coefficient_bound (p : ℕ × ℕ) : ‖term 1 p‖ ≤ 1 := by
  rw [term, norm_smul]
  calc
    _ ≤ ‖matrixEntry 1 (p.1 + 1) (p.2 + 1)‖ * 1 := by
      gcongr
      exact rankOne_norm_le _ _
    _ ≤ 1 := by
      simpa using entry_bound (1 : ℂ) (p.1 + 1) (p.2 + 1) (by omega) (by omega)

private def operatorDerivativeTerm (z : ℂ) (p : ℕ × ℕ) : H →L[ℂ] H :=
  ((((p.1 + 1) + (p.2 + 1) : ℕ) : ℂ) * z ^ (p.1 + p.2 + 1)) • term 1 p

def operatorDerivative (z : ℂ) : H →L[ℂ] H :=
  ∑' p : ℕ × ℕ, operatorDerivativeTerm z p

attribute [-instance] ContinuousLinearMap.addCommGroup
attribute [-instance] ContinuousLinearMap.ring
attribute [-instance] ContinuousLinearMap.toNormedRing
attribute [-instance] ContinuousLinearMap.toNormedAddCommGroup
attribute [-instance] ContinuousLinearMap.toNormedSpace
attribute [-instance] ContinuousLinearMap.toPseudoMetricSpace
attribute [-instance] ContinuousLinearMap.module
attribute [-instance] ContinuousLinearMap.topologicalSpace
attribute [-instance] CStarAlgebra.toNonUnitalCStarAlgebra

private lemma operatorDerivativeTerm_hasDerivAt (p : ℕ × ℕ) (z : ℂ) :
    HasDerivAt (fun ζ : ℂ => term ζ p) (operatorDerivativeTerm z p) z := by
  have he : (p.1 + 1) + (p.2 + 1) - 1 = p.1 + p.2 + 1 := by omega
  convert (hasDerivAt_pow ((p.1 + 1) + (p.2 + 1)) z).smul_const (term 1 p) using 1
  · funext ζ
    exact derivative_term_factor ζ p
  · simp only [operatorDerivativeTerm, he]

private lemma operatorDerivativeTerm_bound {R : ℝ} (hR : 0 < R) (hR1 : R < 1)
    {z : ℂ} (hz : ‖z‖ ≤ R) (p : ℕ × ℕ) :
    ‖operatorDerivativeTerm z p‖ ≤
      (((p.1 + 1) + (p.2 + 1) : ℕ) : ℝ) * R ^ (p.1 + p.2) := by
  have hp : R ^ (p.1 + p.2 + 1) ≤ R ^ (p.1 + p.2) := by
    rw [pow_succ]
    nlinarith [pow_nonneg hR.le (p.1 + p.2)]
  simp only [operatorDerivativeTerm, norm_smul, norm_mul, norm_pow,
    Complex.norm_natCast]
  calc
    _ ≤ (((p.1 + 1) + (p.2 + 1) : ℕ) : ℝ) *
        R ^ (p.1 + p.2 + 1) * 1 := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg z) hz (p.1 + p.2 + 1))
          (Nat.cast_nonneg ((p.1 + 1) + (p.2 + 1))))
        (derivative_term_coefficient_bound p) (norm_nonneg _) (by positivity)
    _ ≤ _ := by
      simpa using mul_le_mul_of_nonneg_left hp
        (Nat.cast_nonneg ((p.1 + 1) + (p.2 + 1)) :
          (0 : ℝ) ≤ (((p.1 + 1) + (p.2 + 1) : ℕ) : ℝ))

private lemma operatorDerivative_summable {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun p : ℕ × ℕ => ‖operatorDerivativeTerm z p‖) := by
  obtain ⟨R, hzR, hR1⟩ := exists_between hz
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg z) hzR
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (operatorDerivativeTerm_bound hR hR1 hzR.le) (derivative_pair_majorant hR hR1)

/-- Complex operator-norm differentiation of the literal signed rank-one sum. -/
theorem hasDerivAt_operator {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt operator (operatorDerivative z) z := by
  obtain ⟨R, hzR, hR1⟩ := exists_between hz
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg z) hzR
  have hm : z ∈ Metric.ball (0 : ℂ) R := by simpa using hzR
  exact hasDerivAt_tsum_of_isPreconnected
    (derivative_pair_majorant hR hR1) Metric.isOpen_ball
    (convex_ball (0 : ℂ) R).isPreconnected
    (fun p ζ _ => operatorDerivativeTerm_hasDerivAt p ζ)
    (fun p ζ hζ => operatorDerivativeTerm_bound hR hR1
      (by simpa using (Metric.mem_ball.mp hζ).le) p)
    hm (term_summable hz).of_norm hm

private def sourceCoefficient (n : ℕ) : H :=
  lp.single 2 n (halfBinomial (n + 1) / (Real.sqrt (n + 1 : ℝ) : ℂ))

private lemma sourceCoefficient_bound (n : ℕ) : ‖sourceCoefficient n‖ ≤ 1 := by
  rw [sourceCoefficient, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  simpa [sourceValue] using sourceValue_bound 1 n

private def sourceFamilyTerm (j : ℕ) (z : ℂ) (n : ℕ) : H :=
  ((n + 1 : ℂ) ^ j * z ^ (n + 1)) • sourceCoefficient n

/-- Entirely specified coordinate-weighted source series, on the original H. -/
def sourceFamily (j : ℕ) (z : ℂ) : H := ∑' n : ℕ, sourceFamilyTerm j z n

private def sourceFamilyDerivativeTerm (j : ℕ) (z : ℂ) (n : ℕ) : H :=
  ((n + 1 : ℂ) ^ (j + 1) * z ^ n) • sourceCoefficient n

def sourceFamilyDerivative (j : ℕ) (z : ℂ) : H :=
  ∑' n : ℕ, sourceFamilyDerivativeTerm j z n

private lemma sourceFamilyTerm_bound (j : ℕ) {R : ℝ} (hR : 0 ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ R) (n : ℕ) :
    ‖sourceFamilyTerm j z n‖ ≤ (n + 1 : ℝ) ^ j * R ^ (n + 1) := by
  have hn : ‖(n + 1 : ℂ)‖ = (n + 1 : ℝ) := by
    exact_mod_cast Complex.norm_natCast (n + 1)
  simp only [sourceFamilyTerm, norm_smul, norm_mul, norm_pow, hn]
  calc
    _ ≤ (n + 1 : ℝ) ^ j * R ^ (n + 1) * 1 := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg z) hz (n + 1)) (by positivity))
        (sourceCoefficient_bound n) (norm_nonneg _) (by positivity)
    _ = _ := mul_one _

private lemma sourceFamilyDerivativeTerm_bound (j : ℕ) {R : ℝ} (hR : 0 ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ R) (n : ℕ) :
    ‖sourceFamilyDerivativeTerm j z n‖ ≤ (n + 1 : ℝ) ^ (j + 1) * R ^ n := by
  have hn : ‖(n + 1 : ℂ)‖ = (n + 1 : ℝ) := by
    exact_mod_cast Complex.norm_natCast (n + 1)
  simp only [sourceFamilyDerivativeTerm, norm_smul, norm_mul, norm_pow, hn]
  calc
    _ ≤ (n + 1 : ℝ) ^ (j + 1) * R ^ n * 1 := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg z) hz n) (by positivity))
        (sourceCoefficient_bound n) (norm_nonneg _) (by positivity)
    _ = _ := mul_one _

private lemma sourceFamily_summable (j : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ‖sourceFamilyTerm j z n‖) := by
  obtain ⟨R, hzR, hR1⟩ := exists_between hz
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg z) hzR
  have hs : Summable (fun n : ℕ => (n + 1 : ℝ) ^ j * R ^ (n + 1)) := by
    simpa only [pow_succ, mul_assoc] using
      (derivative_shifted_geometric hR hR1 j).mul_right R
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (sourceFamilyTerm_bound j hR.le hzR.le) hs

private lemma sourceFamilyDerivative_summable (j : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ‖sourceFamilyDerivativeTerm j z n‖) := by
  obtain ⟨R, hzR, hR1⟩ := exists_between hz
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg z) hzR
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (sourceFamilyDerivativeTerm_bound j hR.le hzR.le)
    (derivative_shifted_geometric hR hR1 (j + 1))

private lemma sourceFamilyTerm_hasDerivAt (j n : ℕ) (z : ℂ) :
    HasDerivAt (fun ζ => sourceFamilyTerm j ζ n)
      (sourceFamilyDerivativeTerm j z n) z := by
  have hd := ((hasDerivAt_pow (n + 1) z).const_mul ((n + 1 : ℂ) ^ j)).smul_const
    (sourceCoefficient n)
  convert hd using 1
  · simp only [sourceFamilyTerm, pow_succ]
  · simp only [sourceFamilyDerivativeTerm, pow_succ, Nat.add_sub_cancel]
    congr 1
    norm_num [Nat.cast_add, Nat.cast_one]
    ring

/-- All coordinate weights needed for v, w, and Dw have genuine norm derivatives. -/
theorem hasDerivAt_sourceFamily (j : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (sourceFamily j) (sourceFamilyDerivative j z) z := by
  obtain ⟨R, hzR, hR1⟩ := exists_between hz
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg z) hzR
  have hm : z ∈ Metric.ball (0 : ℂ) R := by simpa using hzR
  exact hasDerivAt_tsum_of_isPreconnected
    (derivative_shifted_geometric hR hR1 (j + 1)) Metric.isOpen_ball
    (convex_ball (0 : ℂ) R).isPreconnected
    (fun n ζ _ => sourceFamilyTerm_hasDerivAt j n ζ)
    (fun n ζ hζ => sourceFamilyDerivativeTerm_bound j hR.le
      (by simpa using (Metric.mem_ball.mp hζ).le) n)
    hm (sourceFamily_summable j hz).of_norm hm

private lemma sourceFamily_apply (j : ℕ) {z : ℂ} (hz : ‖z‖ < 1) (n : ℕ) :
    sourceFamily j z n = (n + 1 : ℂ) ^ j * halfBinomial (n + 1) * z ^ (n + 1) /
      (Real.sqrt (n + 1 : ℝ) : ℂ) := by
  change (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n)
    (∑' i : ℕ, sourceFamilyTerm j z i) = _
  rw [(lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n).map_tsum
    (sourceFamily_summable j hz).of_norm]
  rw [tsum_eq_single n]
  · change ((n + 1 : ℂ) ^ j * z ^ (n + 1)) * sourceCoefficient n n = _
    rw [sourceCoefficient, lp.single_apply_self]
    ring
  · intro i hi
    change ((i + 1 : ℂ) ^ j * z ^ (i + 1)) * sourceCoefficient i n = 0
    simp [sourceCoefficient, lp.single_apply, hi]

private lemma sourceFamilyDerivative_apply (j : ℕ) {z : ℂ} (hz : ‖z‖ < 1) (n : ℕ) :
    sourceFamilyDerivative j z n =
      (n + 1 : ℂ) ^ (j + 1) * halfBinomial (n + 1) * z ^ n /
        (Real.sqrt (n + 1 : ℝ) : ℂ) := by
  change (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n)
    (∑' i : ℕ, sourceFamilyDerivativeTerm j z i) = _
  rw [(lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n).map_tsum
    (sourceFamilyDerivative_summable j hz).of_norm]
  rw [tsum_eq_single n]
  · change ((n + 1 : ℂ) ^ (j + 1) * z ^ n) * sourceCoefficient n n = _
    rw [sourceCoefficient, lp.single_apply_self]
    ring
  · intro i hi
    change ((i + 1 : ℂ) ^ (j + 1) * z ^ i) * sourceCoefficient i n = 0
    simp [sourceCoefficient, lp.single_apply, hi]

private lemma sourceFamily_frequency_derivative (j : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    z • sourceFamilyDerivative j z = sourceFamily (j + 1) z := by
  ext n
  change z * sourceFamilyDerivative j z n = sourceFamily (j + 1) z n
  rw [sourceFamilyDerivative_apply j hz, sourceFamily_apply (j + 1) hz]
  simp only [pow_succ]
  ring

private lemma sourceFamily_zero_eq_source {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    sourceFamily 0 (Real.sqrt r : ℂ) = source r hr hr1 := by
  ext n
  rw [sourceFamily_apply 0 (radial_norm_lt_one hr1)]
  change _ = sourceValue r n
  simp only [pow_zero, one_mul, sourceValue]

private lemma sourceFamily_one_eq_weightedSource {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    sourceFamily 1 (Real.sqrt r : ℂ) = weightedSource r hr hr1 := by
  ext n
  rw [sourceFamily_apply 1 (radial_norm_lt_one hr1)]
  change _ = (n + 1 : ℂ) * sourceValue r n
  simp only [pow_one, sourceValue]
  ring

private lemma resolvent_eq_ringInverse {z : ℂ} (hz : ‖z‖ < 1) :
    resolvent z = Ring.inverse (1 - operator z) := by
  exact (NormedRing.inverse_one_sub (operator z) (operator_norm_lt_one hz)).symm

/-- Inverse differentiation is obtained from the genuine norm-controlled Neumann unit. -/
theorem hasDerivAt_resolvent {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt resolvent
      (resolvent z * operatorDerivative z * resolvent z) z := by
  let u : (H →L[ℂ] H)ˣ := Units.oneSub (operator z) (operator_norm_lt_one hz)
  have hu : (u : H →L[ℂ] H) = 1 - operator z := Units.val_oneSub _ _
  have hui : ((u⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) = resolvent z := by
    exact (NormedRing.inverse_one_sub (operator z) (operator_norm_lt_one hz)).symm.trans
      (resolvent_eq_ringInverse hz).symm
  have hI :
      HasFDerivAt (Ring.inverse : (H →L[ℂ] H) → H →L[ℂ] H)
        (-ContinuousLinearMap.mulLeftRight ℂ (H →L[ℂ] H)
          (↑(u⁻¹) : H →L[ℂ] H) (↑(u⁻¹) : H →L[ℂ] H)) u :=
    @hasFDerivAt_ringInverse ℂ inferInstance (H →L[ℂ] H)
      CStarAlgebra.toNormedRing inferInstance CStarAlgebra.toNormedAlgebra u
  rw [hu, hui] at hI
  have hd : HasDerivAt (fun ζ : ℂ => Ring.inverse (1 - operator ζ))
      (resolvent z * operatorDerivative z * resolvent z) z := by
    have hc := hI.comp_hasDerivAt z ((hasDerivAt_const z (1 : H →L[ℂ] H)).sub
      (hasDerivAt_operator hz))
    convert hc using 1
    · rfl
    · ext w
      simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply,
        Function.comp_apply, sub_zero, zero_sub, mul_neg, neg_mul, neg_neg]
  apply hd.congr_of_eventuallyEq
  have hU : {ζ : ℂ | ‖ζ‖ < 1} ∈ 𝓝 z :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds hz
  filter_upwards [hU] with ζ hζ
  exact resolvent_eq_ringInverse hζ

def columnSeries (z : ℂ) : H := resolvent z (sourceFamily 0 z)

def columnSeriesDerivative (z : ℂ) : H :=
  (resolvent z * operatorDerivative z * resolvent z) (sourceFamily 0 z) +
    resolvent z (sourceFamilyDerivative 0 z)

theorem hasDerivAt_columnSeries {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt columnSeries (columnSeriesDerivative z) z :=
  (hasDerivAt_resolvent hz).clm_apply (hasDerivAt_sourceFamily 0 hz)

private def radialOperatorDerivative (r : ℝ) : H →L[ℂ] H :=
  ((1 / (2 * Real.sqrt r) : ℝ) : ℂ) • operatorDerivative (Real.sqrt r : ℂ)

private def radialSourceFamily (j : ℕ) (r : ℝ) : H := sourceFamily j (Real.sqrt r : ℂ)

private def radialColumn (r : ℝ) : H := columnSeries (Real.sqrt r : ℂ)

private def radialColumnDerivative (r : ℝ) : H :=
  ((1 / (2 * Real.sqrt r) : ℝ) : ℂ) • columnSeriesDerivative (Real.sqrt r : ℂ)

/-- Original radial operator, with the physical frequencies n+1 unchanged. -/
private lemma radial_source_family_derivative_eq (j : ℕ) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) :
    ((1 / (2 * Real.sqrt r) : ℝ) : ℂ) •
        sourceFamilyDerivative j (Real.sqrt r : ℂ) =
      (1 / (2 * (r : ℂ))) • radialSourceFamily (j + 1) r := by
  have hz : (Real.sqrt r : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hr).ne'
  have hs : (Real.sqrt r : ℂ) ^ 2 = (r : ℂ) := by
    exact_mod_cast Real.sq_sqrt hr.le
  rw [radialSourceFamily, ← sourceFamily_frequency_derivative j (radial_norm_lt_one hr1),
    smul_smul]
  congr 1
  push_cast
  rw [← hs, pow_two]
  field_simp [hz]
  <;> ring

/-- In particular 2r v'=w and 2r w'=Dw, as identities of actual H vectors. -/
private lemma hasDerivAt_radial_sourceFamily (j : ℕ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt (radialSourceFamily j)
      ((1 / (2 * (r : ℂ))) • radialSourceFamily (j + 1) r) r := by
  rw [← radial_source_family_derivative_eq j hr hr1]
  exact (hasDerivAt_sourceFamily j (radial_norm_lt_one hr1)).scomp r
    (Real.hasDerivAt_sqrt hr.ne').ofReal_comp

private lemma radialColumn_eq_column {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    radialColumn r = column r hr.le hr1 := by
  change resolvent (Real.sqrt r : ℂ) (sourceFamily 0 (Real.sqrt r : ℂ)) = _
  rw [sourceFamily_zero_eq_source hr.le hr1]
  ext n
  exact resolvent_column hr hr1 n

private lemma hasDerivAt_radial_column {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt radialColumn (radialColumnDerivative r) r :=
  (hasDerivAt_columnSeries (radial_norm_lt_one hr1)).scomp r
    (Real.hasDerivAt_sqrt hr.ne').ofReal_comp

private def sourceBilinearFunctional (w : H) : H →L[ℂ] ℂ := innerSL ℂ (star w)

private lemma sourceBilinearFunctional_apply (w x : H) :
    sourceBilinearFunctional w x = ∑' n : ℕ, w n * x n := by
  rw [sourceBilinearFunctional, innerSL_apply_apply, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp only [lp.star_apply, RCLike.inner_apply', ← RCLike.star_def, star_star]

private lemma sourceBilinearFunctional_smul_left (a : ℂ) (w x : H) :
    sourceBilinearFunctional (a • w) x = a * sourceBilinearFunctional w x := by
  rw [sourceBilinearFunctional_apply, sourceBilinearFunctional_apply]
  calc
    _ = ∑' n : ℕ, a * (w n * x n) := by
      apply tsum_congr
      intro n
      change (a * w n) * x n = a * (w n * x n)
      ring
    _ = _ := tsum_mul_left

private lemma operatorDerivative_scaled_apply {z : ℂ} (hz : ‖z‖ < 1) (x : H) (n : ℕ) :
    (z • operatorDerivative z) x n =
      ∑' m : ℕ, ((n + 1 : ℂ) + (m + 1 : ℂ)) *
        matrixEntry z (n + 1) (m + 1) * x m := by
  let ev : (H →L[ℂ] H) →L[ℂ] ℂ := z •
    ((lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n).comp
      (ContinuousLinearMap.apply ℂ H x))
  have h := ev.hasSum (operatorDerivative_summable hz).of_norm.hasSum
  have he (p : ℕ × ℕ) : ev (operatorDerivativeTerm z p) =
      if p.1 = n then ((n + 1 : ℂ) + (p.2 + 1 : ℂ)) *
        matrixEntry z (n + 1) (p.2 + 1) * x p.2 else 0 := by
    rcases p with ⟨i, j⟩
    change z *
      (((((i + 1) + (j + 1) : ℕ) : ℂ) * z ^ (i + j + 1)) * term 1 (i, j) x n) = _
    rw [term_apply]
    by_cases hi : i = n
    · subst i
      simp only [if_pos rfl, matrixEntry, one_pow, mul_one]
      push_cast
      simp only [pow_add, pow_succ]
      ring
    · simp [hi]
  simp_rw [he] at h
  have hp := h.summable.tsum_prod
  have heq : (∑' i : ℕ, ∑' j : ℕ,
      if i = n then ((n + 1 : ℂ) + (j + 1 : ℂ)) *
        matrixEntry z (n + 1) (j + 1) * x j else 0) =
      ∑' j : ℕ, ((n + 1 : ℂ) + (j + 1 : ℂ)) *
        matrixEntry z (n + 1) (j + 1) * x j := by
    calc
      _ = ∑' i : ℕ, if i = n then
          (∑' j : ℕ, ((n + 1 : ℂ) + (j + 1 : ℂ)) *
            matrixEntry z (n + 1) (j + 1) * x j) else 0 := by
        apply tsum_congr
        intro i
        split_ifs <;> simp_all
      _ = _ := by simp
  exact (show (z • operatorDerivative z) x n = _ from h.tsum_eq.symm).trans
    (hp.trans heq)

private lemma radial_scaled_operatorDerivative {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (Real.sqrt r : ℂ) • operatorDerivative (Real.sqrt r : ℂ) =
      (sourceBilinearFunctional (weightedSource r hr.le hr1)).smulRight
        (weightedSource r hr.le hr1) := by
  let w := weightedSource r hr.le hr1
  ext x n
  change ((Real.sqrt r : ℂ) • operatorDerivative (Real.sqrt r : ℂ)) x n =
    sourceBilinearFunctional w x * w n
  rw [operatorDerivative_scaled_apply (radial_norm_lt_one hr1),
    sourceBilinearFunctional_apply]
  calc
    _ = ∑' m : ℕ, w n * (w m * x m) := by
      apply tsum_congr
      intro m
      rw [original_coordinate_anticommutator]
      change (w n * w m) * x m = w n * (w m * x m)
      ring
    _ = w n * (∑' m : ℕ, w m * x m) := tsum_mul_left
    _ = _ := mul_comm _ _

/-- Exact native signed rank-one radial derivative, with bilinear transpose. -/
theorem radial_operator_derivative_rankOne {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (r : ℂ) • radialOperatorDerivative r = (1 / 2 : ℂ) •
      (sourceBilinearFunctional (weightedSource r hr.le hr1)).smulRight
        (weightedSource r hr.le hr1) := by
  have hz : (Real.sqrt r : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hr).ne'
  have hs : (Real.sqrt r : ℂ) ^ 2 = (r : ℂ) := by
    exact_mod_cast Real.sq_sqrt hr.le
  have hcoef : (r : ℂ) * ((1 / (2 * Real.sqrt r) : ℝ) : ℂ) =
      (1 / 2 : ℂ) * (Real.sqrt r : ℂ) := by
    push_cast
    rw [← hs, pow_two]
    field_simp [hz]
    <;> ring
  rw [radialOperatorDerivative, smul_smul, hcoef, ← smul_smul,
    radial_scaled_operatorDerivative hr hr1]

private def radialNormalization (r : ℝ) : ℝ := 1 / (Real.sqrt (1 - r) * F r)

private lemma radialNormalization_ne_zero {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (radialNormalization r : ℂ) ≠ 0 := by
  have hF : F r ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (F_ge_one hr.le hr1))
  have hs : Real.sqrt (1 - r) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  exact_mod_cast (one_div_ne_zero (mul_ne_zero hs hF))

/-- The actual explicit inverse column obeys r c'=κ R_-w/2. -/
private lemma radial_column_derivative_scaled {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (r : ℂ) • radialColumnDerivative r =
      ((radialNormalization r : ℂ) / 2) •
        resolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1) := by
  let z : ℂ := (Real.sqrt r : ℂ)
  let R := resolvent z
  let w := weightedSource r hr.le hr1
  let c := column r hr.le hr1
  let a : ℂ := ((1 / (2 * Real.sqrt r) : ℝ) : ℂ)
  have hC : R (sourceFamily 0 z) = c := by
    exact radialColumn_eq_column hr hr1
  have hA : ((r : ℂ) * a) • (operatorDerivative z c) =
      (1 / 2 : ℂ) • (sourceBilinearFunctional w c • w) := by
    have he := congrArg (fun T : H →L[ℂ] H => T c)
      (radial_operator_derivative_rankOne hr hr1)
    change (r : ℂ) • (a • (operatorDerivative z c)) =
      (1 / 2 : ℂ) • (sourceBilinearFunctional w c • w) at he
    simpa only [smul_smul] using he
  have hv : ((r : ℂ) * a) • sourceFamilyDerivative 0 z = (1 / 2 : ℂ) • w := by
    rw [← smul_smul, radial_source_family_derivative_eq 0 hr hr1]
    change (r : ℂ) • ((1 / (2 * (r : ℂ))) • sourceFamily 1 z) = _
    rw [sourceFamily_one_eq_weightedSource hr.le hr1, smul_smul]
    congr 1
    field_simp [show (r : ℂ) ≠ 0 by exact_mod_cast hr.ne']
    <;> ring
  have hy : 1 + sourceBilinearFunctional w c = (radialNormalization r : ℂ) := by
    rw [sourceBilinearFunctional_apply]
    have he := (bilinear_resolvent_scalar hr hr1).2
    simp_rw [resolvent_column hr hr1] at he
    dsimp only [radialNormalization]
    push_cast
    exact he
  calc
    _ = R (((r : ℂ) * a) • (operatorDerivative z c) +
        ((r : ℂ) * a) • sourceFamilyDerivative 0 z) := by
      change (r : ℂ) • (a • ((R * operatorDerivative z * R) (sourceFamily 0 z) +
        R (sourceFamilyDerivative 0 z))) = _
      simp only [mul_apply_eq_comp, map_add, map_smul,
        smul_add, smul_smul, hC]
    _ = R ((1 / 2 : ℂ) • (sourceBilinearFunctional w c • w) + (1 / 2 : ℂ) • w) := by
      rw [hA, hv]
    _ = R (((radialNormalization r : ℂ) / 2) • w) := by
      congr 1
      rw [smul_smul, ← add_smul]
      congr 1
      linear_combination hy / 2
    _ = _ := map_smul R _ _

private lemma originalF_differentiableAt {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    DifferentiableAt ℝ F r := by
  have hz : ‖(r : ℂ)‖ < 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using hr1
  have hd := (D5.S3.Analytic.OriginalHalfBinomialPeriod.picard_fuchs hz).1.hasDerivAt
  exact hd.real_of_complex.differentiableAt

private lemma radialNormalization_hasDerivAt {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt radialNormalization
      (radialNormalization r * (1 / (2 * (1 - r)) - deriv F r / F r)) r := by
  have hb : 0 < 1 - r := by linarith
  have hF : F r ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (F_ge_one hr.le hr1))
  let s := Real.sqrt (1 - r)
  have hs0 : s ≠ 0 := (Real.sqrt_pos.mpr hb).ne'
  have hs2 : s ^ 2 = 1 - r := Real.sq_sqrt hb.le
  have hsd := (Real.hasDerivAt_sqrt hb.ne').comp r ((hasDerivAt_id r).const_sub 1)
  have hprod := hsd.mul (originalF_differentiableAt hr hr1).hasDerivAt
  have hd := (hasDerivAt_const r (1 : ℝ)).div hprod (mul_ne_zero hs0 hF)
  convert hd using 1
  · funext x
    rfl
  change (1 / (s * F r)) * (1 / (2 * (1 - r)) - deriv F r / F r) =
    (0 * (s * F r) - 1 * ((1 / (2 * s) * (-1)) * F r + s * deriv F r)) /
      (s * F r) ^ 2
  rw [← hs2]
  field_simp [hs0, hF]
  <;> ring

private lemma radial_pair_normalization {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    1 + sourceBilinearFunctional (radialSourceFamily 1 r) (radialColumn r) =
      (radialNormalization r : ℂ) := by
  rw [radialColumn_eq_column hr hr1]
  change 1 + sourceBilinearFunctional (sourceFamily 1 (Real.sqrt r : ℂ))
    (column r hr.le hr1) = _
  rw [sourceFamily_one_eq_weightedSource hr.le hr1, sourceBilinearFunctional_apply]
  have he := column_pair_normalization hr hr1
  rw [B_eq hr.le hr1] at he
  push_cast at he
  dsimp only [radialNormalization]
  push_cast
  simpa only [div_eq_mul_inv, mul_inv_rev, one_mul, mul_comm] using he

private lemma radial_frequency_pair {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    sourceBilinearFunctional (radialSourceFamily 2 r) (radialColumn r) =
      (radialNormalization r : ℂ) * ((r : ℂ) / (4 * (1 - (r : ℂ)))) := by
  have hF : F r ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (F_ge_one hr.le hr1))
  have hs : Real.sqrt (1 - r) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  have hb : 1 - r ≠ 0 := by linarith
  calc
    _ = ∑' n : ℕ, weightedSource r hr.le hr1 n * weightedColumn r hr.le hr1 n := by
      rw [sourceBilinearFunctional_apply, radialColumn_eq_column hr hr1]
      apply tsum_congr
      intro n
      change sourceFamily 2 (Real.sqrt r : ℂ) n * columnValue r n = _
      rw [sourceFamily_apply 2 (radial_norm_lt_one hr1)]
      change _ = ((n + 1 : ℂ) * sourceValue r n) * ((n + 1 : ℂ) * columnValue r n)
      simp only [sourceValue, pow_two]
      ring
    _ = ((r * B r / (4 * (1 - r) * F r) : ℝ) : ℂ) := weighted_column_pair hr hr1
    _ = _ := by
      rw [B_eq hr.le hr1]
      dsimp only [radialNormalization]
      push_cast
      field_simp [show (F r : ℂ) ≠ 0 by exact_mod_cast hF,
        show (Real.sqrt (1 - r) : ℂ) ≠ 0 by exact_mod_cast hs,
        show (1 - (r : ℂ)) ≠ 0 by exact_mod_cast hb]
      <;> ring

private lemma radial_pair_hasDerivAt {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt (fun t : ℝ =>
      sourceBilinearFunctional (radialSourceFamily 1 t) (radialColumn t))
      (sourceBilinearFunctional (radialSourceFamily 1 r) (radialColumnDerivative r) +
        sourceBilinearFunctional
          ((1 / (2 * (r : ℂ))) • radialSourceFamily 2 r) (radialColumn r)) r := by
  exact (hasDerivAt_radial_sourceFamily 1 hr hr1).star.inner ℂ
    (hasDerivAt_radial_column hr hr1)

/-- The missing negative-sign weighted moment. This is the actual inverse of
    1-operator, not the already computed inverse of 1+operator. -/
theorem bilinear_negative_resolvent_weighted_scalar {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    Summable (fun n : ℕ => ‖weightedSource r hr.le hr1 n *
      resolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1) n‖) ∧
    (∑' n : ℕ, weightedSource r hr.le hr1 n *
      resolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1) n) =
        ((3 * r / (4 * (1 - r)) - 2 * r * deriv F r / F r : ℝ) : ℂ) := by
  constructor
  · have he := lp.summable_mul (p := 2) (q := 2)
      (by simpa using Real.HolderConjugate.two_two) (weightedSource r hr.le hr1)
        (resolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1))
    simpa only [norm_mul] using he
  · let w := weightedSource r hr.le hr1
    let P : ℂ := sourceBilinearFunctional w (radialColumnDerivative r)
    let T : ℂ := sourceBilinearFunctional (radialSourceFamily 2 r) (radialColumn r)
    let Q : ℂ := sourceBilinearFunctional w (resolvent (Real.sqrt r : ℂ) w)
    let κ : ℂ := (radialNormalization r : ℂ)
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hb : 1 - (r : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (1 : ℝ) - r ≠ 0)
    have hκ : κ ≠ 0 := radialNormalization_ne_zero hr hr1
    have hF : (F r : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one (F_ge_one hr.le hr1)))
    have hT : T = κ * ((r : ℂ) / (4 * (1 - (r : ℂ)))) := radial_frequency_pair hr hr1
    have hCP : (r : ℂ) * P = (κ / 2) * Q := by
      have he := congrArg (sourceBilinearFunctional w) (radial_column_derivative_scaled hr hr1)
      simpa only [map_smul, smul_eq_mul] using he
    have hy := (hasDerivAt_const r (1 : ℂ)).add (radial_pair_hasDerivAt hr hr1)
    have heq : (fun t : ℝ => (radialNormalization t : ℂ)) =ᶠ[𝓝 r]
        (fun t => 1 + sourceBilinearFunctional (radialSourceFamily 1 t) (radialColumn t)) := by
      have hU : Set.Ioo (0 : ℝ) 1 ∈ 𝓝 r := isOpen_Ioo.mem_nhds ⟨hr, hr1⟩
      filter_upwards [hU] with t ht
      exact (radial_pair_normalization ht.1 ht.2).symm
    have hd := (hy.congr_of_eventuallyEq heq).unique
      (radialNormalization_hasDerivAt hr hr1).ofReal_comp
    rw [zero_add, sourceBilinearFunctional_smul_left] at hd
    have hw : radialSourceFamily 1 r = w := sourceFamily_one_eq_weightedSource hr.le hr1
    rw [hw] at hd
    push_cast at hd
    have hiso : (κ / 2) * Q =
        (r : ℂ) * (κ * (1 / (2 * (1 - (r : ℂ))) -
          ((deriv F r : ℝ) : ℂ) / (F r : ℂ))) - T / 2 := by
      rw [← hCP, ← hd]
      field_simp [hr0]
      <;> ring
    have hQ : Q = 3 * (r : ℂ) / (4 * (1 - (r : ℂ))) -
        2 * (r : ℂ) * ((deriv F r : ℝ) : ℂ) / (F r : ℂ) := by
      apply mul_left_cancel₀ hκ
      calc
        κ * Q = 2 * ((κ / 2) * Q) := by ring
        _ = 2 * ((r : ℂ) * (κ * (1 / (2 * (1 - (r : ℂ))) -
            ((deriv F r : ℝ) : ℂ) / (F r : ℂ))) - T / 2) := by rw [hiso]
        _ = κ * (3 * (r : ℂ) / (4 * (1 - (r : ℂ))) -
            2 * (r : ℂ) * ((deriv F r : ℝ) : ℂ) / (F r : ℂ)) := by
          rw [hT]
          field_simp [hb, hF]
          <;> ring
    rw [← sourceBilinearFunctional_apply]
    push_cast
    exact hQ

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation
