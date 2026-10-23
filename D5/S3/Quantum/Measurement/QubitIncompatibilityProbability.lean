/- GID: D5/S3/Quantum/Measurement/QubitIncompatibilityProbability
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/QubitIncompatibilityProbability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The qubit incompatibility probability is strictly less than one quarter. -/

/-
admission_basis: open-problem-resolution (#15842; Refuted)
Direct frozen dependencies: none (the only D5 import belongs to this delivery).
result: proof_shape: content; escape_witness: none.
The refutation uses the literal body, squared Yu function and Lebesgue-volume probability.
The public result is the designated refutation result (`basis=refutes`) in the lane brief.
The required utility: none header supplies no refutes selector, so no machine exemption is claimed.
Four-slot escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15930
Declaration rows: name | proof_shape | escape_witness | one direct consumer.
Definitions have no proof term; their bind-only label supplies no admission witness.
squareDomain | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.squareI_eq_cubeL
squareMap | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.root_square_cancellation
squareDerivative | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.squareMap_derivative
squareMap_injective | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.square_change_lintegral
squareMap_image | proof_shape: content | escape_witness: none | QubitIncompatibilityProbability.square_change_lintegral
squareMap_derivative | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.square_change_lintegral
squareDerivative_det | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.square_change_lintegral
square_change_lintegral | proof_shape: content | escape_witness: none | QubitIncompatibilityProbability.rootI_eq_squareI
triangleMap | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.squareI_eq_cubeL
triangleDerivative | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.triangleMap_derivative
triangleMap_injective | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.triangle_change_lintegral
triangleMap_image | proof_shape: content | escape_witness: none | QubitIncompatibilityProbability.triangle_change_lintegral
triangleMap_derivative | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.triangle_change_lintegral
triangleDerivative_det | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.triangle_change_lintegral
triangle_change_lintegral | proof_shape: content | escape_witness: none | QubitIncompatibilityProbability.squareI_eq_cubeL
squareDensity | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.squareI
squareI | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.squareI_eq_cubeL
xCoord_square | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.root_square_cancellation
root_square_cancellation | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.rootI_eq_squareI
rootI_eq_squareI | proof_shape: content | escape_witness: none | QubitIncompatibilityProbability.volume_NJM_cubeI
squareDensity_measurable | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.squareI_regroup
squareDomain_fubini | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.squareI_eq_cubeL
cubeBeforeTriangle | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.squareI_eq_cubeL
squareI_regroup | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.squareI_triangle
triangleDomain_subset_square | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.squareI_triangle
squareI_triangle | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.squareI_eq_cubeL
p | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.polynomialIntegrand
sqrt_certificate | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.cube_integrand_le_polynomial
polynomial_integral_B0 | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.radial_moment_B0
polynomial_integral_B1 | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.radial_moment_B1
polynomial_integral_B2 | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.radial_moment_B2
w | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.polynomialIntegrand
W | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.polynomialIntegrand
radial_substitution | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.radial_moment_B1
radial_moment_B0 | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.cube_integral_upper_bound
radial_moment_B1 | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.cube_integral_upper_bound
radial_moment_B2 | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.cube_integral_upper_bound
W_bounds | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.cube_integrand_le_polynomial
w_nonneg | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.cube_integrand_le_polynomial
polynomial_cube_integral | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.cube_integral_upper_bound
cubeIntegrand | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.squareI_eq_cubeL
polynomialIntegrand | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.cube_integral_upper_bound
I | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.cube_integral_upper_bound
cube_integrand_le_polynomial | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.cube_integral_upper_bound
cube_integral_upper_bound | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.incompProb_upper_bound
triangle_cube_cancellation | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.squareI_eq_cubeL
cubeL | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.squareI_eq_cubeL
squareI_eq_cubeL | proof_shape: content | escape_witness: none | QubitIncompatibilityProbability.volume_NJM_cubeI
lintegral_unit_ofReal | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.cubeL_eq_ofReal_integral
cube_integrand_nonneg | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.cubeL_eq_ofReal_integral
cubeL_eq_ofReal_integral | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.volume_NJM_cubeI
volume_NJM_cubeI | proof_shape: content | escape_witness: none | QubitIncompatibilityProbability.incompProb_eq_nine_I
I_nonneg | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.incompProb_eq_nine_I
incompProb_eq_nine_I | proof_shape: content | escape_witness: none | QubitIncompatibilityProbability.incompProb_upper_bound
incompProb_upper_bound | proof_shape: content | escape_witness: none | QubitIncompatibilityProbability.result
result | proof_shape: content | escape_witness: none | settling result
-/

import D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
noncomputable section
open D5.S3.Quantum.Measurement.OrderedRootCoordinates
open D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace D5.S3.Quantum.Measurement.QubitIncompatibilityProbability

def squareDomain : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1

private def squareMap (p : ℝ × ℝ) : ℝ × ℝ := (p.1, p.1 * p.2 ^ 2)

private def squareDerivative (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![1, 0; p.2 ^ 2, 2*p.1*p.2]).toContinuousLinearMap

private theorem squareMap_injective : InjOn squareMap squareDomain := by
  intro p hp q hq he
  have hfst := congrArg Prod.fst he
  change p.1 = q.1 at hfst
  have hsnd : p.1*p.2^2 = q.1*q.2^2 := congrArg Prod.snd he
  have hp0 : 0 < p.1 := hp.1.1
  have ht0 : 0 < p.2 := hp.2.1
  have hs0 : 0 < q.2 := hq.2.1
  apply Prod.ext hfst
  rw [← hfst] at hsnd
  have hs := mul_left_cancel₀ (ne_of_gt hp0) hsnd
  nlinarith [hs]

private theorem squareMap_image : squareMap '' squareDomain = rootDomain := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hu0 : 0 < q.1 := hq.1.1
    have hu1 : q.1 < 1 := hq.1.2
    have ht0 : 0 < q.2 := hq.2.1
    have ht1 : q.2 < 1 := hq.2.2
    change 0 < q.1*q.2^2 ∧ q.1*q.2^2 < q.1 ∧ q.1 < 1
    refine ⟨mul_pos hu0 (sq_pos_of_pos ht0), ?_, hu1⟩
    nlinarith [mul_pos hu0 (show 0 < 1-q.2^2 by nlinarith)]
  · intro hp
    have hv0 : 0 < p.2 := hp.1
    have hvu : p.2 < p.1 := hp.2.1
    have hu1 : p.1 < 1 := hp.2.2
    have hu0 : 0 < p.1 := hv0.trans hvu
    have ht0 : 0 < Real.sqrt (p.2/p.1) := Real.sqrt_pos.mpr (div_pos hv0 hu0)
    have ht1 : Real.sqrt (p.2/p.1) < 1 := by
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
      norm_num only [one_pow]
      rw [div_lt_one hu0]
      exact hvu
    refine ⟨(p.1, Real.sqrt (p.2/p.1)), ⟨⟨hu0,hu1⟩, ht0, ht1⟩, ?_⟩
    apply Prod.ext
    · rfl
    · change p.1 * Real.sqrt (p.2/p.1)^2 = p.2
      rw [Real.sq_sqrt (div_nonneg hv0.le hu0.le)]
      field_simp

private theorem squareMap_derivative (p : ℝ × ℝ) : HasFDerivAt squareMap (squareDerivative p) p := by
  unfold squareDerivative
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  have hu := hasFDerivAt_fst (𝕜 := ℝ) (p := p)
  have ht := hasFDerivAt_snd (𝕜 := ℝ) (p := p)
  convert! hu.prodMk (hu.mul (ht.pow 2)) using 1
  ext q <;> simp [ContinuousLinearMap.prod_apply, smul_eq_mul] <;> ring

private theorem squareDerivative_det (p : ℝ × ℝ) : (squareDerivative p).det = 2*p.1*p.2 := by
  simp [squareDerivative, LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of]

private theorem square_change_lintegral (f : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ p in rootDomain, f p) = ∫⁻ p in squareDomain,
      ENNReal.ofReal (2*p.1*p.2) * f (squareMap p) := by
  have hm : MeasurableSet squareDomain := measurableSet_Ioo.prod measurableSet_Ioo
  rw [← squareMap_image, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hm
    (fun p _ => (squareMap_derivative p).hasFDerivWithinAt) squareMap_injective]
  apply setLIntegral_congr_fun hm
  intro p hp
  dsimp only
  rw [squareDerivative_det, abs_of_pos]
  exact mul_pos (mul_pos (by norm_num) hp.1.1) hp.2.1

end D5.S3.Quantum.Measurement.QubitIncompatibilityProbability

namespace D5.S3.Quantum.Measurement.QubitIncompatibilityProbability

def triangleMap (p : ℝ × ℝ) : ℝ × ℝ := (p.1*p.2, p.1*(1-p.2))

private def triangleDerivative (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![p.2, p.1; 1-p.2, -p.1]).toContinuousLinearMap

private theorem triangleMap_injective : InjOn triangleMap squareDomain := by
  intro p hp q hq he
  have hfst := congrArg Prod.fst he
  change p.1*p.2 = q.1*q.2 at hfst
  have hsnd : p.1*(1-p.2) = q.1*(1-q.2) := congrArg Prod.snd he
  have hu0 : 0 < p.1 := hp.1.1
  have he1 : p.1 = q.1 := by nlinarith
  apply Prod.ext he1
  rw [← he1] at hfst
  exact mul_left_cancel₀ (ne_of_gt hu0) hfst

private theorem triangleMap_image : triangleMap '' squareDomain = radialBody := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hr0 : 0 < q.1 := hq.1.1
    have hr1 : q.1 < 1 := hq.1.2
    have ha0 : 0 < q.2 := hq.2.1
    have ha1 : q.2 < 1 := hq.2.2
    change 0 < q.1*q.2 ∧ 0 < q.1*(1-q.2) ∧ q.1*q.2+q.1*(1-q.2) < 1
    exact ⟨mul_pos hr0 ha0, mul_pos hr0 (sub_pos.mpr ha1), by nlinarith⟩
  · intro hp
    have hu0 : 0 < p.1 := hp.1
    have hv0 : 0 < p.2 := hp.2.1
    have hr1 : p.1+p.2 < 1 := hp.2.2
    have hr0 : 0 < p.1+p.2 := add_pos hu0 hv0
    refine ⟨(p.1+p.2, p.1/(p.1+p.2)), ⟨⟨hr0,hr1⟩, div_pos hu0 hr0, ?_⟩, ?_⟩
    · rw [div_lt_one hr0]; linarith
    · apply Prod.ext <;> dsimp [triangleMap] <;> field_simp <;> ring

private theorem triangleMap_derivative (p : ℝ × ℝ) :
    HasFDerivAt triangleMap (triangleDerivative p) p := by
  unfold triangleDerivative
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  have hu := hasFDerivAt_fst (𝕜 := ℝ) (p := p)
  have ht := hasFDerivAt_snd (𝕜 := ℝ) (p := p)
  convert! (hu.mul ht).prodMk (hu.mul (ht.const_sub 1)) using 1
  ext q <;> simp [ContinuousLinearMap.prod_apply, smul_eq_mul] <;> ring

private theorem triangleDerivative_det (p : ℝ × ℝ) : (triangleDerivative p).det = -p.1 := by
  simp [triangleDerivative, LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of]
  ring

theorem triangle_change_lintegral (f : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ p in radialBody, f p) = ∫⁻ p in squareDomain,
      ENNReal.ofReal p.1 * f (triangleMap p) := by
  have hm : MeasurableSet squareDomain := measurableSet_Ioo.prod measurableSet_Ioo
  rw [← triangleMap_image, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hm
    (fun p _ => (triangleMap_derivative p).hasFDerivWithinAt) triangleMap_injective]
  apply setLIntegral_congr_fun hm
  intro p hp
  dsimp only
  rw [triangleDerivative_det, abs_neg, abs_of_pos (show 0 < p.1 from hp.1.1)]

end D5.S3.Quantum.Measurement.QubitIncompatibilityProbability

namespace D5.S3.Quantum.Measurement.QubitIncompatibilityProbability
open Classical D5.S3.Quantum.Measurement.OrderedRootCoordinates D5.S3.Quantum.Measurement.QubitIncompatibilityProbability

private def squareDensity (p q : ℝ × ℝ) : ℝ :=
    if 0<1-p.1-q.1 then 4*p.1*q.1*(1-p.2^2)*(1-q.2^2)*
      Real.sqrt (1-p.1-q.1)*Real.sqrt (1-p.1*p.2^2-q.1*q.2^2) else 0

private def squareI : ℝ≥0∞ := ∫⁻ p : ℝ × ℝ in squareDomain,
    ∫⁻ q : ℝ × ℝ in squareDomain, ENNReal.ofReal (squareDensity p q)

private theorem xCoord_square {u t : ℝ} (hu : 0≤u) (ht : 0≤t) :
    xCoord u (u*t^2) = u*t := by
  unfold xCoord
  rw [Real.sqrt_mul hu, Real.sqrt_sq ht]
  calc
    Real.sqrt u * (Real.sqrt u*t) = Real.sqrt u^2*t := by ring
    _ = _ := by rw [Real.sq_sqrt hu]

private theorem root_square_cancellation {p q : ℝ × ℝ}
    (hp : p ∈ squareDomain) (hq : q ∈ squareDomain) :
    ENNReal.ofReal (2*p.1*p.2) * ENNReal.ofReal (2*q.1*q.2) *
      ENNReal.ofReal (rootDensity (squareMap p) (squareMap q)) =
      ENNReal.ofReal (squareDensity p q) := by
  have hp0 : 0<p.1 := hp.1.1
  have ht0 : 0<p.2 := hp.2.1
  have hq0 : 0<q.1 := hq.1.1
  have hs0 : 0<q.2 := hq.2.1
  rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ)≤2*p.1*p.2),
    ← ENNReal.ofReal_mul (by positivity : (0:ℝ)≤2*p.1*p.2*(2*q.1*q.2))]
  unfold rootDensity squareDensity squareMap
  dsimp only
  rw [xCoord_square hp0.le ht0.le, xCoord_square hq0.le hs0.le]
  by_cases hA : 0<1-p.1-q.1
  · rw [if_pos hA, if_pos hA]
    have hB : 0≤1-p.1*p.2^2-q.1*q.2^2 := by
      have ht1 : p.2<1 := hp.2.2
      have hs1 : q.2<1 := hq.2.2
      nlinarith [mul_pos hp0 (show 0<1-p.2^2 by nlinarith),
        mul_pos hq0 (show 0<1-q.2^2 by nlinarith)]
    rw [Real.sqrt_mul hA.le]
    congr 1
    field_simp [ne_of_gt hp0, ne_of_gt ht0, ne_of_gt hq0, ne_of_gt hs0]
    <;> ring
  · simp [hA]

private theorem rootI_eq_squareI : rootI = squareI := by
  unfold rootI squareI
  change (∫⁻ p : ℝ × ℝ in rootDomain, ∫⁻ q : ℝ × ℝ in rootDomain,
    ENNReal.ofReal (rootDensity p q)) = _
  rw [square_change_lintegral]
  apply setLIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
  intro p hp
  dsimp only
  rw [square_change_lintegral]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
  intro q hq
  dsimp only
  rw [← mul_assoc]
  exact root_square_cancellation hp hq

end D5.S3.Quantum.Measurement.QubitIncompatibilityProbability
namespace D5.S3.Quantum.Measurement.QubitIncompatibilityProbability
open Classical D5.S3.Quantum.Measurement.OrderedRootCoordinates D5.S3.Quantum.Measurement.QubitIncompatibilityProbability

@[fun_prop] private theorem squareDensity_measurable :
    Measurable (Function.uncurry squareDensity) := by
  unfold squareDensity Function.uncurry
  apply Measurable.ite
  · measurability
  · fun_prop
  · exact measurable_const

private theorem squareDomain_fubini (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p : ℝ × ℝ in squareDomain, f p) =
      ∫⁻ u : ℝ in Ioo (0 : ℝ) 1, ∫⁻ t : ℝ in Ioo (0 : ℝ) 1, f (u,t) := by
  rw [squareDomain, Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hf.aemeasurable]

private def cubeBeforeTriangle (p : ℝ × ℝ) : ℝ≥0∞ :=
    ∫⁻ t : ℝ in Ioo (0 : ℝ) 1, ∫⁻ s : ℝ in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (squareDensity (p.1,t) (p.2,s))

private theorem squareI_regroup : squareI = ∫⁻ p : ℝ × ℝ in squareDomain, cubeBeforeTriangle p := by
  unfold squareI cubeBeforeTriangle
  rw [squareDomain_fubini _ (by fun_prop), squareDomain_fubini _ (by fun_prop)]
  apply lintegral_congr
  intro u
  have he : ∀ t : ℝ,
    (∫⁻ q : ℝ × ℝ in squareDomain, ENNReal.ofReal (squareDensity (u,t) q)) =
      ∫⁻ U : ℝ in Ioo (0 : ℝ) 1, ∫⁻ s : ℝ in Ioo (0 : ℝ) 1,
        ENNReal.ofReal (squareDensity (u,t) (U,s)) := by
    intro t
    exact squareDomain_fubini _ (by fun_prop)
  simp_rw [he]
  apply lintegral_lintegral_swap
  fun_prop

private theorem triangleDomain_subset_square : radialBody ⊆ squareDomain := by
  intro p hp
  have hu0 : 0<p.1 := hp.1
  have hU0 : 0<p.2 := hp.2.1
  have hs : p.1+p.2<1 := hp.2.2
  exact ⟨⟨hu0, by linarith⟩, hU0, by linarith⟩

private theorem squareI_triangle : squareI = ∫⁻ p : ℝ × ℝ in radialBody, cubeBeforeTriangle p := by
  rw [squareI_regroup]
  have hs : Function.support (radialBody.indicator cubeBeforeTriangle) ⊆ squareDomain := by
    intro p hp
    have ht : p ∈ radialBody := by
      by_contra hn
      exact hp (indicator_of_notMem hn _)
    exact triangleDomain_subset_square ht
  have ht : MeasurableSet radialBody := by unfold radialBody; measurability
  calc
    _ = ∫⁻ p : ℝ × ℝ in squareDomain, radialBody.indicator cubeBeforeTriangle p := by
      apply setLIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
      intro p hp
      by_cases h : p ∈ radialBody
      · rw [indicator_of_mem h]
      · have hA : ¬ (0<1-p.1-p.2) := by
          intro hA
          exact h ⟨hp.1.1,hp.2.1,by linarith⟩
        rw [indicator_of_notMem h]
        unfold cubeBeforeTriangle
        have he : ∀ t s : ℝ, squareDensity (p.1,t) (p.2,s) = 0 := by
          intro t s
          exact if_neg hA
        simp_rw [he]
        simp
    _ = ∫⁻ p : ℝ × ℝ, radialBody.indicator cubeBeforeTriangle p :=
      setLIntegral_eq_of_support_subset hs
    _ = _ := lintegral_indicator ht _

end D5.S3.Quantum.Measurement.QubitIncompatibilityProbability


open MeasureTheory Set
noncomputable section
namespace D5.S3.Quantum.Measurement.QubitIncompatibilityProbability

private def p (z : ℝ) : ℝ := 1 - z / 2 - z ^ 2 / 8

private theorem sqrt_certificate {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    Real.sqrt (1 - z) ≤ p z := by
  have hz2 : z ^ 2 ≤ 1 := by nlinarith
  have hp : 0 ≤ p z := by unfold p; linarith
  have he : p z ^ 2 - (1 - z) = z ^ 3 * (8 + z) / 64 := by unfold p; ring
  have hh : 0 ≤ z ^ 3 * (8 + z) / 64 := by positivity
  have hs := Real.sq_sqrt (by linarith : 0 ≤ 1 - z)
  have hn := Real.sqrt_nonneg (1 - z)
  nlinarith

private theorem polynomial_integral_B0 :
    (∫ z : ℝ in (0 : ℝ)..1, 2 * z ^ 2 * (1 - z ^ 2) ^ 3) = 32 / 315 := by
  have he : (fun z : ℝ => 2 * z ^ 2 * (1 - z ^ 2) ^ 3) =
      fun z => 2 * z ^ 2 - 6 * z ^ 4 + 6 * z ^ 6 - 2 * z ^ 8 := by
    funext z; ring
  rw [he]
  change (∫ z : ℝ in (0 : ℝ)..1, 2 * z ^ 2 - 6 * z ^ 4 + 6 * z ^ 6 - 2 * z ^ 8) = _
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [intervalIntegral.integral_sub, intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul, integral_pow]
  norm_num

private theorem polynomial_integral_B1 :
    (∫ z : ℝ in (0 : ℝ)..1, 2 * z ^ 2 * (1 - z ^ 2) ^ 4) = 256 / 3465 := by
  have he : (fun z : ℝ => 2 * z ^ 2 * (1 - z ^ 2) ^ 4) =
      fun z => 2 * z ^ 2 - 8 * z ^ 4 + 12 * z ^ 6 - 8 * z ^ 8 + 2 * z ^ 10 := by
    funext z; ring
  rw [he]
  change (∫ z : ℝ in (0 : ℝ)..1, 2 * z ^ 2 - 8 * z ^ 4 + 12 * z ^ 6 - 8 * z ^ 8 + 2 * z ^ 10) = _
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [intervalIntegral.integral_sub, intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul, integral_pow]
  norm_num

private theorem polynomial_integral_B2 :
    (∫ z : ℝ in (0 : ℝ)..1, 2 * z ^ 2 * (1 - z ^ 2) ^ 5) = 512 / 9009 := by
  have he : (fun z : ℝ => 2 * z ^ 2 * (1 - z ^ 2) ^ 5) =
      fun z => 2 * z ^ 2 - 10 * z ^ 4 + 20 * z ^ 6 - 20 * z ^ 8 + 10 * z ^ 10 - 2 * z ^ 12 := by
    funext z; ring
  rw [he]
  change (∫ z : ℝ in (0 : ℝ)..1, 2 * z ^ 2 - 10 * z ^ 4 + 20 * z ^ 6 - 20 * z ^ 8 + 10 * z ^ 10 - 2 * z ^ 12) = _
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [intervalIntegral.integral_sub, intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul, integral_pow]
  norm_num

private def w (a t s : ℝ) : ℝ := a * (1 - a) * (1 - t ^ 2) * (1 - s ^ 2)
private def W (a t s : ℝ) : ℝ := a * t ^ 2 + (1 - a) * s ^ 2

private theorem radial_substitution (n : ℕ) :
    (∫ r : ℝ in (0 : ℝ)..1, r ^ n * Real.sqrt (1 - r)) =
      ∫ z : ℝ in (0 : ℝ)..1, 2 * z ^ 2 * (1 - z ^ 2) ^ n := by
  have hd : ∀ z : ℝ, HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * z) z := by
    intro z
    have h : HasDerivAt (fun y : ℝ => y ^ 2) (2 * z) z := by
      simpa using hasDerivAt_pow 2 z
    have h' : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * z)) z := by
      exact h.const_sub 1
    convert h' using 1 <;> ring
  have he := intervalIntegral.integral_comp_mul_deriv
    (a := (0 : ℝ)) (b := 1) (g := fun r : ℝ => r ^ n * Real.sqrt (1 - r))
    (fun x _ => hd x) (by fun_prop) (by fun_prop)
  have hi : (∫ z : ℝ in (0 : ℝ)..1,
      (1 - z ^ 2) ^ n * Real.sqrt (1 - (1 - z ^ 2)) * (-2 * z)) =
      -(∫ z : ℝ in (0 : ℝ)..1, 2 * z ^ 2 * (1 - z ^ 2) ^ n) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro z hz
    have hz0 : 0 ≤ z := (uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1) ▸ hz).1
    dsimp only
    rw [show 1 - (1 - z ^ 2) = z ^ 2 by ring, Real.sqrt_sq hz0]
    ring
  simp only [Function.comp_def] at he
  change (∫ z : ℝ in (0 : ℝ)..1,
      (1 - z ^ 2) ^ n * Real.sqrt (1 - (1 - z ^ 2)) * (-2 * z)) =
      ∫ r : ℝ in (1 - 0 ^ 2)..(1 - 1 ^ 2), r ^ n * Real.sqrt (1 - r) at he
  norm_num only [zero_pow (by norm_num : 2 ≠ 0), one_pow, sub_zero, sub_self] at he
  rw [hi, intervalIntegral.integral_symm (a := (0 : ℝ)) (b := 1)] at he
  exact neg_injective he.symm


private theorem radial_moment_B0 :
    (∫ r : ℝ in (0 : ℝ)..1, r ^ 3 * Real.sqrt (1 - r)) = 32 / 315 := by
  rw [radial_substitution, polynomial_integral_B0]

private theorem radial_moment_B1 :
    (∫ r : ℝ in (0 : ℝ)..1, r ^ 4 * Real.sqrt (1 - r)) = 256 / 3465 := by
  rw [radial_substitution, polynomial_integral_B1]

private theorem radial_moment_B2 :
    (∫ r : ℝ in (0 : ℝ)..1, r ^ 5 * Real.sqrt (1 - r)) = 512 / 9009 := by
  rw [radial_substitution, polynomial_integral_B2]

private theorem W_bounds {a t s : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    0 ≤ W a t s ∧ W a t s ≤ 1 := by
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  have hs2 : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
  have h0 := mul_nonneg ha.1 (sq_nonneg t)
  have h1 := mul_nonneg (sub_nonneg.mpr ha.2) (sq_nonneg s)
  have h2 := mul_le_mul_of_nonneg_left ht2 ha.1
  have h3 := mul_le_mul_of_nonneg_left hs2 (sub_nonneg.mpr ha.2)
  unfold W
  constructor <;> nlinarith

private theorem w_nonneg {a t s : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) : 0 ≤ w a t s := by
  unfold w
  have ht2 : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have hs2 : 0 ≤ 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
  exact mul_nonneg (mul_nonneg (mul_nonneg ha.1 (sub_nonneg.mpr ha.2)) ht2) hs2




set_option maxHeartbeats 2000000 in
private theorem polynomial_cube_integral (r : ℝ) :
    (∫ a : ℝ in (0 : ℝ)..1, ∫ t : ℝ in (0 : ℝ)..1,
      ∫ s : ℝ in (0 : ℝ)..1, w a t s * p (r * W a t s)) =
      2 / 27 - (r / 2) * (2 / 135) - (r ^ 2 / 8) * (118 / 23625) := by
  have he : ∀ a t s : ℝ, w a t s * p (r * W a t s) =
        (1 : ℝ) * r ^ 0 * a ^ 1 * t ^ 0 * s ^ 0 +
        (-1 : ℝ) * r ^ 0 * a ^ 1 * t ^ 0 * s ^ 2 +
        (-1 : ℝ) * r ^ 0 * a ^ 1 * t ^ 2 * s ^ 0 +
        (1 : ℝ) * r ^ 0 * a ^ 1 * t ^ 2 * s ^ 2 +
        (-1 : ℝ) * r ^ 0 * a ^ 2 * t ^ 0 * s ^ 0 +
        (1 : ℝ) * r ^ 0 * a ^ 2 * t ^ 0 * s ^ 2 +
        (1 : ℝ) * r ^ 0 * a ^ 2 * t ^ 2 * s ^ 0 +
        (-1 : ℝ) * r ^ 0 * a ^ 2 * t ^ 2 * s ^ 2 +
        (-1 / 2 : ℝ) * r ^ 1 * a ^ 1 * t ^ 0 * s ^ 2 +
        (1 / 2 : ℝ) * r ^ 1 * a ^ 1 * t ^ 0 * s ^ 4 +
        (1 / 2 : ℝ) * r ^ 1 * a ^ 1 * t ^ 2 * s ^ 2 +
        (-1 / 2 : ℝ) * r ^ 1 * a ^ 1 * t ^ 2 * s ^ 4 +
        (1 : ℝ) * r ^ 1 * a ^ 2 * t ^ 0 * s ^ 2 +
        (-1 : ℝ) * r ^ 1 * a ^ 2 * t ^ 0 * s ^ 4 +
        (-1 / 2 : ℝ) * r ^ 1 * a ^ 2 * t ^ 2 * s ^ 0 +
        (-1 / 2 : ℝ) * r ^ 1 * a ^ 2 * t ^ 2 * s ^ 2 +
        (1 : ℝ) * r ^ 1 * a ^ 2 * t ^ 2 * s ^ 4 +
        (1 / 2 : ℝ) * r ^ 1 * a ^ 2 * t ^ 4 * s ^ 0 +
        (-1 / 2 : ℝ) * r ^ 1 * a ^ 2 * t ^ 4 * s ^ 2 +
        (-1 / 2 : ℝ) * r ^ 1 * a ^ 3 * t ^ 0 * s ^ 2 +
        (1 / 2 : ℝ) * r ^ 1 * a ^ 3 * t ^ 0 * s ^ 4 +
        (1 / 2 : ℝ) * r ^ 1 * a ^ 3 * t ^ 2 * s ^ 0 +
        (-1 / 2 : ℝ) * r ^ 1 * a ^ 3 * t ^ 2 * s ^ 4 +
        (-1 / 2 : ℝ) * r ^ 1 * a ^ 3 * t ^ 4 * s ^ 0 +
        (1 / 2 : ℝ) * r ^ 1 * a ^ 3 * t ^ 4 * s ^ 2 +
        (-1 / 8 : ℝ) * r ^ 2 * a ^ 1 * t ^ 0 * s ^ 4 +
        (1 / 8 : ℝ) * r ^ 2 * a ^ 1 * t ^ 0 * s ^ 6 +
        (1 / 8 : ℝ) * r ^ 2 * a ^ 1 * t ^ 2 * s ^ 4 +
        (-1 / 8 : ℝ) * r ^ 2 * a ^ 1 * t ^ 2 * s ^ 6 +
        (3 / 8 : ℝ) * r ^ 2 * a ^ 2 * t ^ 0 * s ^ 4 +
        (-3 / 8 : ℝ) * r ^ 2 * a ^ 2 * t ^ 0 * s ^ 6 +
        (-1 / 4 : ℝ) * r ^ 2 * a ^ 2 * t ^ 2 * s ^ 2 +
        (-1 / 8 : ℝ) * r ^ 2 * a ^ 2 * t ^ 2 * s ^ 4 +
        (3 / 8 : ℝ) * r ^ 2 * a ^ 2 * t ^ 2 * s ^ 6 +
        (1 / 4 : ℝ) * r ^ 2 * a ^ 2 * t ^ 4 * s ^ 2 +
        (-1 / 4 : ℝ) * r ^ 2 * a ^ 2 * t ^ 4 * s ^ 4 +
        (-3 / 8 : ℝ) * r ^ 2 * a ^ 3 * t ^ 0 * s ^ 4 +
        (3 / 8 : ℝ) * r ^ 2 * a ^ 3 * t ^ 0 * s ^ 6 +
        (1 / 2 : ℝ) * r ^ 2 * a ^ 3 * t ^ 2 * s ^ 2 +
        (-1 / 8 : ℝ) * r ^ 2 * a ^ 3 * t ^ 2 * s ^ 4 +
        (-3 / 8 : ℝ) * r ^ 2 * a ^ 3 * t ^ 2 * s ^ 6 +
        (-1 / 8 : ℝ) * r ^ 2 * a ^ 3 * t ^ 4 * s ^ 0 +
        (-3 / 8 : ℝ) * r ^ 2 * a ^ 3 * t ^ 4 * s ^ 2 +
        (1 / 2 : ℝ) * r ^ 2 * a ^ 3 * t ^ 4 * s ^ 4 +
        (1 / 8 : ℝ) * r ^ 2 * a ^ 3 * t ^ 6 * s ^ 0 +
        (-1 / 8 : ℝ) * r ^ 2 * a ^ 3 * t ^ 6 * s ^ 2 +
        (1 / 8 : ℝ) * r ^ 2 * a ^ 4 * t ^ 0 * s ^ 4 +
        (-1 / 8 : ℝ) * r ^ 2 * a ^ 4 * t ^ 0 * s ^ 6 +
        (-1 / 4 : ℝ) * r ^ 2 * a ^ 4 * t ^ 2 * s ^ 2 +
        (1 / 8 : ℝ) * r ^ 2 * a ^ 4 * t ^ 2 * s ^ 4 +
        (1 / 8 : ℝ) * r ^ 2 * a ^ 4 * t ^ 2 * s ^ 6 +
        (1 / 8 : ℝ) * r ^ 2 * a ^ 4 * t ^ 4 * s ^ 0 +
        (1 / 8 : ℝ) * r ^ 2 * a ^ 4 * t ^ 4 * s ^ 2 +
        (-1 / 4 : ℝ) * r ^ 2 * a ^ 4 * t ^ 4 * s ^ 4 +
        (-1 / 8 : ℝ) * r ^ 2 * a ^ 4 * t ^ 6 * s ^ 0 +
        (1 / 8 : ℝ) * r ^ 2 * a ^ 4 * t ^ 6 * s ^ 2 := by
    intro a t s
    unfold w W p
    ring
  simp_rw [he]
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_mul_const, integral_pow]
  norm_num
  ring

private def cubeIntegrand (r a t s : ℝ) : ℝ :=
  r ^ 3 * Real.sqrt (1 - r) * w a t s * Real.sqrt (1 - r * W a t s)

private def polynomialIntegrand (r a t s : ℝ) : ℝ :=
  r ^ 3 * Real.sqrt (1 - r) * w a t s * p (r * W a t s)

private def I : ℝ := 4 * ∫ r : ℝ in (0 : ℝ)..1, ∫ a : ℝ in (0 : ℝ)..1,
  ∫ t : ℝ in (0 : ℝ)..1, ∫ s : ℝ in (0 : ℝ)..1, cubeIntegrand r a t s

private theorem cube_integrand_le_polynomial {r a t s : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) (ha : a ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    cubeIntegrand r a t s ≤ polynomialIntegrand r a t s := by
  have hW := W_bounds ha ht hs
  have hz0 : 0 ≤ r * W a t s := mul_nonneg hr.1 hW.1
  have hz1 : r * W a t s ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hW.2 hr.1
    nlinarith [hr.2]
  apply mul_le_mul_of_nonneg_left (sqrt_certificate hz0 hz1)
  exact mul_nonneg (mul_nonneg (pow_nonneg hr.1 3) (Real.sqrt_nonneg _))
    (w_nonneg ha ht hs)

private theorem cube_integral_upper_bound : I ≤ 5910272 / 212837625 := by
  have hm : (∫ r : ℝ in (0 : ℝ)..1, ∫ a : ℝ in (0 : ℝ)..1,
      ∫ t : ℝ in (0 : ℝ)..1, ∫ s : ℝ in (0 : ℝ)..1, cubeIntegrand r a t s) ≤
      (∫ r : ℝ in (0 : ℝ)..1, ∫ a : ℝ in (0 : ℝ)..1,
      ∫ t : ℝ in (0 : ℝ)..1, ∫ s : ℝ in (0 : ℝ)..1, polynomialIntegrand r a t s) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (by apply Continuous.intervalIntegrable; unfold cubeIntegrand w W; fun_prop)
      (by apply Continuous.intervalIntegrable; unfold polynomialIntegrand p w W; fun_prop)
    intro r hr
    apply intervalIntegral.integral_mono_on (by norm_num)
      (by apply Continuous.intervalIntegrable; unfold cubeIntegrand w W; fun_prop)
      (by apply Continuous.intervalIntegrable; unfold polynomialIntegrand p w W; fun_prop)
    intro a ha
    apply intervalIntegral.integral_mono_on (by norm_num)
      (by apply Continuous.intervalIntegrable; unfold cubeIntegrand w W; fun_prop)
      (by apply Continuous.intervalIntegrable; unfold polynomialIntegrand p w W; fun_prop)
    intro t ht
    apply intervalIntegral.integral_mono_on (by norm_num)
      (by apply Continuous.intervalIntegrable; unfold cubeIntegrand w W; fun_prop)
      (by apply Continuous.intervalIntegrable; unfold polynomialIntegrand p w W; fun_prop)
    intro s hs
    exact cube_integrand_le_polynomial hr ha ht hs
  have he : 4 * (∫ r : ℝ in (0 : ℝ)..1, ∫ a : ℝ in (0 : ℝ)..1,
      ∫ t : ℝ in (0 : ℝ)..1, ∫ s : ℝ in (0 : ℝ)..1, polynomialIntegrand r a t s) =
      5910272 / 212837625 := by
    unfold polynomialIntegrand
    simp_rw [mul_assoc, intervalIntegral.integral_const_mul]
    simp_rw [polynomial_cube_integral]
    have he : ∀ r : ℝ, r ^ 3 * (Real.sqrt (1 - r) *
        (2 / 27 - (r / 2) * (2 / 135) - (r ^ 2 / 8) * (118 / 23625))) =
        (2 / 27) * (r ^ 3 * Real.sqrt (1 - r)) -
        ((2 / 135) / 2) * (r ^ 4 * Real.sqrt (1 - r)) -
        ((118 / 23625) / 8) * (r ^ 5 * Real.sqrt (1 - r)) := by
      intro r; ring
    simp_rw [he]
    simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
      [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
       radial_moment_B0, radial_moment_B1, radial_moment_B2]
    norm_num
  unfold I
  linarith

end D5.S3.Quantum.Measurement.QubitIncompatibilityProbability

namespace D5.S3.Quantum.Measurement.QubitIncompatibilityProbability
open Classical D5.S3.Quantum.Measurement.OrderedRootCoordinates D5.S3.Quantum.Measurement.QubitIncompatibilityProbability D5.S3.Quantum.Measurement.QubitIncompatibilityProbability

private theorem triangle_cube_cancellation {p : ℝ × ℝ} (hp : p ∈ squareDomain)
    (t s : ℝ) :
    ENNReal.ofReal p.1 *
      ENNReal.ofReal (squareDensity ((triangleMap p).1,t) ((triangleMap p).2,s)) =
      ENNReal.ofReal 4 * ENNReal.ofReal (cubeIntegrand p.1 p.2 t s) := by
  have hr0 : 0<p.1 := hp.1.1
  have hr1 : p.1<1 := hp.1.2
  rw [← ENNReal.ofReal_mul hr0.le, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤4)]
  unfold squareDensity triangleMap cubeIntegrand w W
  dsimp only
  rw [if_pos (show 0<1-p.1*p.2-p.1*(1-p.2) by nlinarith)]
  have hA : 1-p.1*p.2-p.1*(1-p.2) = 1-p.1 := by ring
  have hB : 1-p.1*p.2*t^2-p.1*(1-p.2)*s^2 =
      1-p.1*(p.2*t^2+(1-p.2)*s^2) := by ring
  rw [hA,hB]
  congr 1
  ring

private def cubeL : ℝ≥0∞ :=
    ∫⁻ r : ℝ in Ioo (0 : ℝ) 1, ∫⁻ a : ℝ in Ioo (0 : ℝ) 1,
      ∫⁻ t : ℝ in Ioo (0 : ℝ) 1, ∫⁻ s : ℝ in Ioo (0 : ℝ) 1,
        ENNReal.ofReal (cubeIntegrand r a t s)

private theorem squareI_eq_cubeL : squareI = ENNReal.ofReal 4 * cubeL := by
  rw [squareI_triangle, triangle_change_lintegral]
  have he : (∫⁻ p : ℝ × ℝ in squareDomain,
      ENNReal.ofReal p.1 * cubeBeforeTriangle (triangleMap p)) =
      ∫⁻ p : ℝ × ℝ in squareDomain,
        ENNReal.ofReal 4 * (∫⁻ t : ℝ in Ioo (0 : ℝ) 1,
          ∫⁻ s : ℝ in Ioo (0 : ℝ) 1, ENNReal.ofReal (cubeIntegrand p.1 p.2 t s)) := by
    apply setLIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
    intro p hp
    dsimp only
    unfold cubeBeforeTriangle
    simp_rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro t
    apply lintegral_congr
    intro s
    exact triangle_cube_cancellation hp t s
  rw [he, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  unfold cubeL
  exact squareDomain_fubini _ (by unfold cubeIntegrand w W; fun_prop)

end D5.S3.Quantum.Measurement.QubitIncompatibilityProbability
namespace D5.S3.Quantum.Measurement.QubitIncompatibilityProbability
open Classical D5.S3.Quantum.Measurement.QubitIncompatibilityProbability

private theorem lintegral_unit_ofReal (f : ℝ → ℝ) (hc : Continuous f)
    (hn : ∀ x ∈ Icc (0 : ℝ) 1, 0≤f x) :
    (∫⁻ x : ℝ in Ioo (0 : ℝ) 1, ENNReal.ofReal (f x)) =
      ENNReal.ofReal (∫ x : ℝ in (0 : ℝ)..1, f x) := by
  rw [Measure.restrict_congr_set (Ioo_ae_eq_Icc : Ioo (0 : ℝ) 1 =ᵐ[volume] Icc (0 : ℝ) 1)]
  rw [← ofReal_integral_eq_lintegral_ofReal hc.integrableOn_Icc]
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact hn x hx

private theorem cube_integrand_nonneg {r a t s : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) (ha : a ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    0≤cubeIntegrand r a t s := by
  unfold cubeIntegrand
  exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hr.1 3) (Real.sqrt_nonneg _))
    (w_nonneg ha ht hs)) (Real.sqrt_nonneg _)

private theorem cubeL_eq_ofReal_integral :
    cubeL = ENNReal.ofReal (∫ r : ℝ in (0 : ℝ)..1, ∫ a : ℝ in (0 : ℝ)..1,
      ∫ t : ℝ in (0 : ℝ)..1, ∫ s : ℝ in (0 : ℝ)..1, cubeIntegrand r a t s) := by
  have hS : ∀ r a t : ℝ, r ∈ Icc (0:ℝ) 1 → a ∈ Icc (0:ℝ) 1 → t ∈ Icc (0:ℝ) 1 →
      0≤∫ s : ℝ in (0:ℝ)..1, cubeIntegrand r a t s := by
    intro r a t hr ha ht
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro s hs
    exact cube_integrand_nonneg hr ha ht hs
  have hT : ∀ r a : ℝ, r ∈ Icc (0:ℝ) 1 → a ∈ Icc (0:ℝ) 1 →
      0≤∫ t : ℝ in (0:ℝ)..1, ∫ s : ℝ in (0:ℝ)..1, cubeIntegrand r a t s := by
    intro r a hr ha
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t ht
    exact hS r a t hr ha ht
  have hA : ∀ r : ℝ, r ∈ Icc (0:ℝ) 1 →
      0≤∫ a : ℝ in (0:ℝ)..1, ∫ t : ℝ in (0:ℝ)..1,
        ∫ s : ℝ in (0:ℝ)..1, cubeIntegrand r a t s := by
    intro r hr
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro a ha
    exact hT r a hr ha
  unfold cubeL
  symm
  rw [← lintegral_unit_ofReal _ (by unfold cubeIntegrand w W; fun_prop) hA]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro r hr
  have hr' : r ∈ Icc (0:ℝ) 1 := ⟨hr.1.le,hr.2.le⟩
  dsimp only
  rw [← lintegral_unit_ofReal _ (by unfold cubeIntegrand w W; fun_prop) (fun a ha => hT r a hr' ha)]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro a ha
  have ha' : a ∈ Icc (0:ℝ) 1 := ⟨ha.1.le,ha.2.le⟩
  dsimp only
  rw [← lintegral_unit_ofReal _ (by unfold cubeIntegrand w W; fun_prop) (fun t ht => hS r a t hr' ha' ht)]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have ht' : t ∈ Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2.le⟩
  dsimp only
  exact (lintegral_unit_ofReal _ (by unfold cubeIntegrand w W; fun_prop)
    (fun s hs => cube_integrand_nonneg hr' ha' ht' hs)).symm

private theorem volume_NJM_cubeI : volume NJM = ENNReal.ofReal (4*Real.pi^2) * ENNReal.ofReal I := by
  rw [volume_NJM_rootI, rootI_eq_squareI, squareI_eq_cubeL, cubeL_eq_ofReal_integral,
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤4)]
  rfl

end D5.S3.Quantum.Measurement.QubitIncompatibilityProbability
namespace D5.S3.Quantum.Measurement.QubitIncompatibilityProbability
private theorem I_nonneg : 0≤I := by
  unfold I
  apply mul_nonneg (by norm_num)
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro r hr
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro a ha
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro t ht
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro s hs
  exact cube_integrand_nonneg hr ha ht hs

private theorem incompProb_eq_nine_I : incompProb = 9*I := by
  unfold incompProb
  rw [volume_NJM_cubeI, volume_V, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : (0:ℝ)≤4*Real.pi^2),
    ENNReal.toReal_ofReal I_nonneg,
    ENNReal.toReal_ofReal (by positivity : (0:ℝ)≤2*Real.pi/3)]
  field_simp [ne_of_gt Real.pi_pos]
  <;> ring

private theorem incompProb_upper_bound : incompProb ≤ 5910272/23648625 := by
  rw [incompProb_eq_nine_I]
  nlinarith [cube_integral_upper_bound]

theorem result : ¬ claim := by
  intro h
  have hu := incompProb_upper_bound
  unfold claim at h
  rw [h] at hu
  norm_num at hu

end D5.S3.Quantum.Measurement.QubitIncompatibilityProbability
