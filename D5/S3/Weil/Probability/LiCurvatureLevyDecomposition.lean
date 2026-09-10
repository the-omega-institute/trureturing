/- GID: D5/S3/Weil/Probability/LiCurvatureLevyDecomposition
   generality: I
   mirror-B: D5/B/S3/Weil/Probability/LiCurvatureLevyDecomposition
   mirror-E: none(waiver:analytic-proof-source)
   anchors: []
   utility: none
   digest: Split the existing reconstructed Li energy into its identity-atom quadratic term and positive jump term; subquadratic growth excludes the identity atom. -/

import D5.S3.Weil.Probability.LiCurvatureProbabilityCompletion
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
A common Herglotz measure may have an atom at the circle identity. That point
has no finite real preimage under a positive-scale Cayley map. The original
geometric-polynomial energy sees this atom as an n^2 term. The jump expression
below retains its cancellation before integration, so finite total jump mass
is never assumed. This is an energy decomposition, not an invocation of a
Levy-Khintchine existence theorem or an identification with actual zeta zeros.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Probability.LiCurvatureLevyDecomposition

open MeasureTheory Set Filter Topology
open scoped ComplexOrder
open D5.S3.Weil.TestFunctions.LiCurvatureCriterion
open D5.S3.Weil.Probability.LiCurvatureProbabilityCompletion

noncomputable local instance circleMeasurableSpace : MeasurableSpace Circle := borel Circle
local instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

/-- The original geometric energy at the identity is exactly quadratic. -/
theorem geometric_energy_at_identity (n : ℕ) :
    Complex.normSq (geometricPolynomial n (1 : Circle)) = (n : ℝ) ^ 2 := by
  simp [geometricPolynomial, Complex.normSq_apply, pow_two]

/-- Away from the identity, the same geometric energy is its compensated
jump expression. The nonzero denominator is derived from the actual point. -/
theorem geometric_energy_off_identity (n : ℕ) (z : Circle) (hz : z ≠ 1) :
    Complex.normSq (geometricPolynomial n z) =
      2 * (1 - ((z : ℂ) ^ n).re) / Complex.normSq ((z : ℂ) - 1) := by
  have hne : (z : ℂ) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    apply hz
    exact Subtype.ext h
  have hden : Complex.normSq ((z : ℂ) - 1) ≠ 0 :=
    (Complex.normSq_pos.mpr hne).ne'
  apply (eq_div_iff hden).mpr
  have hsum : geometricPolynomial n z * ((z : ℂ) - 1) = (z : ℂ) ^ n - 1 := by
    simpa only [geometricPolynomial] using geom_sum_mul (z : ℂ) n
  have hproduct := congrArg Complex.normSq hsum
  rw [map_mul] at hproduct
  have hunit : Complex.normSq ((z : ℂ) ^ n) = 1 := by
    rw [map_pow]
    simp
  calc
    _ = Complex.normSq ((z : ℂ) ^ n - 1) := hproduct
    _ = 2 * (1 - ((z : ℂ) ^ n).re) := by
      rw [Complex.normSq_apply] at hunit
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.one_re, Complex.one_im]
      nlinarith

private theorem energy_integrable (μ : Measure Circle) [IsFiniteMeasure μ] (n : ℕ) :
    Integrable (fun z : Circle => Complex.normSq (geometricPolynomial n z)) μ := by
  have hcontinuous : Continuous (fun z : Circle => Complex.normSq (geometricPolynomial n z)) := by
    unfold geometricPolynomial
    fun_prop
  simpa using hcontinuous.continuousOn.integrableOn_compact (μ := μ) isCompact_univ

/-- The compensated jump integrand is integrable for every finite source
measure, even when the uncompensated weight has infinite integral. -/
theorem li_jump_integrable (μ : Measure Circle) [IsFiniteMeasure μ] (a : ℝ) (n : ℕ) :
    IntegrableOn (fun z : Circle =>
      2 * a * (1 - ((z : ℂ) ^ n).re) / Complex.normSq ((z : ℂ) - 1))
      ({1}ᶜ : Set Circle) μ := by
  refine ((energy_integrable μ n).const_mul a).restrict.congr ?_
  filter_upwards [self_mem_ae_restrict (measurableSet_singleton (1 : Circle)).compl] with z hz
  have hne : z ≠ 1 := by simpa using hz
  rw [geometric_energy_off_identity n z hne]
  ring

/-- Exact Gaussian-atom plus jump decomposition of the pre-existing Li energy.
The source measure is arbitrary finite; a probability or no-atom assumption
is unnecessary for this identity. -/
theorem reconstructed_li_levy_decomposition
    (μ : Measure Circle) [IsFiniteMeasure μ] (a : ℝ) (n : ℕ) :
    reconstructedLi μ a n =
      a * μ.real {1} * (n : ℝ) ^ 2 +
        ∫ z : Circle in {1}ᶜ,
          2 * a * (1 - ((z : ℂ) ^ n).re) / Complex.normSq ((z : ℂ) - 1) ∂μ := by
  have hs : MeasurableSet ({1} : Set Circle) := measurableSet_singleton _
  have hsplit := integral_add_compl hs (energy_integrable μ n)
  have hatom : (∫ z : Circle in {1}, Complex.normSq (geometricPolynomial n z) ∂μ) =
      μ.real {1} * (n : ℝ) ^ 2 := by
    rw [integral_singleton, geometric_energy_at_identity]
    rfl
  have hjump : (∫ z : Circle in {1}ᶜ,
      2 * a * (1 - ((z : ℂ) ^ n).re) / Complex.normSq ((z : ℂ) - 1) ∂μ) =
        a * ∫ z : Circle in {1}ᶜ, Complex.normSq (geometricPolynomial n z) ∂μ := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun hs.compl
    intro z hz
    have hne : z ≠ 1 := by simpa using hz
    change 2 * a * (1 - ((z : ℂ) ^ n).re) / Complex.normSq ((z : ℂ) - 1) =
      a * Complex.normSq (geometricPolynomial n z)
    rw [geometric_energy_off_identity n z hne]
    ring
  calc
    _ = a * ((∫ z : Circle in {1}, Complex.normSq (geometricPolynomial n z) ∂μ) +
        ∫ z : Circle in {1}ᶜ, Complex.normSq (geometricPolynomial n z) ∂μ) := by
      unfold reconstructedLi
      rw [hsplit]
    _ = _ := by rw [hatom, hjump]; ring

/-- The identity atom is a nonnegative quadratic floor for every coefficient. -/
theorem identity_atom_energy_floor (μ : Measure Circle) [IsFiniteMeasure μ]
    (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    a * μ.real {1} * (n : ℝ) ^ 2 ≤ reconstructedLi μ a n := by
  have hjump : 0 ≤ ∫ z : Circle in {1}ᶜ,
      2 * a * (1 - ((z : ℂ) ^ n).re) / Complex.normSq ((z : ℂ) - 1) ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [self_mem_ae_restrict (measurableSet_singleton (1 : Circle)).compl] with z hz
    have hne : z ≠ 1 := by simpa using hz
    calc
      0 ≤ a * Complex.normSq (geometricPolynomial n z) :=
        mul_nonneg ha (Complex.normSq_nonneg _)
      _ = _ := by rw [geometric_energy_off_identity n z hne]; ring
  rw [reconstructed_li_levy_decomposition]
  linarith

/-- Positive first scale and subquadratic growth exclude mass at the identity.
The conclusion concerns the actual Borel measure, not only a chosen density. -/
theorem identity_atom_vanishes_of_subquadratic
    (μ : Measure Circle) [IsFiniteMeasure μ] (a : ℝ) (ha : 0 < a)
    (decay : Tendsto (fun n : ℕ =>
      reconstructedLi μ a (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 2) atTop (𝓝 0)) :
    μ {1} = 0 := by
  have hfloor (n : ℕ) : a * μ.real {1} ≤
      reconstructedLi μ a (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    apply (le_div_iff₀ (by positivity : 0 < ((n + 1 : ℕ) : ℝ) ^ 2)).mpr
    exact identity_atom_energy_floor μ a ha.le (n + 1)
  have hupper : a * μ.real {1} ≤ 0 := ge_of_tendsto' decay hfloor
  have hnonnegative : 0 ≤ μ.real {1} := ENNReal.toReal_nonneg
  have hreal : μ.real {1} = 0 := by nlinarith
  calc
    μ {1} = ENNReal.ofReal ((μ {1}).toReal) :=
      (ENNReal.ofReal_toReal (measure_ne_top μ {1})).symm
    _ = 0 := by rw [show (μ {1}).toReal = 0 from hreal, ENNReal.ofReal_zero]

/-- A normalized positive curvature sequence with positive first coefficient
and subquadratic growth has an actually constructed boundary-atom-free circle
measure and the pure compensated jump representation of every original term.
Neither the measure nor its missing boundary atom is an input. -/
theorem normalized_curvature_jump_representation
    (c : ℤ → ℂ) (L : ℕ → ℝ)
    (normalized : c 0 = 1)
    (positive : ∀ N : ℕ, (toeplitzMatrix c N).PosSemidef)
    (zeroValue : L 0 = 0) (firstPositive : 0 < L 1)
    (recurrence : ∀ n, 1 ≤ n →
      L (n + 1) - 2 * L n + L (n - 1) = 2 * L 1 * (c n).re)
    (decay : Tendsto (fun n : ℕ => L (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 2)
      atTop (𝓝 0)) :
    ∃ μ : ProbabilityMeasure Circle,
      (∀ n : ℤ, circleMoment (μ : Measure Circle) n = c n) ∧
      (μ : Measure Circle) {1} = 0 ∧
      (∀ n : ℕ, L n = ∫ z : Circle in {1}ᶜ,
        2 * L 1 * (1 - ((z : ℂ) ^ n).re) / Complex.normSq ((z : ℂ) - 1)
          ∂(μ : Measure Circle)) := by
  obtain ⟨μ, hμ, _⟩ :=
    normalized_curvature_reconstruction c L normalized positive zeroValue recurrence
  have hdecay : Tendsto (fun n : ℕ =>
      reconstructedLi (μ : Measure Circle) (L 1) (n + 1) /
        ((n + 1 : ℕ) : ℝ) ^ 2) atTop (𝓝 0) := by
    have heq : (fun n : ℕ => reconstructedLi (μ : Measure Circle) (L 1) (n + 1) /
        ((n + 1 : ℕ) : ℝ) ^ 2) =
        (fun n : ℕ => L (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 2) := by
      funext n
      rw [← hμ.2 (n + 1)]
    rw [heq]
    exact decay
  have hmass := identity_atom_vanishes_of_subquadratic
    (μ : Measure Circle) (L 1) firstPositive hdecay
  have hreal : (μ : Measure Circle).real {1} = 0 := by
    change ((μ : Measure Circle) {1}).toReal = 0
    rw [hmass, ENNReal.toReal_zero]
  refine ⟨μ, hμ.1, hmass, fun n => ?_⟩
  rw [hμ.2 n, reconstructed_li_levy_decomposition, hreal, mul_zero, zero_mul, zero_add]

#print axioms reconstructed_li_levy_decomposition
#print axioms li_jump_integrable
#print axioms identity_atom_vanishes_of_subquadratic
#print axioms normalized_curvature_jump_representation

end D5.S3.Weil.Probability.LiCurvatureLevyDecomposition
