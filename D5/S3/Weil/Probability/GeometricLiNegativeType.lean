/- GID: D5/S3/Weil/Probability/GeometricLiNegativeType
   generality: I
   mirror-B: D5/B/S3/Weil/Probability/GeometricLiNegativeType
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original reconstructed Li energy is a squared Gram distance on every finite integer sample, yielding exact negative-type and Gaussian positivity identities. -/

import D5.S3.Weil.Probability.FiniteGaussianSchoenberg
import D5.S3.Weil.Probability.LiCurvatureProbabilityCompletion
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
Extend the existing finite geometric polynomial to its integer cocycle. The
identity point is retained and contributes b_n(1)=n. Integration is against the
original arbitrary finite Borel circle measure. No zero-atom, finite jump mass,
subquadratic-growth, independent-coordinate or RH premise is imposed.
The Gram matrix is constructed from these very same functions; it is not a
supplied Hilbert representation of the desired distance.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Probability.GeometricLiNegativeType

open MeasureTheory Matrix
open D5.S3.Weil.TestFunctions.LiCurvatureCriterion
open D5.S3.Weil.Probability.FiniteGaussianSchoenberg
open scoped BigOperators ComplexOrder

noncomputable local instance circleMeasurableSpace : MeasurableSpace Circle := borel Circle
local instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

/-- Integer continuation of the existing geometric polynomial, including its
removable value at the identity. -/
def integerGeometric (n : ℤ) (z : Circle) : ℂ := by
  classical
  exact if z = 1 then (n : ℂ) else ((z : ℂ) ^ n - 1) / ((z : ℂ) - 1)

@[simp] theorem integerGeometric_zero (z : Circle) : integerGeometric 0 z = 0 := by
  by_cases hz : z = 1 <;> simp [integerGeometric, hz]

/-- Nonnegative indices agree with the original source polynomial. -/
theorem integerGeometric_nat (n : ℕ) (z : Circle) :
    integerGeometric (n : ℤ) z = geometricPolynomial n z := by
  classical
  by_cases hz : z = 1
  · subst z
    simp [integerGeometric, geometricPolynomial]
  · have hden : (z : ℂ) - 1 ≠ 0 := by
      apply sub_ne_zero.mpr
      intro h
      exact hz (Subtype.ext h)
    have hsum : geometricPolynomial n z * ((z : ℂ) - 1) = (z : ℂ) ^ n - 1 := by
      simpa only [geometricPolynomial] using geom_sum_mul (z : ℂ) n
    simpa only [integerGeometric, if_neg hz, zpow_natCast] using
      (div_eq_iff hden).mpr hsum.symm

/-- The actual integer cocycle law, valid also at the identity and for negative
indices. -/
theorem integerGeometric_add (z : Circle) (m n : ℤ) :
    integerGeometric (m + n) z = integerGeometric m z + (z : ℂ) ^ m * integerGeometric n z := by
  classical
  by_cases hz : z = 1
  · subst z
    simp [integerGeometric]
  · have hden : (z : ℂ) - 1 ≠ 0 := by
      apply sub_ne_zero.mpr
      intro h
      exact hz (Subtype.ext h)
    simp only [integerGeometric, if_neg hz, zpow_add₀ (Circle.coe_ne_zero z)]
    field_simp [hden]
    ring

/-- The negative branch is a unit-modulus multiple of the positive branch. -/
theorem integerGeometric_neg (z : Circle) (n : ℤ) :
    integerGeometric (-n) z = -(z : ℂ) ^ (-n) * integerGeometric n z := by
  have h := integerGeometric_add z (-n) n
  simp only [neg_add_cancel, integerGeometric_zero] at h
  calc
    _ = -((z : ℂ) ^ (-n) * integerGeometric n z) :=
      eq_neg_of_add_eq_zero_left h.symm
    _ = _ := by ring

/-- Integer continuation remains continuous across the identity. -/
theorem integerGeometric_continuous (n : ℤ) : Continuous (integerGeometric n) := by
  rcases n.eq_nat_or_neg with ⟨k, rfl | rfl⟩
  · rw [show integerGeometric (k : ℤ) = geometricPolynomial k from
      funext (integerGeometric_nat k)]
    unfold geometricPolynomial
    fun_prop
  · rw [show integerGeometric (-(k : ℤ)) =
        (fun z : Circle => -(z : ℂ) ^ (-(k : ℤ)) * geometricPolynomial k z) by
      funext z
      rw [integerGeometric_neg, integerGeometric_nat]]
    have hp : Continuous (fun z : Circle => (z : ℂ) ^ (-(k : ℤ))) := by
      apply Continuous.zpow₀ continuous_subtype_val
      intro z
      exact Or.inl (Circle.coe_ne_zero z)
    have hg : Continuous (geometricPolynomial k) := by unfold geometricPolynomial; fun_prop
    exact hp.neg.mul hg

/-- Both integer branches have the original energy at the absolute index. -/
theorem integerGeometric_energy (z : Circle) (n : ℤ) :
    Complex.normSq (integerGeometric n z) = Complex.normSq (geometricPolynomial n.natAbs z) := by
  rcases n.eq_nat_or_neg with ⟨k, rfl | rfl⟩
  · simp [integerGeometric_nat]
  · simp [integerGeometric_neg, integerGeometric_nat, Complex.normSq_eq_norm_sq,
      norm_mul, norm_zpow, Circle.norm_coe]

/-- The original energy is exactly the squared distance between two cocycle
values, with no off-identity restriction. -/
theorem integerGeometric_distance (z : Circle) (m n : ℤ) :
    Complex.normSq (integerGeometric m z - integerGeometric n z) =
      Complex.normSq (geometricPolynomial (m - n).natAbs z) := by
  have h := integerGeometric_add z n (m - n)
  rw [show n + (m - n) = m by ring] at h
  have difference : integerGeometric m z - integerGeometric n z =
      (z : ℂ) ^ n * integerGeometric (m - n) z := by rw [h]; ring
  rw [difference, map_mul]
  have hunit : Complex.normSq ((z : ℂ) ^ n) = 1 := by
    simp [Complex.normSq_eq_norm_sq, norm_zpow, Circle.norm_coe]
  rw [hunit, one_mul, integerGeometric_energy]

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A real Gram matrix built from the original measure and integer geometric
functions. The scale is not hidden in an assumed embedding. -/
def geometricLiGram (μ : Measure Circle) (a : ℝ) (index : I → ℤ) : Matrix I I ℝ :=
  fun i j => a * ∫ z : Circle, inner ℝ (integerGeometric (index i) z)
    (integerGeometric (index j) z) ∂μ

private theorem inner_integrable (μ : Measure Circle) [IsFiniteMeasure μ] (m n : ℤ) :
    Integrable (fun z : Circle => inner ℝ (integerGeometric m z) (integerGeometric n z)) μ := by
  have hc : Continuous (fun z : Circle =>
      inner ℝ (integerGeometric m z) (integerGeometric n z)) :=
    (integerGeometric_continuous m).inner (integerGeometric_continuous n)
  simpa using hc.continuousOn.integrableOn_compact (μ := μ) isCompact_univ

/-- Exact Gram quadratic identity for the unchanged integral representation. -/
theorem geometricLiGram_quadratic (μ : Measure Circle) [IsFiniteMeasure μ]
    (a : ℝ) (index : I → ℤ) (x : I → ℝ) :
    star x ⬝ᵥ (geometricLiGram μ a index *ᵥ x) =
      a * ∫ z : Circle, Complex.normSq (∑ i, x i • integerGeometric (index i) z) ∂μ := by
  have hfinite (z : Circle) :
      Complex.normSq (∑ i, x i • integerGeometric (index i) z) =
        ∑ i, ∑ j, x i * inner ℝ (integerGeometric (index i) z)
          (integerGeometric (index j) z) * x j := by
    rw [Complex.normSq_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ← Matrix.star_dotProduct_gram_mulVec]
    simp only [dotProduct, mulVec, Matrix.gram_apply, star_trivial, Finset.mul_sum, mul_assoc]
  rw [show (fun z : Circle => Complex.normSq (∑ i, x i • integerGeometric (index i) z)) =
      (fun z => ∑ i, ∑ j, x i * inner ℝ (integerGeometric (index i) z)
        (integerGeometric (index j) z) * x j) from funext hfinite]
  rw [integral_finsetSum Finset.univ]
  · simp only [dotProduct, mulVec, geometricLiGram, star_trivial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum Finset.univ]
    · simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_mul_const, integral_const_mul]
      ring
    · intro j _
      exact ((inner_integrable μ (index i) (index j)).const_mul (x i)).mul_const (x j)
  · intro i _
    exact integrable_finsetSum Finset.univ fun j _ =>
      ((inner_integrable μ (index i) (index j)).const_mul (x i)).mul_const (x j)

/-- Nonnegative scale makes this actual integrated matrix positive. -/
theorem geometricLiGram_posSemidef (μ : Measure Circle) [IsFiniteMeasure μ]
    (a : ℝ) (ha : 0 ≤ a) (index : I → ℤ) : (geometricLiGram μ a index).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (by
      apply Matrix.IsHermitian.ext
      intro i j
      simp only [geometricLiGram, star_trivial, real_inner_comm])
  intro x
  rw [geometricLiGram_quadratic]
  exact mul_nonneg ha (integral_nonneg fun z => Complex.normSq_nonneg _)

/-- The Gram distance is exactly the original reconstructed Li value, including
negative or repeated sample indices and the identity atom. -/
theorem geometricLiGram_distance (μ : Measure Circle) [IsFiniteMeasure μ]
    (a : ℝ) (index : I → ℤ) (i j : I) :
    geometricLiGram μ a index i i + geometricLiGram μ a index j j -
      2 * geometricLiGram μ a index i j = reconstructedLi μ a (index i - index j).natAbs := by
  have point (z : Circle) :
      inner ℝ (integerGeometric (index i) z) (integerGeometric (index i) z) +
      inner ℝ (integerGeometric (index j) z) (integerGeometric (index j) z) -
      2 * inner ℝ (integerGeometric (index i) z) (integerGeometric (index j) z) =
        Complex.normSq (geometricPolynomial (index i - index j).natAbs z) := by
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    calc
      _ = ‖integerGeometric (index i) z - integerGeometric (index j) z‖ ^ 2 := by
        rw [norm_sub_sq_real]
        ring
      _ = _ := by rw [← Complex.normSq_eq_norm_sq, integerGeometric_distance]
  have hint :
      (∫ z : Circle, inner ℝ (integerGeometric (index i) z) (integerGeometric (index i) z) +
        inner ℝ (integerGeometric (index j) z) (integerGeometric (index j) z) -
        2 * inner ℝ (integerGeometric (index i) z) (integerGeometric (index j) z) ∂μ) =
      ∫ z : Circle, Complex.normSq (geometricPolynomial (index i - index j).natAbs z) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall point)
  have hsplit := integral_sub ((inner_integrable μ (index i) (index i)).add
      (inner_integrable μ (index j) (index j)))
      ((inner_integrable μ (index i) (index j)).const_mul 2)
  simp only [Pi.add_apply] at hsplit
  rw [hsplit,
    integral_add (inner_integrable μ (index i) (index i)) (inner_integrable μ (index j) (index j)),
    integral_const_mul] at hint
  unfold geometricLiGram reconstructedLi
  rw [← hint]
  ring

/-- The full finite zero-sum Li form equals minus twice an actual nonnegative
integral. This is a certificate of conditional negative type, not an assumption. -/
theorem reconstructed_li_zero_sum_identity (μ : Measure Circle) [IsFiniteMeasure μ]
    (a : ℝ) (index : I → ℤ) (x : I → ℝ) (hx : ∑ i, x i = 0) :
    (∑ i, ∑ j, x i * x j * reconstructedLi μ a (index i - index j).natAbs) =
      -2 * a * ∫ z : Circle, Complex.normSq (∑ i, x i • integerGeometric (index i) z) ∂μ := by
  simp_rw [← geometricLiGram_distance μ a index]
  rw [gram_distance_zero_sum _ x hx, geometricLiGram_quadratic]
  ring

/-- Conditional negative type on every finite sample of the whole integer
carrier. No truncation cutoff or supplied negative-type property occurs. -/
theorem reconstructed_li_conditionally_negative (μ : Measure Circle) [IsFiniteMeasure μ]
    (a : ℝ) (ha : 0 ≤ a) (index : I → ℤ) (x : I → ℝ) (hx : ∑ i, x i = 0) :
    (∑ i, ∑ j, x i * x j * reconstructedLi μ a (index i - index j).natAbs) ≤ 0 := by
  rw [reconstructed_li_zero_sum_identity μ a index x hx]
  have hp : 0 ≤ ∫ z : Circle, Complex.normSq (∑ i, x i • integerGeometric (index i) z) ∂μ :=
    integral_nonneg fun z => Complex.normSq_nonneg _
  nlinarith [mul_nonneg ha hp]

/-- Exponential positivity is now derived for every finite sample, against
complex vectors, directly from the same original Li energy. -/
theorem reconstructed_li_exponential_posSemidef (μ : Measure Circle) [IsFiniteMeasure μ]
    (a : ℝ) (ha : 0 ≤ a) (index : I → ℤ) (t : ℝ) (ht : 0 ≤ t) :
    Matrix.PosSemidef
      (fun i j => (Real.exp (-t * reconstructedLi μ a (index i - index j).natAbs) : ℂ)) := by
  have h := gram_gaussian_posSemidef (geometricLiGram μ a index)
    (geometricLiGram_posSemidef μ a ha index) t ht
  simpa only [geometricLiGram_distance] using h

#print axioms integerGeometric_distance
#print axioms reconstructed_li_zero_sum_identity
#print axioms reconstructed_li_conditionally_negative
#print axioms reconstructed_li_exponential_posSemidef

end D5.S3.Weil.Probability.GeometricLiNegativeType
