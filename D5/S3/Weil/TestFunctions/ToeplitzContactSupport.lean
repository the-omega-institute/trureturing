/- GID: D5/S3/Weil/TestFunctions/ToeplitzContactSupport
   generality: G
   mirror-B: D5/B/S3/Weil/TestFunctions/ToeplitzContactSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Toeplitz contact zeros support the finite atomic residual optimizer. -/

import D5.S3.Weil.Budget.FullCirclePrimalAttainment
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Fintype.EquivFin
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Algebra.Polynomial

/- Library-search audit trail (2026-08-29):
   * `RationalContactSupport.rational_contact_support` proves the support clause
     for rational features, but its conjugated-coefficient convention does not
     expose the source polynomial and it has no finite atomic optimizer clauses.
   * Body-shape searches for negative Fourier moments, Toeplitz moment matrices,
     and coefficient-polynomial sums found no canonical D5 construction.
   * Pinned Mathlib has no full Toeplitz contact-support theorem. The proof below
     applies `orthonormal_fourier`, `Polynomial.card_roots'`, `Finset.preimage`,
     `Finset.equivFin`, and `Measure.ae_mem_finset_iff` to prove the bridge. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix MeasureTheory Set
open scoped BigOperators ComplexConjugate ENNReal NNReal
open D5.S3.Weil.Budget.FullCirclePrimalAttainment

namespace D5.S3.Weil.TestFunctions.ToeplitzContactSupport

noncomputable local instance circleMeasurableSpace : MeasurableSpace Circle := borel Circle
local instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

private theorem normalizedCircleHaar_monomial_gram (j k : Nat) :
    (∫ z : Circle, (z : Complex) ^ k * star ((z : Complex) ^ j)
      ∂(normalizedCircleHaar : Measure Circle)) =
      if j = k then 1 else 0 := by
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  have hFourier :=
    (orthonormal_iff_ite.mp (orthonormal_fourier (T := 2 * Real.pi)))
      (j : Int) (k : Int)
  rw [ContinuousMap.inner_toLp] at hFourier
  rw [normalizedCircleHaar, FiniteMeasure.toMeasure_map]
  rw [integral_map AddCircle.homeomorphCircle'.continuous.measurable.aemeasurable]
  · convert hFourier using 1
    · apply integral_congr_ae
      filter_upwards [] with x
      rw [show AddCircle.homeomorphCircle' x = x.toCircle by
        induction x using QuotientAddGroup.induction_on
        rw [AddCircle.homeomorphCircle'_apply_mk, AddCircle.toCircle_apply_mk]
        congr 1
        field_simp]
      simp only [fourier_apply, AddCircle.toCircle_zsmul]
      simp
    · simp
  · fun_prop

private theorem moment_integrand_eq_gram (z : Circle) (j k : Nat) :
    (z : Complex) ^ (-((j : Int) - (k : Int))) =
      (z : Complex) ^ k * star ((z : Complex) ^ j) := by
  rw [neg_sub]
  rw [zpow_sub₀ (Circle.coe_ne_zero z)]
  rw [div_eq_mul_inv]
  congr 1
  change ((↑(z ^ j) : Complex)⁻¹) = star (↑(z ^ j) : Complex)
  rw [← Circle.coe_inv, Circle.coe_inv_eq_conj]
  rfl

/-- Construct the truncated Fourier moments and Toeplitz matrix of a circle
measure. If a unit analytic coefficient vector is an eigenvector at a
normalized-Haar floor, then the residual is supported on its contact zeros.
Those finitely many zeros enumerate the residual as an atomic measure, with no
more atoms than the polynomial degree, and give the full optimizer form. -/
theorem toeplitz_contact_support
    (N : Nat)
    (completion residual : FiniteMeasure Circle)
    (alpha : NNReal)
    (v : Fin (N + 1) -> Complex)
    (decomposition : completion = alpha • normalizedCircleHaar + residual) :
    let moment : Int -> Complex := fun k =>
      ∫ z : Circle, (z : Complex) ^ (-k) ∂(completion : Measure Circle)
    let toeplitz : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex := fun j k =>
      moment ((j : Int) - (k : Int))
    let contactPolynomial : Polynomial Complex :=
      ∑ j, Polynomial.C (v j) * Polynomial.X ^ (j : Nat)
    star v ⬝ᵥ v = 1 ->
    toeplitz *ᵥ v = (alpha : Complex) • v ->
    (residual : Measure Circle).support ⊆
        {z : Circle | contactPolynomial.eval (z : Complex) = 0} ∧
      contactPolynomial.natDegree ≤ N ∧
      ∃ (M : Nat) (point : Fin M -> Circle) (weight : Fin M -> ENNReal),
        M ≤ contactPolynomial.natDegree ∧
        (∀ r, contactPolynomial.eval (point r : Complex) = 0) ∧
        (∀ r, weight r ≠ ∞) ∧
        (residual : Measure Circle) =
          ∑ r, weight r • Measure.dirac (point r) ∧
        (completion : Measure Circle) =
          ((alpha • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) +
            ∑ r, weight r • Measure.dirac (point r) := by
  classical
  dsimp only
  let moment : Int -> Complex := fun k =>
    ∫ z : Circle, (z : Complex) ^ (-k) ∂(completion : Measure Circle)
  let toeplitz : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex := fun j k =>
    moment ((j : Int) - (k : Int))
  let contactPolynomial : Polynomial Complex :=
    ∑ j, Polynomial.C (v j) * Polynomial.X ^ (j : Nat)
  change star v ⬝ᵥ v = 1 ->
    toeplitz *ᵥ v = (alpha : Complex) • v ->
    (residual : Measure Circle).support ⊆
        {z : Circle | contactPolynomial.eval (z : Complex) = 0} ∧
      contactPolynomial.natDegree ≤ N ∧
      ∃ (M : Nat) (point : Fin M -> Circle) (weight : Fin M -> ENNReal),
        M ≤ contactPolynomial.natDegree ∧
        (∀ r, contactPolynomial.eval (point r : Complex) = 0) ∧
        (∀ r, weight r ≠ ∞) ∧
        (residual : Measure Circle) =
          ∑ r, weight r • Measure.dirac (point r) ∧
        (completion : Measure Circle) =
          ((alpha • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) +
            ∑ r, weight r • Measure.dirac (point r)
  intro unitVector eigenvector
  let feature : Circle -> Fin (N + 1) -> Complex := fun z j => (z : Complex) ^ (j : Nat)
  let residualGram : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex := fun j k =>
    ∫ z, feature z k * star (feature z j) ∂(residual : Measure Circle)
  have featureContinuous (j : Fin (N + 1)) : Continuous (fun z => feature z j) := by
    exact continuous_subtype_val.pow _
  have integrandIntegrable (measure : FiniteMeasure Circle)
      (j k : Fin (N + 1)) :
      Integrable (fun z => feature z k * star (feature z j))
        (measure : Measure Circle) := by
    have continuousIntegrand : Continuous (fun z => feature z k * star (feature z j)) := by
      fun_prop
    simpa using continuousIntegrand.continuousOn.integrableOn_compact
      (μ := (measure : Measure Circle)) isCompact_univ
  have toeplitzGram (j k : Fin (N + 1)) :
      toeplitz j k =
        ∫ z, feature z k * star (feature z j) ∂(completion : Measure Circle) := by
    apply integral_congr_ae
    filter_upwards [] with z
    exact moment_integrand_eq_gram z j k
  have gramDecomposition :
      toeplitz = (alpha : Complex) • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex) +
        residualGram := by
    ext j k
    rw [toeplitzGram]
    rw [decomposition]
    change
      (∫ z, feature z k * star (feature z j)
        ∂((alpha • normalizedCircleHaar + residual : FiniteMeasure Circle) : Measure Circle)) = _
    rw [FiniteMeasure.toMeasure_add, FiniteMeasure.toMeasure_smul]
    have floorIntegrable :
        Integrable (fun z => feature z k * star (feature z j))
          (alpha • (normalizedCircleHaar : Measure Circle)) := by
      simpa only [FiniteMeasure.toMeasure_smul] using
        (integrandIntegrable (alpha • normalizedCircleHaar) j k)
    rw [integral_add_measure floorIntegrable (integrandIntegrable residual j k)]
    simp only [Matrix.add_apply, Matrix.smul_apply, one_apply, residualGram]
    rw [integral_smul_nnreal_measure]
    simp only [NNReal.smul_def, smul_eq_mul, feature]
    rw [normalizedCircleHaar_monomial_gram]
    by_cases h : j = k
    · subst k
      simp
    · have hval : (j : Nat) ≠ (k : Nat) := fun hv => h (Fin.ext hv)
      simp [h, hval]
  have residualKernel : residualGram *ᵥ v = 0 := by
    rw [gramDecomposition] at eigenvector
    rw [add_mulVec, smul_mulVec, one_mulVec] at eigenvector
    simpa only [add_eq_left] using eigenvector
  have contactEval (z : Circle) :
      contactPolynomial.eval (z : Complex) = ∑ j, v j * feature z j := by
    simp only [contactPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, feature]
  have contactContinuous :
      Continuous (fun z : Circle => contactPolynomial.eval (z : Complex)) := by
    exact contactPolynomial.continuous.comp continuous_subtype_val
  have residualQuadraticZero :
      ∫ z, contactPolynomial.eval (z : Complex) *
          star (contactPolynomial.eval (z : Complex))
        ∂(residual : Measure Circle) = 0 := by
    calc
      ∫ z, contactPolynomial.eval (z : Complex) *
            star (contactPolynomial.eval (z : Complex))
          ∂(residual : Measure Circle) =
          ∫ z, ∑ j, ∑ k,
            star (v j) * (feature z k * star (feature z j)) * v k
            ∂(residual : Measure Circle) := by
              refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
              change contactPolynomial.eval (z : Complex) *
                star (contactPolynomial.eval (z : Complex)) = _
              rw [contactEval]
              simp only [star_sum, star_mul]
              simp_rw [Finset.sum_mul, Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro j _
              apply Finset.sum_congr rfl
              intro k _
              ring
      _ = ∑ j, ∑ k, star (v j) * residualGram j k * v k := by
            rw [integral_finsetSum Finset.univ]
            · apply Finset.sum_congr rfl
              intro j _
              rw [integral_finsetSum Finset.univ]
              · apply Finset.sum_congr rfl
                intro k _
                simp only [residualGram]
                simp only [integral_const_mul, integral_mul_const]
              · intro k _
                exact ((integrandIntegrable residual j k).const_mul (star (v j))).mul_const (v k)
            · intro j _
              exact integrable_finsetSum Finset.univ fun k _ =>
                ((integrandIntegrable residual j k).const_mul (star (v j))).mul_const (v k)
      _ = star v ⬝ᵥ (residualGram *ᵥ v) := by
            simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
            ring_nf
      _ = 0 := by rw [residualKernel]; simp
  have residualNormSqZero :
      ∫ z, Complex.normSq (contactPolynomial.eval (z : Complex))
        ∂(residual : Measure Circle) = 0 := by
    have complexIntegral :
        (∫ z, (Complex.normSq (contactPolynomial.eval (z : Complex)) : Complex)
          ∂(residual : Measure Circle)) = 0 := by
      rw [Complex.star_def] at residualQuadraticZero
      simpa only [Complex.mul_conj] using residualQuadraticZero
    rw [integral_complex_ofReal] at complexIntegral
    exact Complex.ofReal_injective complexIntegral
  have normSqIntegrable :
      Integrable (fun z : Circle => Complex.normSq (contactPolynomial.eval (z : Complex)))
        (residual : Measure Circle) := by
    have normSqContinuous :
        Continuous (fun z : Circle => Complex.normSq (contactPolynomial.eval (z : Complex))) := by
      fun_prop
    simpa using normSqContinuous.continuousOn.integrableOn_compact
      (μ := (residual : Measure Circle)) isCompact_univ
  have contactZeroAlmostEverywhere :
      (fun z : Circle => contactPolynomial.eval (z : Complex))
        =ᵐ[(residual : Measure Circle)] 0 := by
    have normSqZeroAlmostEverywhere :=
      (integral_eq_zero_iff_of_nonneg
        (fun z : Circle => Complex.normSq_nonneg (contactPolynomial.eval (z : Complex)))
        normSqIntegrable).1 residualNormSqZero
    filter_upwards [normSqZeroAlmostEverywhere] with z hz
    exact Complex.normSq_eq_zero.mp hz
  have polynomialZeroClosed :
      IsClosed {z : Circle | contactPolynomial.eval (z : Complex) = 0} := by
    exact isClosed_eq contactContinuous continuous_const
  have supportSubset :
      (residual : Measure Circle).support ⊆
        {z : Circle | contactPolynomial.eval (z : Complex) = 0} :=
    Measure.support_subset_of_isClosed polynomialZeroClosed contactZeroAlmostEverywhere
  have degreeBound : contactPolynomial.natDegree ≤ N := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j _
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.le_of_lt_succ j.isLt)
  have contactPolynomialNonzero : contactPolynomial ≠ 0 := by
    intro polynomialZero
    have vectorZero : v = 0 := by
      funext j
      have coeffZero := congrArg (fun p : Polynomial Complex => p.coeff (j : Nat)) polynomialZero
      have coeffIdentity : contactPolynomial.coeff (j : Nat) = v j := by
        simp only [contactPolynomial, Polynomial.finsetSum_coeff,
          Polynomial.coeff_C_mul_X_pow]
        rw [Finset.sum_eq_single j]
        · simp
        · intro b _ hbj
          simp only [ite_eq_right_iff]
          intro hjb
          exact (hbj (Fin.ext hjb.symm)).elim
        · simp
      rw [coeffIdentity] at coeffZero
      simpa using coeffZero
    rw [vectorZero] at unitVector
    simp at unitVector
  let circleRoots : Finset Circle :=
    contactPolynomial.roots.toFinset.preimage
      (fun z : Circle => (z : Complex)) Circle.coe_injective.injOn
  have circleRootsMem (z : Circle) :
      z ∈ circleRoots ↔ contactPolynomial.eval (z : Complex) = 0 := by
    simp only [circleRoots, Finset.mem_preimage]
    rw [Multiset.mem_toFinset, Polynomial.mem_roots contactPolynomialNonzero]
    rfl
  have circleRootsCard : circleRoots.card ≤ contactPolynomial.natDegree := by
    dsimp only [circleRoots]
    rw [Finset.card_preimage]
    exact (Finset.card_filter_le _ _).trans
      ((Multiset.toFinset_card_le contactPolynomial.roots).trans
        (Polynomial.card_roots' contactPolynomial))
  have residualAlmostEverywhereInRoots :
      ∀ᵐ z ∂(residual : Measure Circle), z ∈ circleRoots := by
    filter_upwards [contactZeroAlmostEverywhere] with z hz
    rw [circleRootsMem]
    exact hz
  have atomicResidual :
      (residual : Measure Circle) =
        ∑ z ∈ circleRoots, (residual : Measure Circle) {z} • Measure.dirac z :=
    Measure.ae_mem_finset_iff.mp residualAlmostEverywhereInRoots
  let point : Fin circleRoots.card -> Circle := fun r =>
    (circleRoots.equivFin.symm r).1
  let weight : Fin circleRoots.card -> ENNReal := fun r =>
    (residual : Measure Circle) {point r}
  have rootsAsFinSum :
      (∑ z ∈ circleRoots, (residual : Measure Circle) {z} • Measure.dirac z) =
        ∑ r, weight r • Measure.dirac (point r) := by
    rw [← Finset.sum_attach circleRoots, Finset.attach_eq_univ]
    rw [← (circleRoots.equivFin.symm.sum_comp fun z : circleRoots =>
      (residual : Measure Circle) {(z : Circle)} • Measure.dirac (z : Circle))]
  have weightFinite (r : Fin circleRoots.card) : weight r ≠ ∞ := by
    exact measure_ne_top (residual : Measure Circle) {point r}
  have pointRoot (r : Fin circleRoots.card) :
      contactPolynomial.eval (point r : Complex) = 0 := by
    rw [← circleRootsMem]
    exact (circleRoots.equivFin.symm r).2
  refine ⟨supportSubset, degreeBound, circleRoots.card, point, weight,
    circleRootsCard, pointRoot, weightFinite, ?_, ?_⟩
  · rw [← rootsAsFinSum]
    exact atomicResidual
  · rw [decomposition, FiniteMeasure.toMeasure_add, FiniteMeasure.toMeasure_smul,
      atomicResidual, rootsAsFinSum]

#print axioms toeplitz_contact_support

end D5.S3.Weil.TestFunctions.ToeplitzContactSupport
