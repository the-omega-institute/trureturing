/- GID: D5/S3/Weil/TestFunctions/UniqueFiniteAtomicResidual
   generality: G
   mirror-B: D5/B/S3/Weil/TestFunctions/UniqueFiniteAtomicResidual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A singular positive Toeplitz matrix has a unique rank-atomic residual and completion. -/

import D5.S3.Weil.TestFunctions.ExactTruncatedHaarFloor
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.MeasureTheory.Measure.WithDensity

/- Library-search audit trail (2026-08-30):
   * D5 searches found the canonical `normalizedCircleHaar`, the positive
     truncated-moment construction, and the contact-support theorem, but no
     frozen uniqueness or exact atom-rank theorem.
   * Body-shape searches for circle Fourier moments, finite atomic measures,
     Toeplitz matrices, and weighted residual completions found no additional
     canonical D5 primitive.
   * Pinned Mathlib has no Caratheodory-Fejer decomposition theorem. This proof
     applies its Lagrange interpolation, Vandermonde determinant, matrix-rank,
     finite-support measure, and with-density lemmas directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix MeasureTheory Set
open scoped BigOperators ComplexConjugate ComplexOrder ENNReal NNReal MatrixOrder
open D5.S3.Weil.Budget.FullCirclePrimalAttainment
open D5.S3.Weil.CayleyLaguerre.TruncatedCircleMomentBridge
open D5.S3.Weil.TestFunctions.ExactTruncatedHaarFloor
open D5.S3.Weil.TestFunctions.ToeplitzContactSupport

namespace D5.S3.Weil.TestFunctions.UniqueFiniteAtomicResidual

noncomputable local instance circleMeasurableSpace : MeasurableSpace Circle := borel Circle
local instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

/-- A coefficient is a feasible normalized-Haar floor when some representing
circle measure dominates that Haar multiple. -/
def TruncatedHaarFloorFeasible
    (N : Nat)
    (moment : Int → Complex)
    (alpha : NNReal) : Prop :=
  ∃ mu : FiniteMeasure Circle,
    (∀ k : Int, k.natAbs ≤ N →
      (∫ z : Circle, (z : Complex) ^ (-k) ∂(mu : Measure Circle)) = moment k) ∧
    (((alpha • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) ≤
      (mu : Measure Circle))

/-- The maximal truncated normalized-Haar floor is the supremum of the
feasible coefficients. -/
noncomputable def maximalTruncatedHaarFloor
    (N : Nat)
    (moment : Int → Complex) : NNReal :=
  sSup {alpha | TruncatedHaarFloorFeasible N moment alpha}

private theorem difference_bound {N : Nat} (j k : Fin (N + 1)) :
    Int.natAbs ((j : Int) - (k : Int)) ≤ N := by
  have hj := j.isLt
  have hk := k.isLt
  simp only [Nat.lt_add_one_iff] at hj hk
  omega

private theorem contact_polynomial_ne_zero
    {N : Nat} (v : Fin (N + 1) → Complex) (unitVector : star v ⬝ᵥ v = 1) :
    (∑ j, Polynomial.C (v j) * Polynomial.X ^ (j : Nat)) ≠ 0 := by
  intro polynomialZero
  have vectorZero : v = 0 := by
    funext j
    have coeffZero := congrArg
      (fun p : Polynomial Complex => p.coeff (j : Nat)) polynomialZero
    have coeffIdentity :
        (∑ i, Polynomial.C (v i) * Polynomial.X ^ (i : Nat)).coeff (j : Nat) = v j := by
      simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        simp only [ite_eq_right_iff]
        intro hji
        exact (hij (Fin.ext hji.symm)).elim
      · simp
    rw [coeffIdentity] at coeffZero
    simpa using coeffZero
  rw [vectorZero] at unitVector
  simp at unitVector

private theorem representing_support_subset_contact
    (N : Nat)
    (moments : Int → Complex)
    (v : Fin (N + 1) → Complex)
    (tau : FiniteMeasure Circle)
    (represents : ∀ k : Int, k.natAbs ≤ N →
      (∫ z : Circle, (z : Complex) ^ (-k) ∂(tau : Measure Circle)) = moments k)
    (unitVector : star v ⬝ᵥ v = 1)
    (kernel :
      (fun j k : Fin (N + 1) => moments ((j : Int) - (k : Int))) *ᵥ v = 0) :
    (tau : Measure Circle).support ⊆
      {z : Circle |
        (∑ j, Polynomial.C (v j) * Polynomial.X ^ (j : Nat)).eval (z : Complex) = 0} := by
  have matrixIdentity :
      (fun j k : Fin (N + 1) =>
        ∫ z : Circle, (z : Complex) ^ (-((j : Int) - (k : Int)))
          ∂(tau : Measure Circle)) =
      (fun j k : Fin (N + 1) => moments ((j : Int) - (k : Int))) := by
    ext j k
    exact represents _ (difference_bound j k)
  have eigenvector :
      (fun j k : Fin (N + 1) =>
        ∫ z : Circle, (z : Complex) ^ (-((j : Int) - (k : Int)))
          ∂(tau : Measure Circle)) *ᵥ v = (0 : Complex) • v := by
    rw [matrixIdentity, kernel]
    simp
  have result := toeplitz_contact_support N tau tau 0 v (by simp) unitVector eigenvector
  exact result.1

private theorem polynomial_integral_eq_of_moments
    (N : Nat)
    (mu nu : FiniteMeasure Circle)
    (momentsEqual : ∀ k : Int, k.natAbs ≤ N →
      (∫ z : Circle, (z : Complex) ^ (-k) ∂(mu : Measure Circle)) =
        ∫ z : Circle, (z : Complex) ^ (-k) ∂(nu : Measure Circle))
    (p : Polynomial Complex)
    (degree : p.natDegree ≤ N) :
    (∫ z : Circle, p.eval (z : Complex) ∂(mu : Measure Circle)) =
      ∫ z : Circle, p.eval (z : Complex) ∂(nu : Measure Circle) := by
  have expansion (z : Circle) :
      p.eval (z : Complex) =
        ∑ k ∈ Finset.range (N + 1), p.coeff k * (z : Complex) ^ k := by
    exact Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le degree) _
  have integrableTerm (measure : FiniteMeasure Circle) (k : Nat) :
      Integrable (fun z : Circle => p.coeff k * (z : Complex) ^ k)
        (measure : Measure Circle) := by
    have continuousTerm : Continuous
        (fun z : Circle => p.coeff k * (z : Complex) ^ k) := by
      fun_prop
    simpa using continuousTerm.continuousOn.integrableOn_compact
      (μ := (measure : Measure Circle)) isCompact_univ
  simp_rw [expansion]
  rw [integral_finsetSum (Finset.range (N + 1))
    (fun k _ => integrableTerm mu k)]
  rw [integral_finsetSum (Finset.range (N + 1))
    (fun k _ => integrableTerm nu k)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_const_mul, integral_const_mul]
  congr 1
  have hMoment := momentsEqual (-(k : Int))
    (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  simpa only [neg_neg, zpow_natCast] using hMoment

private theorem representing_measure_unique
    (N : Nat)
    (moments : Int → Complex)
    (v : Fin (N + 1) → Complex)
    (unitVector : star v ⬝ᵥ v = 1)
    (kernel :
      (fun j k : Fin (N + 1) => moments ((j : Int) - (k : Int))) *ᵥ v = 0)
    (mu nu : FiniteMeasure Circle)
    (muRepresents : ∀ k : Int, k.natAbs ≤ N →
      (∫ z : Circle, (z : Complex) ^ (-k) ∂(mu : Measure Circle)) = moments k)
    (nuRepresents : ∀ k : Int, k.natAbs ≤ N →
      (∫ z : Circle, (z : Complex) ^ (-k) ∂(nu : Measure Circle)) = moments k) :
    mu = nu := by
  classical
  let contactPolynomial : Polynomial Complex :=
    ∑ j, Polynomial.C (v j) * Polynomial.X ^ (j : Nat)
  have polynomialNonzero : contactPolynomial ≠ 0 :=
    contact_polynomial_ne_zero v unitVector
  let roots : Finset Circle :=
    contactPolynomial.roots.toFinset.preimage
      (fun z : Circle => (z : Complex)) Circle.coe_injective.injOn
  have rootsMem (z : Circle) :
      z ∈ roots ↔ contactPolynomial.eval (z : Complex) = 0 := by
    simp only [roots, Finset.mem_preimage]
    rw [Multiset.mem_toFinset, Polynomial.mem_roots polynomialNonzero]
    rfl
  have rootsCard : roots.card ≤ N := by
    calc
      roots.card ≤ contactPolynomial.natDegree := by
        dsimp only [roots]
        rw [Finset.card_preimage]
        exact (Finset.card_filter_le _ _).trans
          ((Multiset.toFinset_card_le contactPolynomial.roots).trans
            (Polynomial.card_roots' contactPolynomial))
      _ ≤ N := by
        apply Polynomial.natDegree_sum_le_of_forall_le
        intro j _
        exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
          (Nat.le_of_lt_succ j.isLt)
  have muSupport := representing_support_subset_contact
    N moments v mu muRepresents unitVector kernel
  have nuSupport := representing_support_subset_contact
    N moments v nu nuRepresents unitVector kernel
  have muAlmostEverywhere : ∀ᵐ z ∂(mu : Measure Circle), z ∈ roots := by
    filter_upwards [Measure.support_mem_ae] with z hz
    exact (rootsMem z).2 (muSupport hz)
  have nuAlmostEverywhere : ∀ᵐ z ∂(nu : Measure Circle), z ∈ roots := by
    filter_upwards [Measure.support_mem_ae] with z hz
    exact (rootsMem z).2 (nuSupport hz)
  have muAtomic : (mu : Measure Circle) =
      ∑ z ∈ roots, (mu : Measure Circle) {z} • Measure.dirac z :=
    Measure.ae_mem_finset_iff.mp muAlmostEverywhere
  have nuAtomic : (nu : Measure Circle) =
      ∑ z ∈ roots, (nu : Measure Circle) {z} • Measure.dirac z :=
    Measure.ae_mem_finset_iff.mp nuAlmostEverywhere
  have singletonMass (z : Circle) (hz : z ∈ roots) :
      (mu : Measure Circle) {z} = (nu : Measure Circle) {z} := by
    let basis := Lagrange.basis roots (fun x : Circle => (x : Complex)) z
    have basisDegree : basis.natDegree ≤ N := by
      calc
        basis.natDegree = roots.card - 1 :=
          Lagrange.natDegree_basis Circle.coe_injective.injOn hz
        _ ≤ roots.card := Nat.sub_le _ _
        _ ≤ N := rootsCard
    have integralEquality := polynomial_integral_eq_of_moments N mu nu
      (fun k hk => (muRepresents k hk).trans (nuRepresents k hk).symm)
      basis basisDegree
    have integralAtomic (measure : FiniteMeasure Circle)
        (atomic : (measure : Measure Circle) =
          ∑ x ∈ roots, (measure : Measure Circle) {x} • Measure.dirac x) :
        (∫ x : Circle, basis.eval (x : Complex) ∂(measure : Measure Circle)) =
          ((measure : Measure Circle) {z}).toReal := by
      calc
        (∫ x : Circle, basis.eval (x : Complex) ∂(measure : Measure Circle)) =
            ∫ x : Circle, basis.eval (x : Complex)
              ∂(∑ x ∈ roots, (measure : Measure Circle) {x} • Measure.dirac x) := by
                exact congrArg
                  (fun source : Measure Circle =>
                    ∫ x : Circle, basis.eval (x : Complex) ∂source)
                  atomic
        _ = ((measure : Measure Circle) {z}).toReal := by
          rw [integral_finsetSum_measure]
          · rw [Finset.sum_eq_single z]
            · rw [integral_smul_measure, integral_dirac]
              change ((measure : Measure Circle) {z}).toReal * basis.eval (z : Complex) = _
              rw [show basis.eval (z : Complex) = 1 by
                exact Lagrange.eval_basis_self Circle.coe_injective.injOn hz]
              simp
            · intro x hx hxz
              rw [integral_smul_measure, integral_dirac]
              change ((measure : Measure Circle) {x}).toReal * basis.eval (x : Complex) = 0
              rw [show basis.eval (x : Complex) = 0 by
                exact Lagrange.eval_basis_of_ne hxz.symm hx]
              simp
            · exact fun h => (h hz).elim
          · intro x hx
            exact Integrable.smul_measure
              (integrable_dirac (a := x)
                (f := fun y : Circle => basis.eval (y : Complex)) enorm_lt_top)
              (measure_ne_top (measure : Measure Circle) {x})
    rw [integralAtomic mu muAtomic, integralAtomic nu nuAtomic] at integralEquality
    apply (ENNReal.toReal_eq_toReal_iff'
      (measure_ne_top (mu : Measure Circle) {z})
      (measure_ne_top (nu : Measure Circle) {z})).mp
    exact Complex.ofReal_injective integralEquality
  apply FiniteMeasure.toMeasure_injective
  rw [muAtomic, nuAtomic]
  apply Finset.sum_congr rfl
  intro z hz
  rw [singletonMass z hz]

private theorem atomic_toeplitz_rank
    (N M : Nat)
    (point : Fin M → Circle)
    (weight : Fin M → NNReal)
    (pointInjective : Function.Injective point)
    (weightPositive : ∀ i, 0 < weight i)
    (atomBound : M ≤ N) :
    Matrix.rank (fun j k : Fin (N + 1) =>
      ∑ i, (weight i : Complex) *
        (point i : Complex) ^ (k : Nat) * star ((point i : Complex) ^ (j : Nat))) = M := by
  classical
  let B : Matrix (Fin M) (Fin (N + 1)) Complex := fun i j =>
    (weight i).sqrt * (point i : Complex) ^ (j : Nat)
  have gramIdentity :
      (fun j k : Fin (N + 1) =>
        ∑ i, (weight i : Complex) *
          (point i : Complex) ^ (k : Nat) * star ((point i : Complex) ^ (j : Nat))) =
        Bᴴ * B := by
    ext j k
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, B]
    apply Finset.sum_congr rfl
    intro i _
    have sqrtSquareNNReal :
        (weight i).sqrt * (weight i).sqrt = weight i := by
      simpa only [pow_two] using NNReal.sq_sqrt (weight i)
    have sqrtSquareComplex :
        ((weight i).sqrt : Complex) * ((weight i).sqrt : Complex) =
          (weight i : Complex) := by
      exact_mod_cast sqrtSquareNNReal
    symm
    calc
      star (((weight i).sqrt : Complex) *
            (point i : Complex) ^ (j : Nat)) *
          (((weight i).sqrt : Complex) *
            (point i : Complex) ^ (k : Nat)) =
          (((weight i).sqrt : Complex) * ((weight i).sqrt : Complex)) *
            (point i : Complex) ^ (k : Nat) *
              star ((point i : Complex) ^ (j : Nat)) := by
                simp only [star_mul]
                simp
                ring
      _ = (weight i : Complex) * (point i : Complex) ^ (k : Nat) *
          star ((point i : Complex) ^ (j : Nat)) := by
            rw [sqrtSquareComplex]
  let columnEmbed : Fin M → Fin (N + 1) := fun j =>
    ⟨j, lt_of_lt_of_le j.isLt (Nat.le_succ_of_le atomBound)⟩
  let nodes : Fin M → Complex := fun i => (point i : Complex)
  let scale : Fin M → Complex := fun i => (weight i).sqrt
  let C : Matrix (Fin M) (Fin M) Complex := Matrix.diagonal scale * Matrix.vandermonde nodes
  have cApply (i j : Fin M) : C i j = B i (columnEmbed j) := by
    dsimp only [C]
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · simp [B, columnEmbed, scale, nodes, Matrix.vandermonde_apply]
    · intro x _ hxi
      simp [hxi.symm]
    · simp
  have nodesInjective : Function.Injective nodes :=
    Circle.coe_injective.comp pointInjective
  have scaleNonzero (i : Fin M) : scale i ≠ 0 := by
    dsimp only [scale]
    exact_mod_cast (NNReal.sqrt_pos.2 (weightPositive i)).ne'
  have detC : C.det ≠ 0 := by
    dsimp only [C]
    rw [Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => scaleNonzero i)
      (Matrix.det_vandermonde_ne_zero_iff.mpr nodesInjective)
  have cRowsIndependent : LinearIndependent Complex C.row :=
    Matrix.linearIndependent_rows_of_det_ne_zero detC
  have bRowsIndependent : LinearIndependent Complex B.row := by
    rw [Fintype.linearIndependent_iff]
    intro coefficient combinationZero i
    rw [Fintype.linearIndependent_iff] at cRowsIndependent
    apply cRowsIndependent coefficient
    funext j
    calc
      (∑ x, coefficient x • C.row x) j =
          (∑ x, coefficient x • B.row x) (columnEmbed j) := by
            simp only [Finset.sum_apply, Pi.smul_apply, Matrix.row_apply, cApply]
      _ = 0 := by rw [combinationZero]; rfl
  rw [gramIdentity, Matrix.rank_conjTranspose_mul_self]
  simpa using bRowsIndependent.rank_matrix

private theorem withDensity_finsetSum
    {ι : Type*}
    (s : Finset ι)
    (measure : ι → Measure Circle)
    (density : Circle → ENNReal) :
    (∑ i ∈ s, measure i).withDensity density =
      ∑ i ∈ s, (measure i).withDensity density := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi inductionHypothesis =>
      simp only [Finset.sum_insert hi, withDensity_add_measure,
        inductionHypothesis]

private theorem withDensity_fintypeSum
    {ι : Type*} [Fintype ι]
    (measure : ι → Measure Circle)
    (density : Circle → ENNReal) :
    (∑ i, measure i).withDensity density =
      ∑ i, (measure i).withDensity density := by
  simpa using withDensity_finsetSum (Finset.univ : Finset ι) measure density

/-- A represented truncated moment vector has a maximal normalized-Haar floor.
After subtracting that exact floor, a singular positive semidefinite residual
Toeplitz matrix constructs one positive residual measure with exactly `rank`
many positive circle atoms. Multiplication by the source denominator density
then constructs the unique maximal-floor completion and its atomic formula. -/
theorem unique_finite_atomic_residual
    (N : Nat)
    (sourceMoment : Int → Complex)
    (R : Real)
    (sourceHermitian : ∀ k, sourceMoment (-k) = star (sourceMoment k))
    (zeroMoment : sourceMoment 0 = (R : Complex))
    (positiveMass : 0 < R)
    (represented : ∃ mu : FiniteMeasure Circle,
      ∀ k : Int, k.natAbs ≤ N →
        (∫ z : Circle, (z : Complex) ^ (-k) ∂(mu : Measure Circle)) = sourceMoment k)
    (v : Fin (N + 1) → Complex)
    (unitVector : star v ⬝ᵥ v = 1)
    (denominator : C(Circle, Complex)) :
    let alphaStar := maximalTruncatedHaarFloor N sourceMoment
    let moments : Int → Complex := fun k =>
      sourceMoment k - if k = 0 then (alphaStar : Complex) else 0
    let residualToeplitz : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex :=
      fun j k => moments ((j : Int) - (k : Int))
    TruncatedHaarFloorFeasible N sourceMoment alphaStar →
    Matrix.PosSemidef residualToeplitz →
    residualToeplitz *ᵥ v = 0 →
    IsGreatest {beta | TruncatedHaarFloorFeasible N sourceMoment beta} alphaStar ∧
    ((alphaStar : Real) =
      (show Matrix.IsHermitian
          (fun j k : Fin (N + 1) => sourceMoment ((j : Int) - (k : Int))) by
        apply Matrix.IsHermitian.ext
        intro i j
        rw [← sourceHermitian]
        congr 1
        omega).eigenvalues₀ ⟨N, by simp⟩) ∧
    ∃ tau : FiniteMeasure Circle,
      (∀ k : Int, k.natAbs ≤ N →
        (∫ z : Circle, (z : Complex) ^ (-k) ∂(tau : Measure Circle)) = moments k) ∧
      (∀ candidate : FiniteMeasure Circle,
        (∀ k : Int, k.natAbs ≤ N →
          (∫ z : Circle, (z : Complex) ^ (-k)
            ∂(candidate : Measure Circle)) = moments k) →
        candidate = tau) ∧
      ∃ (point : Fin residualToeplitz.rank → Circle)
        (weight : Fin residualToeplitz.rank → NNReal),
        Function.Injective point ∧
        (∀ j, 0 < weight j) ∧
        (tau : Measure Circle) =
          ∑ j, (weight j : ENNReal) • Measure.dirac (point j) ∧
        ∃ completion : FiniteMeasure Circle,
          (∃ residual : FiniteMeasure Circle,
            (∀ k : Int, k.natAbs ≤ N →
              (∫ z : Circle, (z : Complex) ^ (-k)
                ∂(residual : Measure Circle)) = moments k) ∧
            (completion : Measure Circle) =
              ((alphaStar • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) +
                (residual : Measure Circle).withDensity
                  (fun z => ENNReal.ofReal (Complex.normSq (denominator z)))) ∧
          (∀ candidate : FiniteMeasure Circle,
            (∃ residual : FiniteMeasure Circle,
              (∀ k : Int, k.natAbs ≤ N →
                (∫ z : Circle, (z : Complex) ^ (-k)
                  ∂(residual : Measure Circle)) = moments k) ∧
              (candidate : Measure Circle) =
                ((alphaStar • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) +
                  (residual : Measure Circle).withDensity
                    (fun z => ENNReal.ofReal (Complex.normSq (denominator z)))) →
            candidate = completion) ∧
          (completion : Measure Circle) =
            ((alphaStar • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) +
              ∑ j, ((weight j : ENNReal) *
                ENNReal.ofReal (Complex.normSq (denominator (point j)))) •
                  Measure.dirac (point j) := by
  classical
  let alphaStar := maximalTruncatedHaarFloor N sourceMoment
  let moments : Int → Complex := fun k =>
    sourceMoment k - if k = 0 then (alphaStar : Complex) else 0
  let residualToeplitz : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex :=
    fun j k => moments ((j : Int) - (k : Int))
  change TruncatedHaarFloorFeasible N sourceMoment alphaStar →
    Matrix.PosSemidef residualToeplitz → residualToeplitz *ᵥ v = 0 → _
  intro alphaStarFeasible positive singularKernel
  obtain ⟨sourceMeasure, sourceRepresents⟩ := represented
  have feasibleBounded :
      BddAbove {alpha | TruncatedHaarFloorFeasible N sourceMoment alpha} := by
    let massBound : NNReal := ⟨R, positiveMass.le⟩
    refine ⟨massBound, ?_⟩
    intro beta betaFeasible
    obtain ⟨mu, muMoments, domination⟩ := betaFeasible
    have betaMass : (beta • normalizedCircleHaar).mass = beta := by
      rw [FiniteMeasure.mass, FiniteMeasure.smul_apply]
      change beta * normalizedCircleHaar.mass = beta
      rw [normalizedCircleHaar_mass, mul_one]
    have betaMassLe : (beta • normalizedCircleHaar).mass ≤ mu.mass := by
      apply ENNReal.coe_le_coe.mp
      simpa only [FiniteMeasure.ennreal_mass] using domination Set.univ
    have muMassReal : (mu.mass : Real) = R := by
      have hzero := muMoments 0 (by simp)
      rw [zeroMoment] at hzero
      simp only [neg_zero, zpow_zero, integral_const] at hzero
      have hzeroReal : (mu : Measure Circle).real Set.univ = R := by
        apply Complex.ofReal_injective
        simpa using hzero
      simpa only [FiniteMeasure.measureReal_eq_coe_coeFn, FiniteMeasure.mass] using hzeroReal
    have muMass : mu.mass = massBound := by
      apply NNReal.eq
      exact muMassReal
    calc
      beta = (beta • normalizedCircleHaar).mass := betaMass.symm
      _ ≤ mu.mass := betaMassLe
      _ = massBound := muMass
  have alphaStarMaximal : ∀ beta : NNReal,
      TruncatedHaarFloorFeasible N sourceMoment beta → beta ≤ alphaStar := by
    intro beta betaFeasible
    exact le_csSup feasibleBounded betaFeasible
  have floorIdentity :
      (alphaStar : Real) =
        (show Matrix.IsHermitian
            (fun j k : Fin (N + 1) => sourceMoment ((j : Int) - (k : Int))) by
          apply Matrix.IsHermitian.ext
          intro i j
          rw [← sourceHermitian]
          congr 1
          omega).eigenvalues₀ ⟨N, by simp⟩ := by
    simpa only [alphaStar, maximalTruncatedHaarFloor, TruncatedHaarFloorFeasible] using
      exact_truncated_haar_floor N sourceMoment R sourceHermitian zeroMoment positiveMass
        ⟨sourceMeasure, sourceRepresents⟩
  have residualHermitian : ∀ k, moments (-k) = star (moments k) := by
    intro k
    dsimp only [moments]
    by_cases hzero : k = 0
    · subst k
      have sourceZeroStar : sourceMoment 0 = star (sourceMoment 0) := by
        simpa using sourceHermitian 0
      rw [neg_zero, if_pos rfl, star_sub, ← sourceZeroStar]
      simp
    · have hnegzero : -k ≠ 0 := neg_ne_zero.mpr hzero
      simp only [hzero, hnegzero, if_false, sub_zero]
      exact sourceHermitian k
  obtain ⟨tau, tauRepresents⟩ :=
    truncated_circle_moment_of_posSemidef N moments residualHermitian positive
  have polynomialNonzero :
      (∑ j, Polynomial.C (v j) * Polynomial.X ^ (j : Nat)) ≠ 0 :=
    contact_polynomial_ne_zero v unitVector
  let contactPolynomial : Polynomial Complex :=
    ∑ j, Polynomial.C (v j) * Polynomial.X ^ (j : Nat)
  let roots : Finset Circle :=
    contactPolynomial.roots.toFinset.preimage
      (fun z : Circle => (z : Complex)) Circle.coe_injective.injOn
  have rootsMem (z : Circle) :
      z ∈ roots ↔ contactPolynomial.eval (z : Complex) = 0 := by
    simp only [roots, Finset.mem_preimage]
    rw [Multiset.mem_toFinset, Polynomial.mem_roots polynomialNonzero]
    rfl
  have rootsCard : roots.card ≤ N := by
    calc
      roots.card ≤ contactPolynomial.natDegree := by
        dsimp only [roots]
        rw [Finset.card_preimage]
        exact (Finset.card_filter_le _ _).trans
          ((Multiset.toFinset_card_le contactPolynomial.roots).trans
            (Polynomial.card_roots' contactPolynomial))
      _ ≤ N := by
        apply Polynomial.natDegree_sum_le_of_forall_le
        intro j _
        exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
          (Nat.le_of_lt_succ j.isLt)
  have tauSupport := representing_support_subset_contact N moments v tau
    tauRepresents unitVector singularKernel
  have tauAlmostEverywhere : ∀ᵐ z ∂(tau : Measure Circle), z ∈ roots := by
    filter_upwards [Measure.support_mem_ae] with z hz
    exact (rootsMem z).2 (tauSupport hz)
  have tauAtomicRoots : (tau : Measure Circle) =
      ∑ z ∈ roots, (tau : Measure Circle) {z} • Measure.dirac z :=
    Measure.ae_mem_finset_iff.mp tauAlmostEverywhere
  let positiveRoots : Finset Circle := roots.filter fun z => (tau : Measure Circle) {z} ≠ 0
  have positiveRootsCard : positiveRoots.card ≤ N :=
    (Finset.card_filter_le _ _).trans rootsCard
  let point : Fin positiveRoots.card → Circle := fun j =>
    (positiveRoots.equivFin.symm j).1
  let weight : Fin positiveRoots.card → NNReal := fun j =>
    ((tau : Measure Circle) {point j}).toNNReal
  have pointInjective : Function.Injective point := by
    exact Subtype.val_injective.comp positiveRoots.equivFin.symm.injective
  have weightPositive (j : Fin positiveRoots.card) : 0 < weight j := by
    apply ENNReal.toNNReal_pos
    · exact (Finset.mem_filter.mp (positiveRoots.equivFin.symm j).2).2
    · exact measure_ne_top (tau : Measure Circle) {point j}
  have tauAtomic : (tau : Measure Circle) =
      ∑ j, (weight j : ENNReal) • Measure.dirac (point j) := by
    rw [tauAtomicRoots]
    have filtered :
        (∑ z ∈ roots, (tau : Measure Circle) {z} • Measure.dirac z) =
          ∑ z ∈ positiveRoots, (tau : Measure Circle) {z} • Measure.dirac z := by
      change (∑ z ∈ roots, (tau : Measure Circle) {z} • Measure.dirac z) =
        ∑ z ∈ roots.filter (fun z => (tau : Measure Circle) {z} ≠ 0),
          (tau : Measure Circle) {z} • Measure.dirac z
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro z hz hnot
      simp only [Finset.mem_filter, not_and, not_not] at hnot
      simp [hnot hz]
    rw [filtered, ← Finset.sum_attach positiveRoots, Finset.attach_eq_univ]
    rw [← (positiveRoots.equivFin.symm.sum_comp fun z : positiveRoots =>
      (tau : Measure Circle) {(z : Circle)} • Measure.dirac (z : Circle))]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    exact (ENNReal.coe_toNNReal
      (measure_ne_top (tau : Measure Circle) {point j})).symm
  have toeplitzAtomic : residualToeplitz = fun j k : Fin (N + 1) =>
      ∑ i, (weight i : Complex) *
        (point i : Complex) ^ (k : Nat) * star ((point i : Complex) ^ (j : Nat)) := by
    ext j k
    rw [show residualToeplitz j k = moments ((j : Int) - (k : Int)) by rfl]
    rw [← tauRepresents _ (difference_bound j k), tauAtomic, integral_finsetSum_measure]
    · apply Finset.sum_congr rfl
      intro i _
      rw [integral_smul_measure, integral_dirac]
      have integrandIdentity :
          (point i : Complex) ^ (-((j : Int) - (k : Int))) =
            (point i : Complex) ^ (k : Nat) *
              star ((point i : Complex) ^ (j : Nat)) := by
        rw [neg_sub, zpow_sub₀ (Circle.coe_ne_zero (point i)), div_eq_mul_inv]
        congr 1
        change ((↑((point i) ^ (j : Nat)) : Complex)⁻¹) =
          star (↑((point i) ^ (j : Nat)) : Complex)
        rw [← Circle.coe_inv, Circle.coe_inv_eq_conj]
        rfl
      rw [integrandIdentity]
      change (weight i : Complex) *
        ((point i : Complex) ^ (k : Nat) *
          star ((point i : Complex) ^ (j : Nat))) = _
      ring
    · intro i _
      exact Integrable.smul_measure
        (integrable_dirac (a := point i)
          (f := fun z : Circle => (z : Complex) ^ (-((j : Int) - (k : Int))))
          enorm_lt_top)
        ENNReal.coe_ne_top
  have rankIdentity : residualToeplitz.rank = positiveRoots.card := by
    rw [toeplitzAtomic]
    exact atomic_toeplitz_rank N positiveRoots.card point weight
      pointInjective weightPositive positiveRootsCard
  let rankEquiv : Fin residualToeplitz.rank ≃ Fin positiveRoots.card :=
    finCongr rankIdentity
  let rankedPoint : Fin residualToeplitz.rank → Circle := point ∘ rankEquiv
  let rankedWeight : Fin residualToeplitz.rank → NNReal := weight ∘ rankEquiv
  have rankedPointInjective : Function.Injective rankedPoint :=
    pointInjective.comp rankEquiv.injective
  have rankedWeightPositive (j : Fin residualToeplitz.rank) : 0 < rankedWeight j :=
    weightPositive (rankEquiv j)
  have rankedAtomic : (tau : Measure Circle) =
      ∑ j, (rankedWeight j : ENNReal) • Measure.dirac (rankedPoint j) := by
    rw [tauAtomic]
    exact (rankEquiv.sum_comp fun j =>
      (weight j : ENNReal) • Measure.dirac (point j)).symm
  let density : Circle → ENNReal := fun z =>
    ENNReal.ofReal (Complex.normSq (denominator z))
  have densityHasFiniteIntegral (measure : FiniteMeasure Circle) :
      HasFiniteIntegral (fun z : Circle => Complex.normSq (denominator z))
        (measure : Measure Circle) := by
    have continuousDensity : Continuous
        (fun z : Circle => Complex.normSq (denominator z)) := by
      fun_prop
    simpa only [Measure.restrict_univ] using
      (continuousDensity.continuousOn.integrableOn_compact
        (μ := (measure : Measure Circle)) isCompact_univ).hasFiniteIntegral
  have weightedFinite (measure : FiniteMeasure Circle) :
      IsFiniteMeasure ((measure : Measure Circle).withDensity density) := by
    exact isFiniteMeasure_withDensity_ofReal (densityHasFiniteIntegral measure)
  let completionMeasure : Measure Circle :=
    ((alphaStar • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) +
      (tau : Measure Circle).withDensity density
  have completionFinite : IsFiniteMeasure completionMeasure := by
    dsimp only [completionMeasure]
    infer_instance
  let completion : FiniteMeasure Circle := ⟨completionMeasure, completionFinite⟩
  have completionAtomic : (completion : Measure Circle) =
      ((alphaStar • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) +
        ∑ j, ((rankedWeight j : ENNReal) * density (rankedPoint j)) •
          Measure.dirac (rankedPoint j) := by
    change completionMeasure = _
    dsimp only [completionMeasure]
    rw [rankedAtomic, withDensity_fintypeSum]
    apply congrArg (fun residual : Measure Circle =>
      ((alphaStar • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) + residual)
    apply Finset.sum_congr rfl
    intro j _
    rw [withDensity_smul_measure, dirac_withDensity]
    simp [smul_smul]
  refine ⟨⟨alphaStarFeasible, alphaStarMaximal⟩, floorIdentity,
    tau, tauRepresents, ?_, rankedPoint, rankedWeight,
    rankedPointInjective, rankedWeightPositive, rankedAtomic,
    completion, ⟨tau, tauRepresents, rfl⟩, ?_, ?_⟩
  · intro candidate candidateRepresents
    exact representing_measure_unique N moments v unitVector singularKernel
      candidate tau candidateRepresents tauRepresents
  · intro candidate candidateProperty
    obtain ⟨residual, residualRepresents, candidateFormula⟩ := candidateProperty
    have residualEq : residual = tau := representing_measure_unique
      N moments v unitVector singularKernel residual tau residualRepresents tauRepresents
    apply FiniteMeasure.toMeasure_injective
    rw [candidateFormula, residualEq]
    rfl
  · simpa only [density, rankedPoint, rankedWeight] using completionAtomic

#print axioms unique_finite_atomic_residual

end D5.S3.Weil.TestFunctions.UniqueFiniteAtomicResidual
