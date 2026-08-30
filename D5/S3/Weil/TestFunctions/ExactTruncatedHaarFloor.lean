/- GID: D5/S3/Weil/TestFunctions/ExactTruncatedHaarFloor
   generality: G
   mirror-B: D5/B/S3/Weil/TestFunctions/ExactTruncatedHaarFloor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Identify the exact truncated Haar floor with the least Toeplitz eigenvalue. -/

import D5.S3.Weil.TestFunctions.ToeplitzContactSupport
import D5.S3.Weil.CayleyLaguerre.TruncatedCircleMomentBridge
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.Matrix.Order

/- Library-search audit trail (2026-08-29):
   * D5 searches found no theorem constructing a circle measure from an arbitrary
     positive semidefinite truncated Toeplitz moment matrix.
   * Pinned Mathlib supplies Gram factorization, quotient and isometry completion,
     commuting self-adjoint eigenspace decomposition, and finite atomic measures,
     but no packaged truncated trigonometric moment theorem.
   * `TruncatedCircleMomentBridge` assembles those primitives on the source
     Circle carrier; no new definition or abbreviation is introduced here. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix MeasureTheory Set
open scoped BigOperators ComplexConjugate ComplexOrder ENNReal NNReal MatrixOrder
open D5.S3.Weil.Budget.FullCirclePrimalAttainment
open D5.S3.Weil.CayleyLaguerre.TruncatedCircleMomentBridge

namespace D5.S3.Weil.TestFunctions.ExactTruncatedHaarFloor

noncomputable local instance circleMeasurableSpace : MeasurableSpace Circle := borel Circle
local instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

private theorem circle_moment_toeplitz_posSemidef
    (N : Nat)
    (r : Int -> Complex)
    (hermitian : forall k, r (-k) = star (r k))
    (mu : FiniteMeasure Circle)
    (moments : forall k : Int, k.natAbs <= N ->
      (∫ z : Circle, (z : Complex) ^ (-k) ∂(mu : Measure Circle)) = r k) :
    Matrix.PosSemidef
      (fun j k : Fin (N + 1) => r ((j : Int) - (k : Int))) := by
  classical
  let feature : Circle -> Fin (N + 1) -> Complex := fun z j =>
    (z : Complex) ^ (j : Nat)
  let toeplitz : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex := fun j k =>
    r ((j : Int) - (k : Int))
  have featureContinuous (j : Fin (N + 1)) :
      Continuous (fun z => feature z j) := by
    exact continuous_subtype_val.pow _
  have integrandIntegrable (j k : Fin (N + 1)) :
      Integrable (fun z => feature z k * star (feature z j))
        (mu : Measure Circle) := by
    have continuousIntegrand :
        Continuous (fun z => feature z k * star (feature z j)) := by
      fun_prop
    simpa using continuousIntegrand.continuousOn.integrableOn_compact
      (μ := (mu : Measure Circle)) isCompact_univ
  have momentIntegrandEq (z : Circle) (j k : Fin (N + 1)) :
      (z : Complex) ^ (-((j : Int) - (k : Int))) =
        feature z k * star (feature z j) := by
    rw [neg_sub]
    rw [zpow_sub₀ (Circle.coe_ne_zero z)]
    rw [div_eq_mul_inv]
    congr 1
    change ((↑(z ^ (j : Nat)) : Complex)⁻¹) =
      star (↑(z ^ (j : Nat)) : Complex)
    rw [← Circle.coe_inv, Circle.coe_inv_eq_conj]
    rfl
  have differenceBound (j k : Fin (N + 1)) :
      Int.natAbs ((j : Int) - (k : Int)) <= N := by
    have hj := j.isLt
    have hk := k.isLt
    simp only [Nat.lt_add_one_iff] at hj hk
    omega
  have toeplitzGram (j k : Fin (N + 1)) :
      toeplitz j k =
        ∫ z, feature z k * star (feature z j) ∂(mu : Measure Circle) := by
    change r ((j : Int) - (k : Int)) = _
    rw [← moments (((j : Nat) : Int) - ((k : Nat) : Int))
      (differenceBound j k)]
    apply integral_congr_ae
    filter_upwards [] with z
    exact momentIntegrandEq z j k
  have toeplitzHermitian : toeplitz.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    change star (r ((j : Int) - (i : Int))) =
      r ((i : Int) - (j : Int))
    rw [← hermitian]
    congr 1
    omega
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg toeplitzHermitian
  intro x
  let polynomial : Circle -> Complex := fun z => ∑ j, x j * feature z j
  have energyExpansion :
      (∫ z, polynomial z * star (polynomial z) ∂(mu : Measure Circle)) =
        ∑ j, ∑ k, star (x j) * toeplitz j k * x k := by
    calc
      (∫ z, polynomial z * star (polynomial z) ∂(mu : Measure Circle)) =
          ∫ z, ∑ j, ∑ k,
            star (x j) * (feature z k * star (feature z j)) * x k
            ∂(mu : Measure Circle) := by
              refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
              change (∑ j, x j * feature z j) *
                star (∑ j, x j * feature z j) = _
              simp only [star_sum, star_mul]
              simp_rw [Finset.sum_mul, Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro j _
              apply Finset.sum_congr rfl
              intro k _
              ring
      _ = ∑ j, ∑ k, star (x j) * toeplitz j k * x k := by
            rw [integral_finsetSum Finset.univ]
            · apply Finset.sum_congr rfl
              intro j _
              rw [integral_finsetSum Finset.univ]
              · apply Finset.sum_congr rfl
                intro k _
                rw [toeplitzGram]
                simp only [integral_const_mul, integral_mul_const]
              · intro k _
                exact ((integrandIntegrable j k).const_mul (star (x j))).mul_const (x k)
            · intro j _
              exact integrable_finsetSum Finset.univ fun k _ =>
                ((integrandIntegrable j k).const_mul (star (x j))).mul_const (x k)
  have quadraticEnergy :
      star x ⬝ᵥ (toeplitz *ᵥ x) =
        ∫ z, polynomial z * star (polynomial z) ∂(mu : Measure Circle) := by
    rw [energyExpansion]
    simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
    ring_nf
  rw [quadraticEnergy]
  simp only [RCLike.star_def, Complex.mul_conj]
  exact integral_nonneg fun z =>
    Complex.zero_le_real.mpr (Complex.normSq_nonneg (polynomial z))

private theorem sub_smallest_eigenvalue_posSemidef
    {N : Nat}
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex}
    (hA : A.IsHermitian) :
    Matrix.PosSemidef
      (A - (hA.eigenvalues₀ ⟨N, by simp⟩ : Complex) • 1) := by
  classical
  let lambda : Real := hA.eigenvalues₀ ⟨N, by simp⟩
  let diagonalization :=
    Unitary.conjStarAlgAut Complex
      (Matrix (Fin (N + 1)) (Fin (N + 1)) Complex)
      hA.eigenvectorUnitary
  have lambdaLeEigenvalue (i : Fin (N + 1)) :
      lambda <= hA.eigenvalues i := by
    apply hA.eigenvalues₀_antitone
    apply Fin.le_iff_val_le_val.mpr
    have hi := ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i).isLt
    simp only [Fintype.card_fin] at hi
    dsimp only [lambda]
    omega
  change Matrix.PosSemidef (A - (lambda : Complex) • 1)
  rw [hA.spectral_theorem]
  have scalarFixed :
      (lambda : Complex) • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex) =
        diagonalization
          ((lambda : Complex) •
            (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex)) := by
    simp [diagonalization]
  rw [scalarFixed, ← map_sub]
  rw [Unitary.conjStarAlgAut_apply]
  apply Unitary.isUnit_coe.posSemidef_star_right_conjugate_iff.mpr
  have diagonalDifference :
      Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) -
          (lambda : Complex) • 1 =
        Matrix.diagonal (fun i => ((hA.eigenvalues i - lambda : Real) : Complex)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [diagonalDifference]
  apply Matrix.PosSemidef.diagonal
  intro i
  exact Complex.zero_le_real.mpr (sub_nonneg.mpr (lambdaLeEigenvalue i))

private theorem scalar_le_smallest_eigenvalue_of_residual_posSemidef
    {N : Nat}
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex}
    (hA : A.IsHermitian)
    (alpha : Real)
    (residualPositive : Matrix.PosSemidef
      (A - (alpha : Complex) • 1)) :
    alpha <= hA.eigenvalues₀ ⟨N, by simp⟩ := by
  classical
  let hT : A.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  let lastIndex : Fin (Fintype.card (Fin (N + 1))) := ⟨N, by simp⟩
  let x : EuclideanSpace Complex (Fin (N + 1)) :=
    hT.eigenvectorBasis finrank_euclideanSpace lastIndex
  have xNorm : ‖x‖ = 1 :=
    (hT.eigenvectorBasis finrank_euclideanSpace).orthonormal.1 lastIndex
  have xUnit : star x ⬝ᵥ x = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
    rw [inner_self_eq_norm_sq_to_K, xNorm]
    norm_num
  have operatorAtXEuclidean : A.toEuclideanLin x =
      (hA.eigenvalues₀ lastIndex : Complex) • x := by
    simp [Matrix.IsHermitian.eigenvalues₀, x]
  have operatorAtX : A *ᵥ x =
      (hA.eigenvalues₀ lastIndex : Complex) • (x : Fin (N + 1) -> Complex) := by
    have := congrArg WithLp.ofLp operatorAtXEuclidean
    exact this
  have residualAtX : (A - (alpha : Complex) • 1) *ᵥ x =
      ((hA.eigenvalues₀ lastIndex - alpha : Real) : Complex) • x := by
    rw [Matrix.sub_mulVec, operatorAtX, Matrix.smul_mulVec, Matrix.one_mulVec]
    ext i
    simp [sub_smul]
  have quadraticNonnegative := residualPositive.re_dotProduct_nonneg x
  rw [residualAtX] at quadraticNonnegative
  change 0 <= RCLike.re
    (star (x : Fin (N + 1) -> Complex) ⬝ᵥ
      (((hA.eigenvalues₀ lastIndex - alpha : Real) : Complex) •
        (x : Fin (N + 1) -> Complex))) at quadraticNonnegative
  rw [dotProduct_smul, xUnit] at quadraticNonnegative
  simpa [lastIndex] using quadraticNonnegative

private theorem normalized_circle_haar_monomial_gram (j k : Nat) :
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

private theorem normalized_circle_haar_moment (k : Int) :
    (∫ z : Circle, (z : Complex) ^ (-k)
      ∂(normalizedCircleHaar : Measure Circle)) =
      if k = 0 then 1 else 0 := by
  cases k with
  | ofNat n =>
      rw [Int.ofNat_eq_natCast]
      have gram := normalized_circle_haar_monomial_gram n 0
      have integrandIdentity (z : Circle) :
          (z : Complex) ^ (-(n : Int)) =
            (z : Complex) ^ 0 * star ((z : Complex) ^ n) := by
        rw [_root_.zpow_neg, zpow_natCast]
        rw [← Circle.coe_pow, ← Circle.coe_inv, Circle.coe_inv_eq_conj]
        simp
      calc
        (∫ z : Circle, (z : Complex) ^ (-(n : Int))
            ∂(normalizedCircleHaar : Measure Circle)) =
            ∫ z : Circle, (z : Complex) ^ 0 * star ((z : Complex) ^ n)
              ∂(normalizedCircleHaar : Measure Circle) := by
                apply integral_congr_ae
                filter_upwards [] with z
                exact integrandIdentity z
        _ = if (n : Int) = 0 then 1 else 0 := by simpa using gram
  | negSucc n =>
      have gram := normalized_circle_haar_monomial_gram 0 (n + 1)
      rw [Int.negSucc_eq, neg_neg]
      rw [if_neg (by omega : -((n : Int) + 1) ≠ 0)]
      have powerIdentity (z : Circle) :
          (z : Complex) ^ ((n + 1 : Nat) : Int) =
            (z : Complex) ^ (n + 1) := by
        exact zpow_natCast (z : Complex) (n + 1)
      calc
        (∫ z : Circle, (z : Complex) ^ ((n + 1 : Nat) : Int)
            ∂(normalizedCircleHaar : Measure Circle)) =
            ∫ z : Circle, (z : Complex) ^ (n + 1)
              ∂(normalizedCircleHaar : Measure Circle) := by
                apply integral_congr_ae
                filter_upwards [] with z
                exact powerIdentity z
        _ = 0 := by simpa using gram

/-- A represented Hermitian truncated circle moment vector has maximal
normalized-Haar floor equal to the smallest eigenvalue of its Toeplitz moment
matrix. -/
theorem exact_truncated_haar_floor
    (N : Nat)
    (moment : Int -> Complex)
    (R : Real)
    (hermitian : forall k, moment (-k) = star (moment k))
    (zeroMoment : moment 0 = (R : Complex))
    (positiveMass : 0 < R)
    (represented : exists mu : FiniteMeasure Circle,
      forall k : Int, k.natAbs <= N ->
        (∫ z : Circle, (z : Complex) ^ (-k) ∂(mu : Measure Circle)) = moment k) :
    let toeplitz : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex :=
      fun j k => moment ((j : Int) - (k : Int))
    let toeplitzHermitian : toeplitz.IsHermitian := by
      apply Matrix.IsHermitian.ext
      intro i j
      change star (moment ((j : Int) - (i : Int))) =
        moment ((i : Int) - (j : Int))
      rw [← hermitian]
      congr 1
      omega
    let feasibleFloors : Set NNReal :=
      {alpha | exists mu : FiniteMeasure Circle,
        (forall k : Int, k.natAbs <= N ->
          (∫ z : Circle, (z : Complex) ^ (-k) ∂(mu : Measure Circle)) = moment k) ∧
        (((alpha • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) <=
          (mu : Measure Circle))}
    let truncatedHaarFloor : NNReal := sSup feasibleFloors
    (truncatedHaarFloor : Real) =
      toeplitzHermitian.eigenvalues₀ ⟨N, by simp⟩ := by
  classical
  dsimp only
  let toeplitz : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex :=
    fun j k => moment ((j : Int) - (k : Int))
  have toeplitzHermitian : toeplitz.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    change star (moment ((j : Int) - (i : Int))) =
      moment ((i : Int) - (j : Int))
    rw [← hermitian]
    congr 1
    omega
  let feasibleFloors : Set NNReal :=
    {alpha | exists mu : FiniteMeasure Circle,
      (forall k : Int, k.natAbs <= N ->
        (∫ z : Circle, (z : Complex) ^ (-k) ∂(mu : Measure Circle)) = moment k) ∧
      (((alpha • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) <=
        (mu : Measure Circle))}
  let truncatedHaarFloor : NNReal := sSup feasibleFloors
  obtain ⟨sourceMeasure, sourceMoments⟩ := represented
  have toeplitzPositive : toeplitz.PosSemidef := by
    exact circle_moment_toeplitz_posSemidef N moment hermitian sourceMeasure sourceMoments
  let lastIndex : Fin (Fintype.card (Fin (N + 1))) := ⟨N, by simp⟩
  let lambda : Real := toeplitzHermitian.eigenvalues₀ lastIndex
  let eigenvalueReindex :
      Fin (Fintype.card (Fin (N + 1))) ≃ Fin (N + 1) :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  let smallestIndex : Fin (N + 1) := eigenvalueReindex lastIndex
  have lambdaNonnegative : 0 <= lambda := by
    have h := toeplitzPositive.eigenvalues_nonneg smallestIndex
    simpa only [lambda, Matrix.IsHermitian.eigenvalues, smallestIndex,
      eigenvalueReindex, Equiv.symm_apply_apply] using h
  let lambdaNN : NNReal := ⟨lambda, lambdaNonnegative⟩
  have feasibleNonempty : feasibleFloors.Nonempty := by
    refine ⟨0, sourceMeasure, sourceMoments, ?_⟩
    rw [zero_smul]
    change (0 : Measure Circle) <= (sourceMeasure : Measure Circle)
    exact bot_le
  have feasibleBounded : BddAbove feasibleFloors := by
    let massBound : NNReal := ⟨R, positiveMass.le⟩
    refine ⟨massBound, ?_⟩
    intro alpha alphaFeasible
    obtain ⟨mu, muMoments, domination⟩ := alphaFeasible
    have alphaMass : (alpha • normalizedCircleHaar).mass = alpha := by
      rw [FiniteMeasure.mass, FiniteMeasure.smul_apply]
      change alpha * normalizedCircleHaar.mass = alpha
      rw [normalizedCircleHaar_mass, mul_one]
    have alphaMassLe : (alpha • normalizedCircleHaar).mass <= mu.mass := by
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
      alpha = (alpha • normalizedCircleHaar).mass := alphaMass.symm
      _ <= mu.mass := alphaMassLe
      _ = massBound := muMass
  have monomialIntegrable (mu : FiniteMeasure Circle) (k : Int) :
      Integrable (fun z : Circle => (z : Complex) ^ (-k))
        (mu : Measure Circle) := by
    have continuousMonomial :
        Continuous (fun z : Circle => (z : Complex) ^ (-k)) := by
      exact continuous_subtype_val.zpow₀ (-k) fun z => Or.inl (Circle.coe_ne_zero z)
    simpa using continuousMonomial.continuousOn.integrableOn_compact
      (μ := (mu : Measure Circle)) isCompact_univ
  have feasibleUpper : forall alpha : NNReal,
      alpha ∈ feasibleFloors -> (alpha : Real) <= lambda := by
    intro alpha alphaFeasible
    obtain ⟨mu, muMoments, domination⟩ := alphaFeasible
    let floorMeasure : FiniteMeasure Circle := alpha • normalizedCircleHaar
    let residual : FiniteMeasure Circle :=
      ⟨(mu : Measure Circle) - (floorMeasure : Measure Circle), inferInstance⟩
    have decomposition : floorMeasure + residual = mu := by
      apply FiniteMeasure.toMeasure_injective
      change (floorMeasure : Measure Circle) +
          ((mu : Measure Circle) - (floorMeasure : Measure Circle)) =
        (mu : Measure Circle)
      rw [add_comm, Measure.sub_add_cancel_of_le domination]
    let residualMoment : Int -> Complex := fun k =>
      moment k - if k = 0 then (alpha : Complex) else 0
    have residualMoments : forall k : Int, k.natAbs <= N ->
        (∫ z : Circle, (z : Complex) ^ (-k) ∂(residual : Measure Circle)) =
          residualMoment k := by
      intro k hk
      have decompositionIntegral :
          (∫ z : Circle, (z : Complex) ^ (-k) ∂(mu : Measure Circle)) =
            (∫ z : Circle, (z : Complex) ^ (-k)
              ∂(floorMeasure : Measure Circle)) +
            ∫ z : Circle, (z : Complex) ^ (-k)
              ∂(residual : Measure Circle) := by
        rw [← decomposition]
        rw [FiniteMeasure.toMeasure_add]
        exact integral_add_measure (monomialIntegrable floorMeasure k)
          (monomialIntegrable residual k)
      have floorMoment :
          (∫ z : Circle, (z : Complex) ^ (-k)
            ∂(floorMeasure : Measure Circle)) =
            if k = 0 then (alpha : Complex) else 0 := by
        change (∫ z : Circle, (z : Complex) ^ (-k)
          ∂((alpha • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle)) = _
        rw [FiniteMeasure.toMeasure_smul, integral_smul_nnreal_measure,
          normalized_circle_haar_moment]
        by_cases hzero : k = 0 <;> simp [hzero, NNReal.smul_def]
      rw [muMoments k hk, floorMoment] at decompositionIntegral
      dsimp only [residualMoment]
      rw [decompositionIntegral]
      ring
    have residualHermitian : forall k,
        residualMoment (-k) = star (residualMoment k) := by
      intro k
      dsimp only [residualMoment]
      by_cases hzero : k = 0
      · subst k
        have hMomentZero : moment 0 = star (moment 0) := by
          simpa using hermitian 0
        rw [neg_zero, if_pos rfl, star_sub]
        rw [← hMomentZero]
        simp
      · have hnegzero : -k ≠ 0 := neg_ne_zero.mpr hzero
        simp only [hzero, hnegzero, if_false, sub_zero]
        exact hermitian k
    have residualPositive : Matrix.PosSemidef
        (fun j k : Fin (N + 1) => residualMoment ((j : Int) - (k : Int))) :=
      circle_moment_toeplitz_posSemidef N residualMoment residualHermitian
        residual residualMoments
    have residualMatrixEq :
        ((fun j k : Fin (N + 1) => residualMoment ((j : Int) - (k : Int))) :
          Matrix (Fin (N + 1)) (Fin (N + 1)) Complex) =
          toeplitz - (alpha : Complex) •
            (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex) := by
      ext j k
      simp only [residualMoment, Matrix.sub_apply, Matrix.smul_apply]
      by_cases hjk : j = k
      · subst k
        simp [toeplitz]
      · have hdiff : ((j : Int) - (k : Int)) ≠ 0 := by
          intro h
          apply hjk
          apply Fin.ext
          omega
        simp [toeplitz, hjk, hdiff]
    rw [residualMatrixEq] at residualPositive
    exact scalar_le_smallest_eigenvalue_of_residual_posSemidef
      toeplitzHermitian (alpha : Real) residualPositive
  have lambdaFeasible : lambdaNN ∈ feasibleFloors := by
    let residualMoment : Int -> Complex := fun k =>
      moment k - if k = 0 then (lambda : Complex) else 0
    have residualHermitian : forall k,
        residualMoment (-k) = star (residualMoment k) := by
      intro k
      dsimp only [residualMoment]
      by_cases hzero : k = 0
      · subst k
        have hMomentZero : moment 0 = star (moment 0) := by
          simpa using hermitian 0
        rw [neg_zero, if_pos rfl, star_sub]
        rw [← hMomentZero]
        simp
      · have hnegzero : -k ≠ 0 := neg_ne_zero.mpr hzero
        simp only [hzero, hnegzero, if_false, sub_zero]
        exact hermitian k
    have shiftedPositive :
        Matrix.PosSemidef (toeplitz - (lambda : Complex) • 1) := by
      exact sub_smallest_eigenvalue_posSemidef toeplitzHermitian
    have residualMatrixEq :
        ((fun j k : Fin (N + 1) => residualMoment ((j : Int) - (k : Int))) :
          Matrix (Fin (N + 1)) (Fin (N + 1)) Complex) =
          toeplitz - (lambda : Complex) •
            (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex) := by
      ext j k
      simp only [residualMoment, Matrix.sub_apply, Matrix.smul_apply]
      by_cases hjk : j = k
      · subst k
        simp [toeplitz]
      · have hdiff : ((j : Int) - (k : Int)) ≠ 0 := by
          intro h
          apply hjk
          apply Fin.ext
          omega
        simp [toeplitz, hjk, hdiff]
    rw [← residualMatrixEq] at shiftedPositive
    obtain ⟨residual, residualMoments⟩ :=
      truncated_circle_moment_of_posSemidef N residualMoment residualHermitian shiftedPositive
    let completion : FiniteMeasure Circle :=
      lambdaNN • normalizedCircleHaar + residual
    refine ⟨completion, ?_, ?_⟩
    · intro k hk
      change (∫ z : Circle, (z : Complex) ^ (-k)
        ∂((lambdaNN • normalizedCircleHaar + residual : FiniteMeasure Circle) :
          Measure Circle)) = moment k
      rw [FiniteMeasure.toMeasure_add]
      rw [integral_add_measure (monomialIntegrable (lambdaNN • normalizedCircleHaar) k)
        (monomialIntegrable residual k)]
      rw [FiniteMeasure.toMeasure_smul, integral_smul_nnreal_measure,
        normalized_circle_haar_moment, residualMoments k hk]
      dsimp only [residualMoment]
      by_cases hzero : k = 0
      · subst k
        rw [if_pos rfl, if_pos rfl]
        change ((lambdaNN : Real) : Complex) • (1 : Complex) +
          (moment 0 - (lambda : Complex)) = moment 0
        have hcast : (((lambdaNN : Real)) : Complex) = (lambda : Complex) := by
          rfl
        rw [hcast]
        ring
      · simp [hzero]
    · change
        (((lambdaNN • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) <=
          ((lambdaNN • normalizedCircleHaar + residual : FiniteMeasure Circle) :
            Measure Circle))
      simpa using Measure.le_add_right (le_refl
        (((lambdaNN • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle)))
  have floorEquality : truncatedHaarFloor = lambdaNN := by
    apply le_antisymm
    · apply csSup_le feasibleNonempty
      intro alpha alphaFeasible
      apply NNReal.coe_le_coe.mp
      exact feasibleUpper alpha alphaFeasible
    · exact le_csSup feasibleBounded lambdaFeasible
  have castEquality := congrArg (fun x : NNReal => (x : Real)) floorEquality
  change (truncatedHaarFloor : Real) = lambda
  exact castEquality

#print axioms circle_moment_toeplitz_posSemidef
#print axioms sub_smallest_eigenvalue_posSemidef
#print axioms scalar_le_smallest_eigenvalue_of_residual_posSemidef
#print axioms normalized_circle_haar_moment
#print axioms exact_truncated_haar_floor

end D5.S3.Weil.TestFunctions.ExactTruncatedHaarFloor
