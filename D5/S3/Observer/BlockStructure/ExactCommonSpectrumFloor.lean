/- GID: D5/S3/Observer/BlockStructure/ExactCommonSpectrumFloor
   generality: I
   mirror-B: D5/B/S3/Observer/BlockStructure/ExactCommonSpectrumFloor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Characterize the exact common spectral floor by two whitened least eigenvalues. -/

import D5.S3.Observer.BlockStructure.RationalToeplitzCollapse
import D5.S3.Observer.BlockStructure.CommonSpectrumMasterFeasibility
import D5.S3.Weil.TestFunctions.ExactTruncatedHaarFloor
import Mathlib.Analysis.Matrix.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Matrix MeasureTheory Set
open scoped BigOperators ComplexConjugate ComplexOrder ENNReal NNReal MatrixOrder
open D5.S3.Weil.TestFunctions.LiCurvatureCriterion
open D5.S3.Weil.Budget.FullCirclePrimalAttainment
open D5.S3.Weil.CayleyLaguerre.TruncatedCircleMomentBridge
open D5.S3.Observer.BlockStructure.CommonSpectrumMasterFeasibility
open D5.S3.Observer.BlockStructure.RationalToeplitzCollapse

namespace D5.S3.Observer.BlockStructure.ExactCommonSpectrumFloor

noncomputable local instance circleMeasurableSpace : MeasurableSpace Circle := borel Circle
local instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

private theorem rational_gram_eq_weighted_reflected_congruence
    (N : Nat) (mu : FiniteMeasure Circle)
    (coefficient : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex)
    (denominator : Polynomial Complex)
    (denominatorNonzero : forall z : Circle,
      denominator.eval (z : Complex) ≠ 0) :
    let monomial : Circle → Fin (N + 1) → Complex := fun z j ↦
      (z : Complex) ^ (j : Nat)
    let feature : Circle → Fin (N + 1) → Complex := fun z i ↦
      (coefficient *ᵥ monomial z) i / denominator.eval (z : Complex)
    let rationalGram : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex := fun i j ↦
      ∫ z, feature z i * star (feature z j) ∂( mu : Measure Circle)
    let density : Circle → ENNReal := fun z ↦
      ENNReal.ofReal
        (Complex.normSq (denominator.eval (z : Complex)))⁻¹
    let weightedReflected : Measure Circle :=
      ((mu : Measure Circle).withDensity density).map Inv.inv
    let momentMatrix : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex :=
      toeplitzMatrix (circleMoment weightedReflected) N
    rationalGram = coefficient * momentMatrix * coefficientᴴ := by
  classical
  dsimp only
  have collapse := rational_toeplitz_collapse (N + 1) mu coefficient
    denominator denominatorNonzero
  dsimp only at collapse
  rw [collapse]
  congr 1
  congr 1
  ext i j
  let weighted : Measure Circle :=
    (mu : Measure Circle).withDensity fun z ↦
      ENNReal.ofReal
        (Complex.normSq (denominator.eval (z : Complex)))⁻¹
  have circleMomentMapInv (k : Int) :
      circleMoment (weighted.map Inv.inv) k = circleMoment weighted (-k) := by
    simp only [circleMoment]
    have integrandContinuous : Continuous fun z : Circle ↦
        (z : Complex) ^ (-k) :=
      continuous_subtype_val.zpow₀ (-k) fun z ↦ Or.inl (Circle.coe_ne_zero z)
    rw [integral_map measurable_inv.aemeasurable
      integrandContinuous.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [show ((↑(z⁻¹) : Complex)) = (z : Complex)⁻¹ by exact Circle.coe_inv z]
    rw [_root_.inv_zpow']
  simp only [toeplitzMatrix]
  change (∫ z : Circle, (z : Complex) ^ (i : Nat) *
      star ((z : Complex) ^ (j : Nat)) ∂weighted) =
    circleMoment (weighted.map Inv.inv)
      (((i : Nat) : Int) - ((j : Nat) : Int))
  rw [circleMomentMapInv]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [neg_sub]
  rw [zpow_sub₀ (Circle.coe_ne_zero z)]
  rw [zpow_natCast, zpow_natCast, div_eq_mul_inv]
  congr 1
  rw [← Circle.coe_pow, ← Circle.coe_inv, Circle.coe_inv_eq_conj]
  rfl

private theorem weighted_floor_iff_residual
    (N : Nat)
    (denominator : Polynomial Complex)
    (denominatorNonzero : forall z : Circle,
      denominator.eval (z : Complex) ≠ 0)
    (source : FiniteMeasure Circle)
    (alpha : NNReal) :
    let densityReal : Circle → Real := fun z ↦
      (Complex.normSq (denominator.eval (z : Complex)))⁻¹
    let density : Circle → ENNReal := fun z ↦ ENNReal.ofReal (densityReal z)
    let weightedReflected : FiniteMeasure Circle → Measure Circle := fun mu ↦
      ((mu : Measure Circle).withDensity density).map Inv.inv
    let momentMatrix : FiniteMeasure Circle →
        Matrix (Fin (N + 1)) (Fin (N + 1)) Complex := fun mu ↦
      toeplitzMatrix
        (circleMoment (weightedReflected mu)) N
    ((∃ mu : FiniteMeasure Circle,
        momentMatrix mu = momentMatrix source ∧
        (((alpha • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) ≤
          (mu : Measure Circle))) ↔
      (momentMatrix source - (alpha : Complex) •
        momentMatrix normalizedCircleHaar).PosSemidef) := by
  classical
  dsimp only
  let densityReal : Circle → Real := fun z ↦
    (Complex.normSq (denominator.eval (z : Complex)))⁻¹
  let density : Circle → ENNReal := fun z ↦ ENNReal.ofReal (densityReal z)
  have densityContinuous : Continuous densityReal := by
    have evalContinuous : Continuous fun z : Circle ↦
        denominator.eval (z : Complex) :=
      denominator.continuous.comp continuous_subtype_val
    have normSqContinuous : Continuous fun z : Circle ↦
        Complex.normSq (denominator.eval (z : Complex)) := by fun_prop
    exact normSqContinuous.inv₀ fun z h ↦
      denominatorNonzero z (Complex.normSq_eq_zero.mp h)
  have densityFinite (mu : FiniteMeasure Circle) :
      IsFiniteMeasure ((mu : Measure Circle).withDensity density) := by
    dsimp only [density]
    exact isFiniteMeasure_withDensity_ofReal
      (integrableOn_univ.mp
        (densityContinuous.continuousOn.integrableOn_compact
          (μ := (mu : Measure Circle)) isCompact_univ)).hasFiniteIntegral
  let weightedReflected : FiniteMeasure Circle → Measure Circle := fun mu ↦
    ((mu : Measure Circle).withDensity density).map Inv.inv
  let momentMatrix : FiniteMeasure Circle →
      Matrix (Fin (N + 1)) (Fin (N + 1)) Complex := fun mu ↦
    toeplitzMatrix
      (circleMoment (weightedReflected mu)) N
  have weightedReflectedFinite (mu : FiniteMeasure Circle) :
      IsFiniteMeasure (weightedReflected mu) := by
    dsimp only [weightedReflected]
    let _ : IsFiniteMeasure ((mu : Measure Circle).withDensity density) :=
      densityFinite mu
    infer_instance
  let _ : IsFiniteMeasure (weightedReflected source) :=
    weightedReflectedFinite source
  let _ : IsFiniteMeasure (weightedReflected normalizedCircleHaar) :=
    weightedReflectedFinite normalizedCircleHaar
  have monomialIntegrable (mu : Measure Circle) [IsFiniteMeasure mu] (k : Int) :
      Integrable (fun z : Circle ↦ (z : Complex) ^ (-k))
        mu := by
    have continuousMonomial : Continuous fun z : Circle ↦
        (z : Complex) ^ (-k) :=
      continuous_subtype_val.zpow₀ (-k) fun z ↦ Or.inl (Circle.coe_ne_zero z)
    simpa using continuousMonomial.continuousOn.integrableOn_compact
      (μ := mu) isCompact_univ
  have weightedReflected_add (mu nu : FiniteMeasure Circle) :
      weightedReflected (mu + nu) = weightedReflected mu + weightedReflected nu := by
    simp only [weightedReflected, FiniteMeasure.toMeasure_add]
    rw [withDensity_add_measure]
    rw [Measure.map_add _ _ measurable_inv]
  have weightedReflected_smul (c : NNReal) (mu : FiniteMeasure Circle) :
      weightedReflected (c • mu) = c • weightedReflected mu := by
    simp only [weightedReflected, FiniteMeasure.toMeasure_smul]
    change Measure.map Inv.inv
        ((((c : NNReal) : ENNReal) • (mu : Measure Circle)).withDensity density) =
      ((c : NNReal) : ENNReal) •
        Measure.map Inv.inv ((mu : Measure Circle).withDensity density)
    rw [withDensity_smul_measure]
    rw [Measure.map_smul]
  constructor
  · rintro ⟨mu, sameMoment, domination⟩
    let floorMeasure : FiniteMeasure Circle := alpha • normalizedCircleHaar
    let residual : FiniteMeasure Circle :=
      ⟨(mu : Measure Circle) - (floorMeasure : Measure Circle), inferInstance⟩
    have decomposition : floorMeasure + residual = mu := by
      apply FiniteMeasure.toMeasure_injective
      change (floorMeasure : Measure Circle) +
          ((mu : Measure Circle) - (floorMeasure : Measure Circle)) =
        (mu : Measure Circle)
      rw [add_comm, Measure.sub_add_cancel_of_le domination]
    have momentDecomposition :
        momentMatrix mu = (alpha : Complex) •
            momentMatrix normalizedCircleHaar + momentMatrix residual := by
      let _ : IsFiniteMeasure (weightedReflected residual) :=
        weightedReflectedFinite residual
      rw [← decomposition]
      simp only [momentMatrix]
      rw [weightedReflected_add floorMeasure residual, show floorMeasure =
        alpha • normalizedCircleHaar by rfl,
        weightedReflected_smul alpha normalizedCircleHaar]
      ext i j
      simp only [toeplitzMatrix, circleMoment]
      rw [integral_add_measure
        (monomialIntegrable (alpha • weightedReflected normalizedCircleHaar) _)
        (monomialIntegrable (weightedReflected residual) _)]
      rw [integral_smul_nnreal_measure]
      simp [NNReal.smul_def, toeplitzMatrix, circleMoment]
    have sameMomentLocal : momentMatrix mu = momentMatrix source := sameMoment
    have residualIdentity :
        momentMatrix source - (alpha : Complex) •
            momentMatrix normalizedCircleHaar = momentMatrix residual := by
      calc
        momentMatrix source - (alpha : Complex) •
            momentMatrix normalizedCircleHaar =
          momentMatrix mu - (alpha : Complex) •
            momentMatrix normalizedCircleHaar := by rw [sameMomentLocal]
        _ = momentMatrix residual := by rw [momentDecomposition]; abel
    rw [residualIdentity]
    let _ : IsFiniteMeasure (weightedReflected residual) :=
      weightedReflectedFinite residual
    let reflectedFinite : FiniteMeasure Circle :=
      ⟨weightedReflected residual, inferInstance⟩
    let observation : Unit →
        Matrix (Fin (N + 1)) (Fin (N + 1)) Complex →ₗ[Real]
          Matrix (Fin (N + 1)) (Fin (N + 1)) Complex := fun _ ↦
      LinearMap.id
    let admissible : Unit →
        Set (Matrix (Fin (N + 1)) (Fin (N + 1)) Complex) := fun _ ↦
      {momentMatrix residual}
    have measureFeasible : ∃ nu : FiniteMeasure Circle,
        ∀ s, observation s
          (toeplitzMatrix (circleMoment (nu : Measure Circle)) N) ∈
            admissible s := by
      refine ⟨reflectedFinite, ?_⟩
      intro s
      change toeplitzMatrix (circleMoment (weightedReflected residual)) N ∈
        {momentMatrix residual}
      simp only [momentMatrix, Set.mem_singleton_iff]
    have master :=
      (common_spectrum_master_feasibility N Unit
        (Matrix (Fin (N + 1)) (Fin (N + 1)) Complex)
        observation admissible).1.mp measureFeasible
    obtain ⟨y, yPositive, _yHermitian, constraints, _coordinates⟩ := master
    have targetIdentity : toeplitzMatrix y N = momentMatrix residual := by
      have constraint := constraints ()
      simpa only [observation, admissible, LinearMap.id_apply,
        Set.mem_singleton_iff] using constraint
    rwa [← targetIdentity]
  · intro residualPositive
    let r : Int → Complex := fun k ↦
      circleMoment (weightedReflected source) k -
        (alpha : Complex) *
          circleMoment (weightedReflected normalizedCircleHaar) k
    have rHermitian (k : Int) : r (-k) = star (r k) := by
      have momentHermitian (nu : Measure Circle) [IsFiniteMeasure nu] (m : Int) :
          circleMoment nu (-m) = star (circleMoment nu m) := by
        have hHermitian := circle_moment_toeplitz_isHermitian
          nu m.natAbs
        cases m with
        | ofNat n =>
            let j : Fin (n + 1) := ⟨n, by simp⟩
            have h := hHermitian.apply (0 : Fin (n + 1)) j
            simpa [toeplitzMatrix, j, Int.negSucc_eq] using h.symm
        | negSucc n =>
            let j : Fin (n + 2) := ⟨n + 1, by simp⟩
            have h := hHermitian.apply j (0 : Fin (n + 2))
            simpa [toeplitzMatrix, j, Int.negSucc_eq] using h.symm
      dsimp only [r]
      have hs := momentHermitian (weightedReflected source) k
      have hh := momentHermitian (weightedReflected normalizedCircleHaar) k
      calc
        circleMoment (weightedReflected source) (-k) -
            (alpha : Complex) *
              circleMoment (weightedReflected normalizedCircleHaar) (-k) =
          star (circleMoment (weightedReflected source) k) -
            (alpha : Complex) *
              star (circleMoment
                (weightedReflected normalizedCircleHaar) k) := by
                  rw [hs, hh]
        _ = star (circleMoment (weightedReflected source) k -
            (alpha : Complex) *
              circleMoment
                (weightedReflected normalizedCircleHaar) k) := by
                  rw [star_sub, star_mul]
                  simp [mul_comm]
    have residualToeplitz :
        toeplitzMatrix r N =
          momentMatrix source - (alpha : Complex) •
            momentMatrix normalizedCircleHaar := by
      ext i j
      simp [r, momentMatrix, toeplitzMatrix]
    have rPositive : (toeplitzMatrix r N).PosSemidef := by
      rwa [residualToeplitz]
    obtain ⟨sigma, sigmaMoments⟩ :=
      truncated_circle_moment_of_posSemidef N r rHermitian rPositive
    let tau : FiniteMeasure Circle := sigma.map Inv.inv
    let qReal : Circle → Real := fun z ↦
      Complex.normSq (denominator.eval (z : Complex))
    let q : Circle → ENNReal := fun z ↦ ENNReal.ofReal (qReal z)
    have qContinuous : Continuous qReal := by
      dsimp only [qReal]
      fun_prop
    have qIntegrable : Integrable qReal (tau : Measure Circle) :=
      integrableOn_univ.mp
        (qContinuous.continuousOn.integrableOn_compact
          (μ := (tau : Measure Circle)) isCompact_univ)
    let rhoMeasure : Measure Circle := (tau : Measure Circle).withDensity q
    let rhoFinite : IsFiniteMeasure rhoMeasure := by
      dsimp only [rhoMeasure, q]
      exact isFiniteMeasure_withDensity_ofReal qIntegrable.hasFiniteIntegral
    let rho : FiniteMeasure Circle := ⟨rhoMeasure, rhoFinite⟩
    have qMeasurable : Measurable q := qContinuous.measurable.ennreal_ofReal
    have q_ne_zero : ∀ z, q z ≠ 0 := by
      intro z
      rw [ENNReal.ofReal_ne_zero_iff]
      exact Complex.normSq_pos.mpr (denominatorNonzero z)
    have q_ne_top : ∀ z, q z ≠ ∞ := fun _ ↦ ENNReal.ofReal_ne_top
    have density_eq_inv : density = fun z ↦ (q z)⁻¹ := by
      funext z
      dsimp only [density, densityReal, q, qReal]
      exact ENNReal.ofReal_inv_of_pos
        (Complex.normSq_pos.mpr (denominatorNonzero z))
    have reweightedRho :
        (rho : Measure Circle).withDensity density = (tau : Measure Circle) := by
      change rhoMeasure.withDensity density = (tau : Measure Circle)
      rw [density_eq_inv]
      exact withDensity_inv_same qMeasurable
        (Filter.Eventually.of_forall q_ne_zero)
        (Filter.Eventually.of_forall q_ne_top)
    have reflectedRho : weightedReflected rho = sigma := by
      simp only [weightedReflected]
      rw [reweightedRho]
      dsimp only [tau]
      rw [FiniteMeasure.toMeasure_map]
      rw [Measure.map_map measurable_inv measurable_inv]
      simp
    have residualMoment : momentMatrix rho =
        momentMatrix source - (alpha : Complex) •
          momentMatrix normalizedCircleHaar := by
      rw [residualToeplitz.symm]
      ext i j
      simp only [momentMatrix, reflectedRho, toeplitzMatrix, circleMoment]
      exact sigmaMoments _ (by
        have hi := i.isLt
        have hj := j.isLt
        simp only [Nat.lt_add_one_iff] at hi hj
        omega)
    let mu : FiniteMeasure Circle := alpha • normalizedCircleHaar + rho
    refine ⟨mu, ?_, ?_⟩
    · change momentMatrix (alpha • normalizedCircleHaar + rho) =
        momentMatrix source
      simp only [momentMatrix]
      rw [weightedReflected_add (alpha • normalizedCircleHaar) rho,
        weightedReflected_smul alpha normalizedCircleHaar]
      let _ : IsFiniteMeasure (weightedReflected rho) :=
        weightedReflectedFinite rho
      ext i j
      simp only [toeplitzMatrix, circleMoment]
      rw [integral_add_measure
        (monomialIntegrable (alpha • weightedReflected normalizedCircleHaar) _)
        (monomialIntegrable (weightedReflected rho) _)]
      rw [integral_smul_nnreal_measure]
      have pointIdentity := congrArg (fun M ↦ M i j) residualMoment
      have pointIntegral :
          (∫ z : Circle, (z : Complex) ^
              (-(((i : Nat) : Int) - ((j : Nat) : Int)))
              ∂weightedReflected rho) =
            (∫ z : Circle, (z : Complex) ^
                (-(((i : Nat) : Int) - ((j : Nat) : Int)))
                ∂weightedReflected source) -
              (alpha : Complex) *
                ∫ z : Circle, (z : Complex) ^
                  (-(((i : Nat) : Int) - ((j : Nat) : Int)))
                  ∂weightedReflected normalizedCircleHaar := by
        simpa [momentMatrix, toeplitzMatrix, circleMoment, NNReal.smul_def]
          using pointIdentity
      rw [pointIntegral]
      simp [NNReal.smul_def]
    · dsimp only [mu]
      rw [FiniteMeasure.toMeasure_add]
      exact Measure.le_add_right (le_refl _)

private theorem inverse_congruence_cancel
    {N : Nat}
    (A M : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex)
    (hA : IsUnit A) :
    A⁻¹ * (A * M * Aᴴ) * (A⁻¹)ᴴ = M := by
  let _ := hA.invertible
  rw [Matrix.conjTranspose_nonsing_inv]
  have hAstar : IsUnit Aᴴ := hA.star
  let _ := hAstar.invertible
  simp [Matrix.mul_assoc]

private theorem whitening_residual_iff
    {N : Nat}
    (H T : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex)
    (hH : H.PosDef) (alpha : Real) :
    let S := CFC.sqrt H
    let W := S⁻¹
    let Q := W * T * W
    (Q - (alpha : Complex) • 1).PosSemidef ↔
      (T - (alpha : Complex) • H).PosSemidef := by
  dsimp only
  let S : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex := CFC.sqrt H
  have hH_nonneg : 0 ≤ H := hH.posSemidef.nonneg
  have hS_nonneg : 0 ≤ S := CFC.sqrt_nonneg H
  have hS_unit : IsUnit S :=
    (CFC.isUnit_sqrt_iff H (ha := hH_nonneg)).mpr hH.isUnit
  let _ := hS_unit.invertible
  have hS_sq : S * S = H := CFC.sqrt_mul_sqrt_self H (ha := hH_nonneg)
  have hS_star : star S = S := hS_nonneg.isSelfAdjoint.star_eq
  have hWinv_star : star S⁻¹ = S⁻¹ := by
    rw [star_eq_conjTranspose, Matrix.conjTranspose_nonsing_inv]
    simpa only [← star_eq_conjTranspose] using congrArg Inv.inv hS_star
  have hconj :=
    (Matrix.isUnit_nonsing_inv_iff.mpr hS_unit).posSemidef_star_right_conjugate_iff
      (x := T - (alpha : Complex) • H)
  have hcongruence :
      S⁻¹ * (T - (alpha : Complex) • H) * star S⁻¹ =
        S⁻¹ * T * S⁻¹ - (alpha : Complex) • 1 := by
    rw [hWinv_star, Matrix.mul_sub, Matrix.sub_mul]
    rw [← hS_sq]
    simp [Matrix.mul_assoc]
  rw [hcongruence] at hconj
  simpa only [S] using hconj

private theorem generalized_floor_isGreatest
    {N : Nat}
    (H T : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex)
    (hH : H.PosDef) (hT : T.IsHermitian) :
    let W := (CFC.sqrt H)⁻¹
    let Q := Wᴴ * T * W
    let hQ : Q.IsHermitian :=
      Matrix.isHermitian_conjTranspose_mul_mul W hT
    let lambda := hQ.eigenvalues₀ ⟨N, by simp⟩
    IsGreatest {alpha : Real | (T - (alpha : Complex) • H).PosSemidef} lambda := by
  classical
  dsimp only
  let W : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex :=
    (CFC.sqrt H)⁻¹
  have hH_nonneg : 0 ≤ H := hH.posSemidef.nonneg
  have hS_nonneg : 0 ≤ CFC.sqrt H := CFC.sqrt_nonneg H
  have hS_star : star (CFC.sqrt H) = CFC.sqrt H :=
    hS_nonneg.isSelfAdjoint.star_eq
  have hW_star : star W = W := by
    dsimp only [W]
    rw [star_eq_conjTranspose, Matrix.conjTranspose_nonsing_inv]
    simpa only [← star_eq_conjTranspose] using congrArg Inv.inv hS_star
  let Q : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex := Wᴴ * T * W
  have hQ : Q.IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_mul W hT
  let lambda : Real := hQ.eigenvalues₀ ⟨N, by simp⟩
  have smallestResidual :
      (Q - (lambda : Complex) • 1).PosSemidef := by
    let diagonalization :=
      Unitary.conjStarAlgAut Complex
        (Matrix (Fin (N + 1)) (Fin (N + 1)) Complex)
        hQ.eigenvectorUnitary
    have lambdaLeEigenvalue (i : Fin (N + 1)) :
        lambda ≤ hQ.eigenvalues i := by
      apply hQ.eigenvalues₀_antitone
      apply Fin.le_iff_val_le_val.mpr
      have hi := ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i).isLt
      simp only [Fintype.card_fin] at hi
      dsimp only [lambda]
      omega
    change Matrix.PosSemidef (Q - (lambda : Complex) • 1)
    rw [hQ.spectral_theorem]
    have scalarFixed :
        (lambda : Complex) •
            (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex) =
          diagonalization
            ((lambda : Complex) •
              (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex)) := by
      simp [diagonalization]
    rw [scalarFixed, ← map_sub]
    rw [Unitary.conjStarAlgAut_apply]
    apply Unitary.isUnit_coe.posSemidef_star_right_conjugate_iff.mpr
    have diagonalDifference :
        Matrix.diagonal (RCLike.ofReal ∘ hQ.eigenvalues) -
            (lambda : Complex) • 1 =
          Matrix.diagonal
            (fun i ↦ ((hQ.eigenvalues i - lambda : Real) : Complex)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    rw [diagonalDifference]
    apply Matrix.PosSemidef.diagonal
    intro i
    exact Complex.zero_le_real.mpr
      (sub_nonneg.mpr (lambdaLeEigenvalue i))
  have upperBound (alpha : Real)
      (residualPositive : (Q - (alpha : Complex) • 1).PosSemidef) :
      alpha ≤ lambda := by
    let symmetricOperator : Q.toEuclideanLin.IsSymmetric :=
      Matrix.isSymmetric_toEuclideanLin_iff.mpr hQ
    let lastIndex : Fin (Fintype.card (Fin (N + 1))) := ⟨N, by simp⟩
    let x : EuclideanSpace Complex (Fin (N + 1)) :=
      symmetricOperator.eigenvectorBasis finrank_euclideanSpace lastIndex
    have xNorm : ‖x‖ = 1 :=
      (symmetricOperator.eigenvectorBasis finrank_euclideanSpace).orthonormal.1
        lastIndex
    have xUnit : star x ⬝ᵥ x = 1 := by
      rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
      rw [inner_self_eq_norm_sq_to_K, xNorm]
      norm_num
    have operatorAtXEuclidean : Q.toEuclideanLin x =
        (hQ.eigenvalues₀ lastIndex : Complex) • x := by
      simp [Matrix.IsHermitian.eigenvalues₀, x]
    have operatorAtX : Q *ᵥ x =
        (hQ.eigenvalues₀ lastIndex : Complex) •
          (x : Fin (N + 1) → Complex) := by
      have hx := congrArg WithLp.ofLp operatorAtXEuclidean
      exact hx
    have residualAtX : (Q - (alpha : Complex) • 1) *ᵥ x =
        ((hQ.eigenvalues₀ lastIndex - alpha : Real) : Complex) • x := by
      rw [Matrix.sub_mulVec, operatorAtX, Matrix.smul_mulVec,
        Matrix.one_mulVec]
      ext i
      simp [sub_smul]
    have quadraticNonnegative := residualPositive.re_dotProduct_nonneg x
    rw [residualAtX] at quadraticNonnegative
    change 0 ≤ RCLike.re
      (star (x : Fin (N + 1) → Complex) ⬝ᵥ
        (((hQ.eigenvalues₀ lastIndex - alpha : Real) : Complex) •
          (x : Fin (N + 1) → Complex))) at quadraticNonnegative
    rw [dotProduct_smul, xUnit] at quadraticNonnegative
    simpa [lambda, lastIndex] using quadraticNonnegative
  constructor
  · apply (whitening_residual_iff H T hH lambda).mp
    simpa only [Q, ← star_eq_conjTranspose, hW_star] using smallestResidual
  · intro alpha residualPositive
    apply upperBound alpha
    have whitened :=
      (whitening_residual_iff H T hH alpha).mpr residualPositive
    simpa only [Q, ← star_eq_conjTranspose, hW_star] using whitened

theorem exact_common_spectrum_floor
    (N : Nat)
    (coefficient : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex)
    (coefficientUnit : IsUnit coefficient)
    (denominator : Polynomial Complex)
    (denominatorNonzero : forall z : Circle,
      denominator.eval (z : Complex) ≠ 0)
    (G : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex)
    (hG : G.IsHermitian)
    (source : FiniteMeasure Circle)
    (sourceGram :
      (fun i j : Fin (N + 1) ↦
        ∫ z : Circle,
          ((coefficient *ᵥ (fun k : Fin (N + 1) ↦
              (z : Complex) ^ (k : Nat))) i /
            denominator.eval (z : Complex)) *
          star ((coefficient *ᵥ (fun k : Fin (N + 1) ↦
              (z : Complex) ^ (k : Nat))) j /
            denominator.eval (z : Complex)) ∂( source : Measure Circle)) = G) :
    let monomial : Circle → Fin (N + 1) → Complex := fun z j ↦
      (z : Complex) ^ (j : Nat)
    let feature : Circle → Fin (N + 1) → Complex := fun z i ↦
      (coefficient *ᵥ monomial z) i / denominator.eval (z : Complex)
    let rationalGram : FiniteMeasure Circle →
        Matrix (Fin (N + 1)) (Fin (N + 1)) Complex := fun mu i j ↦
      ∫ z, feature z i * star (feature z j) ∂( mu : Measure Circle)
    let densityReal : Circle → Real := fun z ↦
      (Complex.normSq (denominator.eval (z : Complex)))⁻¹
    let density : Circle → ENNReal := fun z ↦ ENNReal.ofReal (densityReal z)
    let weightedReflected : FiniteMeasure Circle → Measure Circle := fun mu ↦
      ((mu : Measure Circle).withDensity density).map Inv.inv
    let momentMatrix : FiniteMeasure Circle →
        Matrix (Fin (N + 1)) (Fin (N + 1)) Complex := fun mu ↦
      toeplitzMatrix (circleMoment (weightedReflected mu)) N
    let H_D := momentMatrix normalizedCircleHaar
    let B := coefficient * H_D * coefficientᴴ
    let T := coefficient⁻¹ * G * (coefficient⁻¹)ᴴ
    let feasibleFloors : Set NNReal :=
      {alpha | ∃ mu : FiniteMeasure Circle,
        rationalGram mu = G ∧
        (((alpha • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) ≤
          (mu : Measure Circle))}
    let alphaStar : NNReal := sSup feasibleFloors
    H_D.PosDef →
      let hT : T.IsHermitian := by
        simpa only [Matrix.conjTranspose_conjTranspose] using
          Matrix.isHermitian_conjTranspose_mul_mul (coefficient⁻¹)ᴴ hG
      let W_D := (CFC.sqrt H_D)⁻¹
      let Q_D := W_Dᴴ * T * W_D
      let hQ_D : Q_D.IsHermitian :=
        Matrix.isHermitian_conjTranspose_mul_mul W_D hT
      let W_B := (CFC.sqrt B)⁻¹
      let Q_B := W_Bᴴ * G * W_B
      let hQ_B : Q_B.IsHermitian :=
        Matrix.isHermitian_conjTranspose_mul_mul W_B hG
      IsGreatest
          {alpha : Real | (T - (alpha : Complex) • H_D).PosSemidef}
          (alphaStar : Real) ∧
        (alphaStar : Real) = hQ_D.eigenvalues₀ ⟨N, by simp⟩ ∧
        (alphaStar : Real) = hQ_B.eigenvalues₀ ⟨N, by simp⟩ := by
  classical
  dsimp only
  intro hH
  let monomial : Circle → Fin (N + 1) → Complex := fun z j ↦
    (z : Complex) ^ (j : Nat)
  let feature : Circle → Fin (N + 1) → Complex := fun z i ↦
    (coefficient *ᵥ monomial z) i / denominator.eval (z : Complex)
  let rationalGram : FiniteMeasure Circle →
      Matrix (Fin (N + 1)) (Fin (N + 1)) Complex := fun mu i j ↦
    ∫ z, feature z i * star (feature z j) ∂( mu : Measure Circle)
  let densityReal : Circle → Real := fun z ↦
    (Complex.normSq (denominator.eval (z : Complex)))⁻¹
  let density : Circle → ENNReal := fun z ↦ ENNReal.ofReal (densityReal z)
  let weightedReflected : FiniteMeasure Circle → Measure Circle := fun mu ↦
    ((mu : Measure Circle).withDensity density).map Inv.inv
  let momentMatrix : FiniteMeasure Circle →
      Matrix (Fin (N + 1)) (Fin (N + 1)) Complex := fun mu ↦
    toeplitzMatrix (circleMoment (weightedReflected mu)) N
  let H_D : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex :=
    momentMatrix normalizedCircleHaar
  let B : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex :=
    coefficient * H_D * coefficientᴴ
  let T : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex :=
    coefficient⁻¹ * G * (coefficient⁻¹)ᴴ
  let feasibleFloors : Set NNReal :=
    {alpha | ∃ mu : FiniteMeasure Circle,
      rationalGram mu = G ∧
      (((alpha • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) ≤
        (mu : Measure Circle))}
  let alphaStar : NNReal := sSup feasibleFloors
  have sourceGramLocal : rationalGram source = G := by
    change rationalGram source = G at sourceGram
    exact sourceGram
  have gramCongruence (mu : FiniteMeasure Circle) :
      rationalGram mu = coefficient * momentMatrix mu * coefficientᴴ := by
    simpa only [rationalGram, feature, monomial, momentMatrix,
      weightedReflected, density, densityReal] using
      rational_gram_eq_weighted_reflected_congruence N mu coefficient
        denominator denominatorNonzero
  have G_congruence : G = coefficient * momentMatrix source * coefficientᴴ :=
    sourceGramLocal.symm.trans (gramCongruence source)
  have T_eq_moment : T = momentMatrix source := by
    dsimp only [T]
    rw [G_congruence]
    exact inverse_congruence_cancel coefficient (momentMatrix source) coefficientUnit
  have gram_eq_iff_moment_eq (mu : FiniteMeasure Circle) :
      rationalGram mu = G ↔ momentMatrix mu = momentMatrix source := by
    constructor
    · intro hmu
      have congruent :
          coefficient * momentMatrix mu * coefficientᴴ =
            coefficient * momentMatrix source * coefficientᴴ := by
        rw [← gramCongruence mu, ← G_congruence]
        exact hmu
      have cancelled := congrArg
        (fun M ↦ coefficient⁻¹ * M * (coefficient⁻¹)ᴴ) congruent
      simpa only [inverse_congruence_cancel coefficient _ coefficientUnit]
        using cancelled
    · intro hmoment
      rw [gramCongruence, hmoment, ← G_congruence]
  have floorResidual (alpha : NNReal) :
      alpha ∈ feasibleFloors ↔
        (T - (alpha : Complex) • H_D).PosSemidef := by
    have weightedEquivalence := weighted_floor_iff_residual N denominator
      denominatorNonzero source alpha
    dsimp only at weightedEquivalence
    rw [T_eq_moment]
    change (∃ mu : FiniteMeasure Circle,
        rationalGram mu = G ∧
          (((alpha • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) ≤
            (mu : Measure Circle))) ↔ _
    constructor
    · rintro ⟨mu, gram, domination⟩
      exact weightedEquivalence.mp
        ⟨mu, (gram_eq_iff_moment_eq mu).mp gram, domination⟩
    · rintro positive
      obtain ⟨mu, sameMoment, domination⟩ := weightedEquivalence.mpr positive
      exact ⟨mu, (gram_eq_iff_moment_eq mu).mpr sameMoment, domination⟩
  have zeroFeasible : (0 : NNReal) ∈ feasibleFloors := by
    refine ⟨source, sourceGramLocal, ?_⟩
    simpa only [zero_smul, FiniteMeasure.toMeasure_zero] using
      Measure.zero_le (source : Measure Circle)
  have zeroResidual : T.PosSemidef := by
    have := (floorResidual 0).mp zeroFeasible
    simpa using this
  have hT : T.IsHermitian := zeroResidual.isHermitian
  have hB : B.PosDef := by
    dsimp only [B]
    exact hH.mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_of_isUnit coefficientUnit)
  let W_D : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex :=
    (CFC.sqrt H_D)⁻¹
  let Q_D : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex := W_Dᴴ * T * W_D
  have hQ_D : Q_D.IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_mul W_D hT
  let lambdaD : Real := hQ_D.eigenvalues₀ ⟨N, by simp⟩
  have greatestT :
      IsGreatest {alpha : Real |
        (T - (alpha : Complex) • H_D).PosSemidef} lambdaD := by
    simpa only [W_D, Q_D, hQ_D, lambdaD] using
      generalized_floor_isGreatest H_D T hH hT
  have lambdaNonnegative : 0 ≤ lambdaD :=
    greatestT.2 (by simpa using zeroResidual)
  let lambdaNN : NNReal := ⟨lambdaD, lambdaNonnegative⟩
  have greatestFeasible : IsGreatest feasibleFloors lambdaNN := by
    constructor
    · apply (floorResidual lambdaNN).mpr
      change (T - (lambdaD : Complex) • H_D).PosSemidef
      exact greatestT.1
    · intro alpha alphaFeasible
      have bound := greatestT.2 ((floorResidual alpha).mp alphaFeasible)
      exact_mod_cast bound
  have alphaNN_eq : alphaStar = lambdaNN := by
    exact greatestFeasible.csSup_eq
  have alpha_eq_lambdaD : (alphaStar : Real) = lambdaD := by
    rw [alphaNN_eq]
    rfl
  have greatestAtAlpha :
      IsGreatest {alpha : Real |
        (T - (alpha : Complex) • H_D).PosSemidef} (alphaStar : Real) := by
    rw [alpha_eq_lambdaD]
    exact greatestT
  have G_from_T : G = coefficient * T * coefficientᴴ := by
    rw [T_eq_moment]
    exact G_congruence
  have residualCongruence (alpha : Real) :
      G - (alpha : Complex) • B =
        coefficient * (T - (alpha : Complex) • H_D) * coefficientᴴ := by
    rw [G_from_T]
    dsimp only [B]
    rw [Matrix.mul_sub, Matrix.sub_mul]
    simp
  have residual_iff (alpha : Real) :
      (G - (alpha : Complex) • B).PosSemidef ↔
        (T - (alpha : Complex) • H_D).PosSemidef := by
    rw [residualCongruence]
    simpa only [star_eq_conjTranspose] using
      coefficientUnit.posSemidef_star_right_conjugate_iff
        (x := T - (alpha : Complex) • H_D)
  have greatestG :
      IsGreatest {alpha : Real |
        (G - (alpha : Complex) • B).PosSemidef} lambdaD := by
    constructor
    · exact (residual_iff lambdaD).mpr greatestT.1
    · intro alpha positive
      exact greatestT.2 ((residual_iff alpha).mp positive)
  let W_B : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex :=
    (CFC.sqrt B)⁻¹
  let Q_B : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex := W_Bᴴ * G * W_B
  have hQ_B : Q_B.IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_mul W_B hG
  let lambdaB : Real := hQ_B.eigenvalues₀ ⟨N, by simp⟩
  have greatestB :
      IsGreatest {alpha : Real |
        (G - (alpha : Complex) • B).PosSemidef} lambdaB := by
    simpa only [W_B, Q_B, hQ_B, lambdaB] using
      generalized_floor_isGreatest B G hB hG
  have lambdaD_eq_lambdaB : lambdaD = lambdaB :=
    greatestG.unique greatestB
  refine ⟨greatestAtAlpha, alpha_eq_lambdaD, ?_⟩
  exact alpha_eq_lambdaD.trans lambdaD_eq_lambdaB

end D5.S3.Observer.BlockStructure.ExactCommonSpectrumFloor
