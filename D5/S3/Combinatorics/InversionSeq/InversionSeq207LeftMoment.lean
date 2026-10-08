/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207LeftMoment
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207LeftMoment
   mirror-E: none(waiver:formal-left-lambert-moment)
   anchors: []
   utility: none
   digest: Reflected kernel elimination identifies the left scalar with its Lambert moment. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftRational

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftMoment

open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology
open InversionSeq207LeftNormalization InversionSeq207LeftDiagonal
open InversionSeq207LeftGauge InversionSeq207Catalytic

set_option maxHeartbeats 6400000 in
theorem left_moment_regularity :
    (letI : UniformSpace (LaurentPolynomial ℚ) := ⊥
     letI : DiscreteUniformity (LaurentPolynomial ℚ) := ⟨rfl⟩
     let alternating := PowerSeries.map LaurentPolynomial.C
       (PowerSeries.mk fun degree => (-1 : ℚ) ^ degree)
     let parameter := PowerSeries.X * alternating ^ 2
     let residual := 1 - parameter * PowerSeries.eval₂
       (RingHom.id (PowerSeries (LaurentPolynomial ℚ))) parameter (forwardSeries true 1 1)
     PowerSeries.map (LaurentPolynomial.eval₂ (RingHom.id ℚ) 1) leftKernelBoundary =
       PowerSeries.map (LaurentPolynomial.eval₂ (RingHom.id ℚ) 1) residual *
         leftScalarMoment) := by
  classical
  let denominator : PowerSeries (LaurentPolynomial ℚ) :=
    1 + PowerSeries.X * PowerSeries.C (LaurentPolynomial.T (-1) - 2) +
      PowerSeries.X ^ 2 * PowerSeries.C (LaurentPolynomial.T 1 - 2) + PowerSeries.X ^ 3
  let numerator : PowerSeries (LaurentPolynomial ℚ) :=
    (PowerSeries.X - 1) ^ 3 * (PowerSeries.X + 1) ^ 3 *
      PowerSeries.C ((LaurentPolynomial.T 1 - 1) ^ 2) *
      (PowerSeries.X * PowerSeries.C (LaurentPolynomial.T 1) - 1) ^ 2 *
      (PowerSeries.X * PowerSeries.C (LaurentPolynomial.T 2) - 1) *
      PowerSeries.C (LaurentPolynomial.T (-3))
  have hrational := left_rational_regularity.1
  have hLambertSum := left_rational_regularity.2.2.1
  have hScalarShift := left_rational_regularity.2.2.2
  letI : UniformSpace (LaurentPolynomial ℚ) := ⊥
  letI : DiscreteUniformity (LaurentPolynomial ℚ) := ⟨rfl⟩
  let column (series : PowerSeries (LaurentPolynomial ℚ)) (index : ℤ) :
      LaurentSeries ℚ :=
    (PowerSeries.mk fun degree => (PowerSeries.coeff degree series).coeff index :
      PowerSeries ℚ)
  let shift : Multiplicative ℤ →* Module.End (LaurentSeries ℚ) (ℤ → LaurentSeries ℚ) :=
    { toFun := fun exponent =>
        { toFun := fun sequence index => sequence (index - exponent.toAdd)
          map_add' := by intros; rfl
          map_smul' := by intros; rfl }
      map_one' := by ext sequence index; simp
      map_mul' := by
        intro first second
        apply LinearMap.ext
        intro sequence
        funext index
        change sequence (index - (first.toAdd + second.toAdd)) =
          sequence (index - first.toAdd - second.toAdd)
        congr 1
        omega }
  let act : LaurentPolynomial (LaurentSeries ℚ) →+*
      Module.End (LaurentSeries ℚ) (ℤ → LaurentSeries ℚ) :=
    AddMonoidAlgebra.liftNCRingHom (algebraMap _ _) shift
      (fun value exponent => Algebra.commute_algebraMap_left value (shift exponent))
  have hactMonomial (value : LaurentSeries ℚ) (exponent : ℤ)
      (sequence : ℤ → LaurentSeries ℚ) (index : ℤ) :
      act (LaurentPolynomial.C value * LaurentPolynomial.T exponent) sequence index =
        value * sequence (index - exponent) := by
    dsimp only [act]
    rw [← LaurentPolynomial.single_eq_C_mul_T,
      AddMonoidAlgebra.liftNCRingHom_single]
    rfl
  have hactC (value : LaurentSeries ℚ) (sequence : ℤ → LaurentSeries ℚ) (index : ℤ) :
      act (LaurentPolynomial.C value) sequence index = value * sequence index := by
    simpa using hactMonomial value 0 sequence index
  let expandMonomial : Multiplicative ℤ →* PowerSeries (LaurentPolynomial ℚ) :=
    { toFun := fun exponent => PowerSeries.C (LaurentPolynomial.T exponent.toAdd)
      map_one' := by simp
      map_mul' := by
        intro first second
        change PowerSeries.C (LaurentPolynomial.T (first.toAdd + second.toAdd)) = _
        rw [LaurentPolynomial.T_add, map_mul] }
  let expand : LaurentPolynomial (PowerSeries ℚ) →+*
      PowerSeries (LaurentPolynomial ℚ) :=
    AddMonoidAlgebra.liftNCRingHom (PowerSeries.map LaurentPolynomial.C)
      expandMonomial (fun _ _ => Commute.all _ _)
  have hexpandMonomial (value : PowerSeries ℚ) (exponent : ℤ) :
      expand (LaurentPolynomial.C value * LaurentPolynomial.T exponent) =
        PowerSeries.map LaurentPolynomial.C value *
          PowerSeries.C (LaurentPolynomial.T exponent) := by
    rw [← LaurentPolynomial.single_eq_C_mul_T]
    exact AddMonoidAlgebra.liftNCRingHom_single _ _ _ _ _
  have hexpandC (value : PowerSeries ℚ) :
      expand (LaurentPolynomial.C value) = PowerSeries.map LaurentPolynomial.C value :=
    by simpa using hexpandMonomial value 0
  have hexpandT (exponent : ℤ) :
      expand (LaurentPolynomial.T exponent) =
        PowerSeries.C (LaurentPolynomial.T exponent) := by
    simpa using hexpandMonomial 1 exponent
  let promote : LaurentPolynomial (PowerSeries ℚ) →+* LaurentPolynomial (LaurentSeries ℚ) :=
    AddMonoidAlgebra.mapRingHom ℤ (HahnSeries.ofPowerSeries ℤ ℚ)
  have hpromoteC (value : PowerSeries ℚ) :
      promote (LaurentPolynomial.C value) = LaurentPolynomial.C (value : LaurentSeries ℚ) :=
    by exact AddMonoidAlgebra.mapRingHom_single _ 0 value
  have hpromoteT (exponent : ℤ) :
      promote (LaurentPolynomial.T exponent) = LaurentPolynomial.T exponent := by
    exact (AddMonoidAlgebra.mapRingHom_single _ exponent 1).trans (by rw [map_one]; rfl)
  have hcolumnAdd (first second : PowerSeries (LaurentPolynomial ℚ)) :
      column (first + second) = column first + column second := by
    funext index
    dsimp only [column]
    simp only [Pi.add_apply]
    rw [← map_add]
    congr 1
  have hproduct (polynomial : LaurentPolynomial (PowerSeries ℚ))
      (series : PowerSeries (LaurentPolynomial ℚ)) :
      column (expand polynomial * series) = act (promote polynomial) (column series) := by
    induction polynomial using LaurentPolynomial.induction_on' with
    | add first second hfirst hsecond =>
        simp only [map_add, add_mul, hcolumnAdd, hfirst, hsecond, LinearMap.add_apply]
    | C_mul_T location value =>
        rw [hexpandMonomial, map_mul, hpromoteC, hpromoteT]
        funext index
        rw [hactMonomial]
        rw [← PowerSeries.coe_mul]
        dsimp only [column]
        congr 1
        ext degree
        rw [show PowerSeries.map LaurentPolynomial.C value *
          PowerSeries.C (LaurentPolynomial.T location) * series =
            PowerSeries.map LaurentPolynomial.C value *
              (PowerSeries.C (LaurentPolynomial.T location) * series) by ring]
        rw [PowerSeries.coeff_mk]
        conv_lhs =>
          rw [PowerSeries.coeff_mul]
          simp only [PowerSeries.coeff_map, PowerSeries.coeff_C_mul,
            AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
        conv_rhs =>
          rw [PowerSeries.coeff_mul]
          simp only [PowerSeries.coeff_mk]
        apply Finset.sum_congr rfl
        intro pair _
        change (AddMonoidAlgebra.single 0 (PowerSeries.coeff pair.1 value) *
          (AddMonoidAlgebra.single location 1 * PowerSeries.coeff pair.2 series)).coeff
            index = _
        rw [AddMonoidAlgebra.coeff_single_zero_mul]
        rw [AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
        simp only [sub_eq_add_neg, add_comm]
  let q : PowerSeries ℚ := PowerSeries.X
  let t : LaurentPolynomial (PowerSeries ℚ) := LaurentPolynomial.T 1
  let inverseT : LaurentPolynomial (PowerSeries ℚ) := LaurentPolynomial.T (-1)
  let laurentDenominator : LaurentPolynomial (PowerSeries ℚ) :=
    1 + LaurentPolynomial.C q * (inverseT - 2) +
      LaurentPolynomial.C (q ^ 2) * (t - 2) + LaurentPolynomial.C (q ^ 3)
  let first : LaurentPolynomial (PowerSeries ℚ) :=
    (LaurentPolynomial.C q - 1) ^ 2 * (LaurentPolynomial.C (q ^ 2) * t - 1)
  let second : LaurentPolynomial (PowerSeries ℚ) :=
    (LaurentPolynomial.C q - t) * laurentDenominator
  let forcing : LaurentPolynomial (PowerSeries ℚ) :=
    (LaurentPolynomial.C (q ^ 2) - 1) ^ 2 * (t - 1)
  let alternating := PowerSeries.map LaurentPolynomial.C
    (PowerSeries.mk fun degree => (-1 : ℚ) ^ degree)
  let parameter := PowerSeries.X * alternating ^ 2
  let residual := 1 - parameter * PowerSeries.eval₂
    (RingHom.id (PowerSeries (LaurentPolynomial ℚ))) parameter (forwardSeries true 1 1)
  have hkernel :
      act (promote first) (column leftDiagonalBoundary) =
        act (promote second) (column leftKernelBoundary) +
          act (promote forcing) (column residual) := by
    have hequation := left_diagonal_reflection.2.2.2
    have hexpansion : expand first * leftDiagonalBoundary =
        expand second * leftKernelBoundary + expand forcing * residual := by
      simpa only [first, second, forcing, laurentDenominator, q, t, inverseT,
        map_mul, map_pow, map_sub, map_add, map_one, map_ofNat, hexpandC, hexpandT,
        PowerSeries.map_X, map_one] using hequation
    exact (hproduct first leftDiagonalBoundary).symm.trans
      ((congrArg column hexpansion).trans
        (by rw [hcolumnAdd, hproduct, hproduct]))
  let monomial (index : ℤ) : LaurentSeries ℚ := HahnSeries.single index 1
  have hmonomialMul (first second : ℤ) :
      monomial first * monomial second = monomial (first + second) := by
    simp [monomial, HahnSeries.single_mul_single]
  have hmonomialZero : monomial 0 = 1 := by simp [monomial, ← HahnSeries.C_apply]
  let reflectSequence (sequence : ℤ → LaurentSeries ℚ) (index : ℤ) :=
    monomial index * sequence (-index)
  let reflectMonomial : Multiplicative ℤ →* LaurentPolynomial (LaurentSeries ℚ) :=
    { toFun := fun exponent =>
        LaurentPolynomial.C (monomial (-exponent.toAdd)) *
          LaurentPolynomial.T (-exponent.toAdd)
      map_one' := by simp [hmonomialZero]
      map_mul' := by
        intro first second
        change LaurentPolynomial.C (monomial (-(first.toAdd + second.toAdd))) *
          LaurentPolynomial.T (-(first.toAdd + second.toAdd)) = _
        rw [neg_add, ← hmonomialMul, LaurentPolynomial.T_add, map_mul]
        ring }
  let reflect : LaurentPolynomial (LaurentSeries ℚ) →+*
      LaurentPolynomial (LaurentSeries ℚ) :=
    AddMonoidAlgebra.liftNCRingHom LaurentPolynomial.C reflectMonomial
      (fun _ _ => Commute.all _ _)
  have hreflectMonomial (value : LaurentSeries ℚ) (exponent : ℤ) :
      reflect (LaurentPolynomial.C value * LaurentPolynomial.T exponent) =
        LaurentPolynomial.C (value * monomial (-exponent)) *
          LaurentPolynomial.T (-exponent) := by
    rw [← LaurentPolynomial.single_eq_C_mul_T]
    dsimp only [reflect]
    rw [AddMonoidAlgebra.liftNCRingHom_single]
    change LaurentPolynomial.C value *
      (LaurentPolynomial.C (monomial (-exponent)) * LaurentPolynomial.T (-exponent)) = _
    rw [← mul_assoc, ← map_mul]
  have hreflectC (value : LaurentSeries ℚ) :
      reflect (LaurentPolynomial.C value) = LaurentPolynomial.C value := by
    simpa [hmonomialZero] using hreflectMonomial value 0
  have hreflectT (exponent : ℤ) :
      reflect (LaurentPolynomial.T exponent) =
        LaurentPolynomial.C (monomial (-exponent)) * LaurentPolynomial.T (-exponent) :=
    by simpa using hreflectMonomial 1 exponent
  have hreflectAction (polynomial : LaurentPolynomial (LaurentSeries ℚ))
      (sequence : ℤ → LaurentSeries ℚ) :
      reflectSequence (act polynomial sequence) =
        act (reflect polynomial) (reflectSequence sequence) := by
    induction polynomial using LaurentPolynomial.induction_on' with
    | add first second hfirst hsecond =>
        funext index
        simpa only [map_add, LinearMap.add_apply, Pi.add_apply, reflectSequence, mul_add]
          using congrFun (congrArg₂ (fun first second => first + second) hfirst hsecond) index
    | C_mul_T location value =>
        funext index
        rw [hreflectMonomial, hactMonomial]
        change monomial index * act (LaurentPolynomial.C value *
          LaurentPolynomial.T location) sequence (-index) = _
        rw [hactMonomial]
        dsimp only [reflectSequence]
        rw [show -(index - -location) = -index - location by omega]
        calc
          monomial index * (value * sequence (-index - location)) =
            value * monomial (-location + (index - -location)) *
              sequence (-index - location) := by
                rw [show -location + (index - -location) = index by omega]
                ring
          _ = _ := by rw [← hmonomialMul]; ring
  have hdiagonal : reflectSequence (column leftDiagonalBoundary) =
      column leftDiagonalBoundary := by
    funext index
    exact (left_diagonal_reflection.2.1 index).symm
  let scalarProjection : LaurentPolynomial ℚ →+* LaurentPolynomial ℚ :=
    LaurentPolynomial.C.comp (LaurentPolynomial.eval₂ (RingHom.id ℚ) 1)
  let projection := PowerSeries.map scalarProjection
  have hprojectC (value : ℚ) : scalarProjection (LaurentPolynomial.C value) =
      LaurentPolynomial.C value := by simp [scalarProjection]
  have hprojectionContinuous : Continuous projection := by
    have hscalarContinuous : Continuous scalarProjection := continuous_of_discreteTopology
    exact continuous_pi (fun degree => hscalarContinuous.comp (continuous_apply degree))
  have hparameterProjection : projection parameter = parameter := by
    have halternating : projection alternating = alternating := by
      ext degree
      simp only [projection, alternating, PowerSeries.coeff_map, hprojectC]
    change projection (PowerSeries.X * alternating ^ 2) = _
    rw [map_mul, map_pow, halternating]
    rw [show projection PowerSeries.X = PowerSeries.X by exact PowerSeries.map_X _]
  have hcoefficientProjection (degree : ℕ) :
      projection (PowerSeries.coeff degree
        (forwardSeries true (1 : PowerSeries (LaurentPolynomial ℚ)) 1)) =
      PowerSeries.coeff degree (forwardSeries true (1 : PowerSeries (LaurentPolynomial ℚ)) 1)
      := by
    simp only [forwardSeries, PowerSeries.coeff_mk, Finsupp.linearCombination_apply,
      one_pow, mul_one, Finsupp.sum, map_sum, map_zsmul, map_one]
  have hresidualProjection : projection residual = residual := by
    have hparameter : PowerSeries.HasEval parameter :=
      PowerSeries.HasEval.mul_right (alternating ^ 2) PowerSeries.HasEval.X
    have hsum := PowerSeries.hasSum_eval₂
      (φ := RingHom.id (PowerSeries (LaurentPolynomial ℚ))) continuous_id hparameter
      (forwardSeries true 1 1)
    have hmapped := hsum.map projection.toAddMonoidHom hprojectionContinuous
    simp only [RingHom.id_apply] at hsum
    have hmapped' : HasSum (fun degree => PowerSeries.coeff degree
        (forwardSeries true 1 1) * parameter ^ degree)
        (projection (PowerSeries.eval₂ (RingHom.id _) parameter (forwardSeries true 1 1)))
        := by
      convert hmapped using 1
      funext degree
      change _ = projection (PowerSeries.coeff degree (forwardSeries true 1 1) *
        parameter ^ degree)
      rw [map_mul, map_pow, hparameterProjection, hcoefficientProjection]
      all_goals rfl
    have hsame := hmapped'.unique hsum
    simp only [residual, map_sub, map_one, map_mul, hparameterProjection, hsame]
  have hresidualSupport (degree : ℕ) (index : ℤ) (hne : index ≠ 0) :
      (PowerSeries.coeff degree residual).coeff index = 0 := by
    have hequality := congrArg (fun series => (PowerSeries.coeff degree series).coeff index)
      hresidualProjection
    rw [PowerSeries.coeff_map] at hequality
    change (LaurentPolynomial.C _).coeff index = _ at hequality
    simpa [LaurentPolynomial.C_apply, hne] using hequality.symm
  have hresidualReflection : reflectSequence (column residual) = column residual := by
    funext index
    by_cases hzero : index = 0
    · subst index
      simp [reflectSequence, hmonomialZero]
    · have hvanish (location : ℤ) (hne : location ≠ 0) : column residual location = 0 := by
        dsimp only [column]
        rw [show (PowerSeries.mk fun degree =>
          (PowerSeries.coeff degree residual).coeff location : PowerSeries ℚ) = 0 by
            ext degree
            simp [hresidualSupport degree location hne]]
        exact map_zero _
      simp [reflectSequence, hvanish index hzero, hvanish (-index) (neg_ne_zero.mpr hzero)]
  have hreflectAdd (first second : ℤ → LaurentSeries ℚ) :
      reflectSequence (first + second) = reflectSequence first + reflectSequence second :=
    by funext index; exact mul_add _ _ _
  have hkernelReflected :
      act (reflect (promote first)) (column leftDiagonalBoundary) =
        act (reflect (promote second)) (reflectSequence (column leftKernelBoundary)) +
          act (reflect (promote forcing)) (column residual) := by
    have hequality := congrArg reflectSequence hkernel
    simpa only [hreflectAdd, hreflectAction, hdiagonal, hresidualReflection] using hequality
  let gauge : LaurentPolynomial (PowerSeries ℚ) :=
    (LaurentPolynomial.C q - t) ^ 2 * (1 - t) ^ 2 *
      (1 - LaurentPolynomial.C q * t) ^ 2 * LaurentPolynomial.T (-3)
  let laurentNumerator : LaurentPolynomial (PowerSeries ℚ) :=
    (LaurentPolynomial.C q - 1) ^ 3 * (LaurentPolynomial.C q + 1) ^ 3 *
      (t - 1) ^ 2 * (LaurentPolynomial.C q * t - 1) ^ 2 *
      (LaurentPolynomial.C q * t ^ 2 - 1) * LaurentPolynomial.T (-3)
  let multiplier : LaurentPolynomial (LaurentSeries ℚ) :=
    LaurentPolynomial.C (monomial 1) * (LaurentPolynomial.T 1 - 1) ^ 2 *
      (LaurentPolynomial.C (monomial 1) * LaurentPolynomial.T 1 - 1) ^ 2 *
        LaurentPolynomial.T (-2)
  have hgauge : column leftGauge = act (promote gauge) (column leftKernelBoundary) := by
    have hexpandGauge : expand gauge * leftKernelBoundary = leftGauge := by
      simp only [gauge, t, q, map_mul, map_pow, map_sub, map_one, hexpandC, hexpandT,
        PowerSeries.map_X, leftGauge]
    rw [← hexpandGauge]
    exact hproduct gauge leftKernelBoundary
  have hgaugeReflected : reflectSequence (column leftGauge) =
      act (reflect (promote gauge)) (reflectSequence (column leftKernelBoundary)) := by
    rw [hgauge, hreflectAction]
  let embedding := algebraMap (LaurentPolynomial (LaurentSeries ℚ))
    (FractionRing (LaurentPolynomial (LaurentSeries ℚ)))
  have hinjective := IsFractionRing.injective (LaurentPolynomial (LaurentSeries ℚ))
    (FractionRing (LaurentPolynomial (LaurentSeries ℚ)))
  let qValue := embedding (LaurentPolynomial.C (monomial 1))
  let tValue := embedding (LaurentPolynomial.T 1)
  have hqValue : qValue ≠ 0 := by
    intro hzero
    have hsource := hinjective (hzero.trans (map_zero embedding).symm)
    have hcoefficient := congrArg (fun polynomial => polynomial.coeff 0) hsource
    simp only [LaurentPolynomial.C_apply, if_true, AddMonoidAlgebra.coeff_zero,
      Finsupp.coe_zero, Pi.zero_apply] at hcoefficient
    exact HahnSeries.single_ne_zero one_ne_zero hcoefficient
  have htValue : tValue ≠ 0 := by
    intro hzero
    have hsource := hinjective (hzero.trans (map_zero embedding).symm)
    have hcoefficient := congrArg (fun polynomial => polynomial.coeff 1) hsource
    simp [LaurentPolynomial.T_apply] at hcoefficient
  have hmonoEmbedding (index : ℤ) :
      embedding (LaurentPolynomial.C (HahnSeries.single index (1 : ℚ))) =
        qValue ^ index := by
    change (embedding.comp LaurentPolynomial.C) (HahnSeries.single index 1) = _
    rw [RatFunc.single_zpow, map_zpow₀]
    rfl
  have hTneg (degree : ℕ) : embedding (LaurentPolynomial.T (-(degree : ℤ))) =
      tValue⁻¹ ^ degree := by
    have hinverse : embedding (LaurentPolynomial.T (-1)) = tValue⁻¹ := by
      apply mul_left_cancel₀ htValue
      rw [mul_inv_cancel₀ htValue]
      change embedding (LaurentPolynomial.T 1) * embedding (LaurentPolynomial.T (-1)) = 1
      rw [← map_mul, ← LaurentPolynomial.T_add]
      norm_num
    rw [show -(degree : ℤ) = (degree : ℤ) * -1 by ring,
      ← LaurentPolynomial.T_pow, map_pow, hinverse]
  have hTpos (degree : ℕ) : embedding (LaurentPolynomial.T (degree : ℤ)) =
      tValue ^ degree := by
    rw [show (degree : ℤ) = (degree : ℤ) * 1 by ring,
      ← LaurentPolynomial.T_pow, map_pow]
  have hTnegativeOne : embedding (LaurentPolynomial.T (-1)) = tValue⁻¹ := by
    simpa using hTneg 1
  have hTnegativeTwo : embedding (LaurentPolynomial.T (-2)) = tValue⁻¹ ^ 2 := by
    simpa using hTneg 2
  have hTnegativeThree : embedding (LaurentPolynomial.T (-3)) = tValue⁻¹ ^ 3 := by
    simpa using hTneg 3
  have hTpositiveThree : embedding (LaurentPolynomial.T 3) = tValue ^ 3 := by
    simpa using hTpos 3
  have hmonoNegativeOne : embedding (LaurentPolynomial.C
      (HahnSeries.single (-1) (1 : ℚ))) = qValue⁻¹ := by
    simpa using hmonoEmbedding (-1)
  have hmonoThree : embedding (LaurentPolynomial.C
      (HahnSeries.single 3 (1 : ℚ))) = qValue ^ 3 := by
    simpa using hmonoEmbedding 3
  have hpolynomials :
      multiplier * promote first * reflect (promote second) =
        LaurentPolynomial.C (((q - 1) ^ 2 : PowerSeries ℚ) : LaurentSeries ℚ) *
          promote laurentDenominator * LaurentPolynomial.C (monomial 1) *
            reflect (promote gauge) ∧
      multiplier * reflect (promote first) * promote second =
        LaurentPolynomial.C (((q - 1) ^ 2 : PowerSeries ℚ) : LaurentSeries ℚ) *
          promote laurentDenominator * LaurentPolynomial.C (monomial 1) * promote gauge ∧
      multiplier * (reflect (promote first) * promote forcing -
        promote first * reflect (promote forcing)) =
          LaurentPolynomial.C (((q - 1) ^ 2 : PowerSeries ℚ) : LaurentSeries ℚ) *
            promote laurentNumerator := by
    refine ⟨?_, ?_, ?_⟩
    all_goals
      apply hinjective
      change embedding _ = embedding _
      simp only [multiplier, first, second, forcing, gauge, laurentDenominator,
        laurentNumerator, q, t, inverseT, map_mul, map_pow, map_sub, map_add, map_one,
        map_ofNat, hpromoteC, hpromoteT, hreflectC, hreflectT, PowerSeries.coe_X,
        monomial, neg_neg]
      simp only [hTnegativeOne, hTnegativeTwo, hTnegativeThree, hTpositiveThree,
        hmonoNegativeOne, hmonoThree]
      field_simp [hqValue, htValue]
      ring
  have helimination :
      act (promote first * reflect (promote second))
          (reflectSequence (column leftKernelBoundary)) -
        act (reflect (promote first) * promote second) (column leftKernelBoundary) =
          act (reflect (promote first) * promote forcing -
            promote first * reflect (promote forcing)) (column residual) := by
    have horiginal := congrArg (act (reflect (promote first))) hkernel
    have hreflected := congrArg (act (promote first)) hkernelReflected
    simp only [map_mul, map_sub, LinearMap.map_add, LinearMap.sub_apply,
      Module.End.mul_apply] at horiginal hreflected ⊢
    have hcommute : act (reflect (promote first)) (act (promote first)
        (column leftDiagonalBoundary)) =
      act (promote first) (act (reflect (promote first)) (column leftDiagonalBoundary)) :=
      by rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
    rw [hcommute] at horiginal
    linear_combination horiginal - hreflected
  have hgaugeEquation :
      act (promote laurentDenominator * LaurentPolynomial.C (monomial 1))
          (reflectSequence (column leftGauge) - column leftGauge) =
        act (promote laurentNumerator) (column residual) := by
    have hequality := congrArg (act multiplier) helimination
    simp only [LinearMap.map_sub, ← Module.End.mul_apply, ← map_mul] at hequality
    simp only [← mul_assoc] at hequality
    rw [hpolynomials.1, hpolynomials.2.1, hpolynomials.2.2] at hequality
    simp only [map_mul, Module.End.mul_apply] at hequality
    rw [← hgaugeReflected, ← hgauge] at hequality
    funext index
    have hpoint := congrFun hequality index
    simp only [Pi.sub_apply, hactC] at hpoint
    have hnonzero : (((q - 1) ^ 2 : PowerSeries ℚ) : LaurentSeries ℚ) ≠ 0 := by
      have hsource : (q - 1) ^ 2 ≠ 0 := by
        apply pow_ne_zero
        intro hzero
        have hconstant := congrArg PowerSeries.constantCoeff hzero
        norm_num [q] at hconstant
      intro hzero
      exact hsource (HahnSeries.ofPowerSeries_injective (hzero.trans (map_zero _).symm))
    apply mul_left_cancel₀ hnonzero
    simpa only [map_mul, Module.End.mul_apply, LinearMap.map_sub, Pi.sub_apply, mul_sub]
      using hpoint
  have hcolumnSub (first second : PowerSeries (LaurentPolynomial ℚ)) :
      column (first - second) = column first - column second := by
    funext index
    dsimp only [column]
    simp only [Pi.sub_apply]
    rw [← map_sub]
    congr 1
  have hcolumnInjective : Function.Injective column := by
    intro first second hequality
    ext degree index
    have hpoint := HahnSeries.ofPowerSeries_injective (congrFun hequality index)
    simpa only [PowerSeries.coeff_mk] using congrArg (PowerSeries.coeff degree) hpoint
  have hgaugeSymmetry (index : ℤ) : column leftGauge (-index) = column leftGauge index :=
    by
    dsimp only [column]
    congr 1
    ext degree
    have hequality := congrArg (fun series => (PowerSeries.coeff degree series).coeff index)
      left_gauge_moment.2.1
    rw [PowerSeries.coeff_map] at hequality
    change (LaurentPolynomial.invert (PowerSeries.coeff degree leftGauge)).coeff index =
      (PowerSeries.coeff degree leftGauge).coeff index at hequality
    simpa only [PowerSeries.coeff_mk, LaurentPolynomial.invert_apply] using hequality
  have hshift : column leftShiftedGauge =
      act (LaurentPolynomial.C (monomial 3)) (reflectSequence (column leftGauge)) := by
    funext index
    rw [hactC]
    dsimp only [reflectSequence]
    rw [hgaugeSymmetry, ← mul_assoc, hmonomialMul]
    exact (left_gauge_moment.2.2.2.1 index).1.trans
      (by rw [add_comm index 3])
  have hcleared : expand laurentDenominator * (leftShiftedGauge -
        PowerSeries.X ^ 3 * leftGauge) = PowerSeries.X ^ 2 * expand laurentNumerator * residual :=
      by
    apply hcolumnInjective
    rw [hproduct, hcolumnSub, hshift]
    have hqcube : column (PowerSeries.X ^ 3 * leftGauge) =
        act (LaurentPolynomial.C (monomial 3)) (column leftGauge) := by
      have hequality := hproduct (LaurentPolynomial.C (q ^ 3)) leftGauge
      simpa only [hexpandC, map_pow (PowerSeries.map LaurentPolynomial.C),
        PowerSeries.map_X, q, hpromoteC,
        PowerSeries.coe_pow, PowerSeries.coe_X, HahnSeries.single_pow,
        one_pow, nsmul_eq_mul, mul_one, monomial, Nat.cast_ofNat] using hequality
    rw [hqcube, ← LinearMap.map_sub]
    have hequality := congrArg (act (LaurentPolynomial.C (monomial 2))) hgaugeEquation
    simp only [← Module.End.mul_apply, ← map_mul] at hequality ⊢
    rw [show promote laurentDenominator * LaurentPolynomial.C (monomial 3) =
      LaurentPolynomial.C (monomial 2) *
        (promote laurentDenominator * LaurentPolynomial.C (monomial 1)) by
          rw [show monomial 3 = monomial 2 * monomial 1 by rw [hmonomialMul]; rfl,
            map_mul]; ring]
    rw [hequality]
    have hequality := hproduct (LaurentPolynomial.C (q ^ 2) * laurentNumerator) residual
    simpa only [map_mul, hexpandC, map_pow (PowerSeries.map LaurentPolynomial.C),
      PowerSeries.map_X, q, hpromoteC,
      PowerSeries.coe_pow, PowerSeries.coe_X, HahnSeries.single_pow, one_pow,
      nsmul_eq_mul, mul_one, monomial, Nat.cast_ofNat] using hequality.symm
  have hdenominatorNonzero : expand laurentDenominator ≠ 0 := by
    intro hzero
    have hconstant := congrArg PowerSeries.constantCoeff hzero
    simp [laurentDenominator, hexpandC, q] at hconstant
  have hforcing : expand laurentDenominator * leftRationalNumerator = expand laurentNumerator := by
    simpa only [denominator, numerator, laurentDenominator, laurentNumerator, q, t, inverseT,
      map_mul, map_sub, map_add, map_pow, map_one, map_ofNat, hexpandC, hexpandT, PowerSeries.map_X,
      LaurentPolynomial.T_pow, nsmul_eq_mul, mul_one, Nat.cast_ofNat]
      using hrational
  have hadditive : leftShiftedGauge - PowerSeries.X ^ 3 * leftGauge =
      PowerSeries.X ^ 2 * residual * leftRationalNumerator := by
    apply mul_left_cancel₀ hdenominatorNonzero
    rw [hcleared]
    rw [show expand laurentDenominator * (PowerSeries.X ^ 2 * residual * leftRationalNumerator) =
      PowerSeries.X ^ 2 * (expand laurentDenominator * leftRationalNumerator) * residual by ring,
      hforcing]
  let evaluation := LaurentPolynomial.eval₂ (RingHom.id ℚ) 1
  let scalarResidual : PowerSeries ℚ := PowerSeries.map evaluation residual
  have hembed : PowerSeries.map LaurentPolynomial.C scalarResidual = residual := by
    change (PowerSeries.map LaurentPolynomial.C).comp (PowerSeries.map evaluation) residual = _
    rw [← PowerSeries.map_comp]
    exact hresidualProjection
  have hscalarProduct (series : PowerSeries (LaurentPolynomial ℚ)) (index : ℤ) :
      column (residual * series) index =
        (scalarResidual : LaurentSeries ℚ) * column series index := by
    rw [← hembed]
    have hequality := congrFun (hproduct (LaurentPolynomial.C scalarResidual) series) index
    simpa only [hexpandC, hpromoteC, hactC] using hequality
  let scalarColumn (series : PowerSeries (LaurentPolynomial ℚ)) (index : ℕ) :
      PowerSeries ℚ := PowerSeries.mk fun degree =>
        (PowerSeries.coeff degree series).coeff index
  have hpositive (index : ℕ) :
      q * (PowerSeries.X ^ index - 1) * scalarColumn leftGauge index =
        scalarResidual * scalarColumn leftRationalNumerator index := by
    have hequality := congrFun (congrArg column hadditive) (index : ℤ)
    rw [hcolumnSub, hshift] at hequality
    simp only [Pi.sub_apply, hactC] at hequality
    have hqpower (power : ℕ) (series : PowerSeries (LaurentPolynomial ℚ)) :
        column (PowerSeries.X ^ power * series) (index : ℤ) =
          monomial power * column series index := by
      have hequality := congrFun (hproduct (LaurentPolynomial.C (q ^ power)) series)
        (index : ℤ)
      simpa only [hexpandC, q, map_pow (PowerSeries.map LaurentPolynomial.C),
        PowerSeries.map_X, hpromoteC, hactC,
        PowerSeries.coe_pow, PowerSeries.coe_X, HahnSeries.single_pow, one_pow,
        nsmul_eq_mul, mul_one, monomial] using hequality
    rw [mul_assoc (PowerSeries.X ^ 2) residual leftRationalNumerator] at hequality
    rw [hqpower 3 leftGauge, hqpower 2 (residual * leftRationalNumerator),
      hscalarProduct] at hequality
    norm_num only [Nat.cast_ofNat] at hequality
    dsimp only [reflectSequence] at hequality
    rw [hgaugeSymmetry] at hequality
    have hqnonzero : monomial 2 ≠ 0 := HahnSeries.single_ne_zero one_ne_zero
    have hcancel : monomial 1 * (monomial index - 1) * column leftGauge index =
        (scalarResidual : LaurentSeries ℚ) * column leftRationalNumerator index := by
      apply mul_left_cancel₀ hqnonzero
      calc
        monomial 2 * (monomial 1 * (monomial index - 1) * column leftGauge index) =
          monomial 3 * (monomial index * column leftGauge index) -
            monomial 3 * column leftGauge index := by
              rw [show monomial 3 = monomial 2 * monomial 1 by
                simpa using (hmonomialMul 2 1).symm]
              ring
        _ = _ := hequality
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℚ)
    simpa only [map_mul, map_sub, map_one, q, PowerSeries.coe_X, map_pow,
      HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one, monomial,
      column, scalarColumn] using hcancel
  have hsolved (index : ℕ) (hne : index ≠ 0) :
      q * scalarColumn leftGauge index =
        -(scalarResidual * scalarColumn leftRationalNumerator index *
          PowerSeries.invOfUnit (1 - PowerSeries.X ^ index) 1) := by
    have hinverse := PowerSeries.mul_invOfUnit
      (1 - PowerSeries.X ^ index : PowerSeries ℚ) 1 (by simp [hne])
    have hequality := congrArg
      (fun series => series * PowerSeries.invOfUnit (1 - PowerSeries.X ^ index) 1)
      (hpositive index)
    calc
      q * scalarColumn leftGauge index = q * scalarColumn leftGauge index *
          ((1 - PowerSeries.X ^ index) *
            PowerSeries.invOfUnit (1 - PowerSeries.X ^ index) 1) := by rw [hinverse, mul_one]
      _ = -(q * (PowerSeries.X ^ index - 1) * scalarColumn leftGauge index *
          PowerSeries.invOfUnit (1 - PowerSeries.X ^ index) 1) := by ring
      _ = _ := by rw [hequality]
  letI : UniformSpace ℚ := ⊥
  letI : DiscreteUniformity ℚ := ⟨rfl⟩
  have hleft := left_gauge_moment.2.2.1.mul_left q
  have hright := hLambertSum.mul_left scalarResidual
  have hterms (index : ℕ) :
      q * (PowerSeries.C ((index : ℚ) ^ 2) * scalarColumn leftGauge index) =
        scalarResidual * (if index = 0 then 0 else PowerSeries.C (-(index : ℚ) ^ 2) *
          scalarColumn leftRationalNumerator index *
            PowerSeries.invOfUnit (1 - PowerSeries.X ^ index) 1) := by
    by_cases hzero : index = 0
    · subst index; simp
    · rw [if_neg hzero, show q * (PowerSeries.C ((index : ℚ) ^ 2) *
        scalarColumn leftGauge index) = PowerSeries.C ((index : ℚ) ^ 2) *
          (q * scalarColumn leftGauge index) by ring, hsolved index hzero, map_neg]
      ring
  have hequality : q * ((1 - q) ^ 4 * PowerSeries.map evaluation leftKernelBoundary) =
      scalarResidual * leftLambertSum := by
    exact (hleft.congr_fun (fun index => (hterms index).symm)).unique hright
  have hfactorNonzero : q * (1 - q) ^ 4 ≠ 0 := by
    apply mul_ne_zero PowerSeries.X_ne_zero
    apply pow_ne_zero
    intro hzero
    have hconstant := congrArg PowerSeries.constantCoeff hzero
    norm_num [q] at hconstant
  change PowerSeries.map evaluation leftKernelBoundary = scalarResidual * leftScalarMoment
  apply mul_left_cancel₀ hfactorNonzero
  calc
    q * (1 - q) ^ 4 * PowerSeries.map evaluation leftKernelBoundary =
      scalarResidual * leftLambertSum := by simpa only [mul_assoc] using hequality
    _ = q * (1 - q) ^ 4 * (scalarResidual * leftScalarMoment) := by
      rw [← hScalarShift]
      dsimp only [q]
      ring

end D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftMoment
