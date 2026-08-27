/- GID: D5/S3/Quantum/Measurement/SharpMeasurementCompatibility
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/SharpMeasurementCompatibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Joint sharp measurements are exactly commuting ones, unlike general effects. -/

import D5.S3.Observer.Conditioning
import D5.S3.Quantum.QubitWitnesses

/- Library-search audit trail (2026-08-27):
   * Exact family hit `Observer.Conditioning.IsRecordMeasurement` is the
     canonical finite PVM predicate and is reused without redeclaration.
   * Frozen `CommutingProjectionFourSector` proves a binary-outcome special
     case but does not cover arbitrary finite outcome types or the nonsharp
     contrast. `StaticEffectSequentialSeparation` concerns sequential laws.
   * Repository and pinned-Mathlib searches found no exact whole theorem.
     Matrix finite-sum identities and
     `Matrix.posSemidef_vecMulVec_self_star` supply the proof components. -/

open scoped BigOperators ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Measurement.SharpMeasurementCompatibility

open D5.S3.Observer.Conditioning
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.QubitWitnesses

private theorem finite_sharp_joint_iff_commute
    {n A B : Type*}
    [Fintype n] [DecidableEq n]
    [Fintype A]
    [Fintype B]
    (P : A -> Matrix n n ℂ) (Q : B -> Matrix n n ℂ)
    (hP : IsRecordMeasurement P) (hQ : IsRecordMeasurement Q) :
    (Exists fun R : A × B -> Matrix n n ℂ =>
        IsRecordMeasurement R /\
          (forall a, P a = ∑ b, R (a, b)) /\
          (forall b, Q b = ∑ a, R (a, b))) <->
      forall a b, P a * Q b = Q b * P a := by
  classical
  constructor
  · rintro ⟨R, hR, hFirst, hSecond⟩ a b
    have hProduct : P a * Q b = R (a, b) := by
      rw [hFirst a, hSecond b, Matrix.sum_mul]
      simp_rw [Matrix.mul_sum]
      calc
        (∑ b', ∑ a', R (a, b') * R (a', b)) =
            ∑ a', R (a, b) * R (a', b) := by
          apply Finset.sum_eq_single b
          · intro b' _ hb'
            apply Finset.sum_eq_zero
            intro a' _
            exact hR.orthogonal (a, b') (a', b) (by
              intro pairsEqual
              exact hb' (Prod.mk.inj pairsEqual).2)
          · simp
        _ = R (a, b) * R (a, b) := by
          apply Finset.sum_eq_single a
          · intro a' _ ha'
            exact hR.orthogonal (a, b) (a', b) (by
              intro pairsEqual
              exact ha' (Prod.mk.inj pairsEqual).1.symm)
          · simp
        _ = R (a, b) := hR.idempotent (a, b)
    calc
      P a * Q b = R (a, b) := hProduct
      _ = star (R (a, b)) := (hR.selfAdjoint (a, b)).symm
      _ = star (P a * Q b) := congrArg star hProduct.symm
      _ = Q b * P a := by rw [star_mul, hP.selfAdjoint, hQ.selfAdjoint]
  · intro hCommute
    let R : A × B -> Matrix n n ℂ := fun outcome => P outcome.1 * Q outcome.2
    have hR : IsRecordMeasurement R := by
      refine
        { selfAdjoint := ?_
          idempotent := ?_
          orthogonal := ?_
          complete := ?_ }
      · intro outcome
        rcases outcome with ⟨a, b⟩
        simp only [R, star_mul, hP.selfAdjoint, hQ.selfAdjoint]
        exact (hCommute a b).symm
      · intro outcome
        rcases outcome with ⟨a, b⟩
        dsimp [R]
        calc
          (P a * Q b) * (P a * Q b) = P a * (Q b * P a) * Q b := by
            simp only [Matrix.mul_assoc]
          _ = P a * (P a * Q b) * Q b := by rw [← hCommute a b]
          _ = (P a * P a) * (Q b * Q b) := by simp only [Matrix.mul_assoc]
          _ = P a * Q b := by rw [hP.idempotent, hQ.idempotent]
      · intro first second distinct
        rcases first with ⟨a, b⟩
        rcases second with ⟨a', b'⟩
        dsimp [R]
        by_cases haa' : a = a'
        · subst a'
          have hbb' : b ≠ b' := by
            intro h
            subst b'
            exact distinct rfl
          calc
            (P a * Q b) * (P a * Q b') = P a * (Q b * P a) * Q b' := by
              simp only [Matrix.mul_assoc]
            _ = P a * (P a * Q b) * Q b' := by rw [← hCommute a b]
            _ = (P a * P a) * (Q b * Q b') := by simp only [Matrix.mul_assoc]
            _ = 0 := by rw [hP.idempotent, hQ.orthogonal b b' hbb', Matrix.mul_zero]
        · calc
            (P a * Q b) * (P a' * Q b') = P a * (Q b * P a') * Q b' := by
              simp only [Matrix.mul_assoc]
            _ = P a * (P a' * Q b) * Q b' := by rw [← hCommute a' b]
            _ = (P a * P a') * (Q b * Q b') := by simp only [Matrix.mul_assoc]
            _ = 0 := by rw [hP.orthogonal a a' haa', Matrix.zero_mul]
      · rw [show (∑ outcome : A × B, R outcome) =
            ∑ a, ∑ b, P a * Q b by
          simp only [R, Fintype.sum_prod_type]]
        simp_rw [← Matrix.mul_sum]
        rw [hQ.complete]
        simp only [Matrix.mul_one, hP.complete]
    refine ⟨R, hR, ?_, ?_⟩
    · intro a
      dsimp [R]
      rw [← Matrix.mul_sum, hQ.complete, Matrix.mul_one]
    · intro b
      dsimp [R]
      rw [← Matrix.sum_mul, hP.complete, Matrix.one_mul]

private theorem jointly_measurable_noncommuting_effects :
    let zPlus : QubitState := ![1, 0]
    let zMinus : QubitState := ![0, 1]
    let xPlus : QubitState := ![1, 1]
    let xMinus : QubitState := ![1, -1]
    let joint : Bool × Bool -> QubitMatrix := fun outcome =>
      match outcome with
      | (false, false) =>
          (1 / 2 : Real) • Matrix.vecMulVec zPlus (star zPlus)
      | (false, true) =>
          (1 / 4 : Real) • Matrix.vecMulVec xPlus (star xPlus)
      | (true, false) =>
          (1 / 4 : Real) • Matrix.vecMulVec xMinus (star xMinus)
      | (true, true) =>
          (1 / 2 : Real) • Matrix.vecMulVec zMinus (star zMinus)
    let first : Bool -> QubitMatrix := fun a => ∑ b, joint (a, b)
    let second : Bool -> QubitMatrix := fun b => ∑ a, joint (a, b)
    (forall outcome, (joint outcome).PosSemidef) /\
      (∑ outcome, joint outcome) = 1 /\
      Not (IsRecordMeasurement first) /\
      Not (IsRecordMeasurement second) /\
      first false * second false ≠ second false * first false := by
  dsimp
  let zPlus : QubitState := ![1, 0]
  let zMinus : QubitState := ![0, 1]
  let xPlus : QubitState := ![1, 1]
  let xMinus : QubitState := ![1, -1]
  let joint : Bool × Bool -> QubitMatrix := fun outcome =>
    match outcome with
    | (false, false) =>
        (1 / 2 : Real) • Matrix.vecMulVec zPlus (star zPlus)
    | (false, true) =>
        (1 / 4 : Real) • Matrix.vecMulVec xPlus (star xPlus)
    | (true, false) =>
        (1 / 4 : Real) • Matrix.vecMulVec xMinus (star xMinus)
    | (true, true) =>
        (1 / 2 : Real) • Matrix.vecMulVec zMinus (star zMinus)
  let first : Bool -> QubitMatrix := fun a => ∑ b, joint (a, b)
  let second : Bool -> QubitMatrix := fun b => ∑ a, joint (a, b)
  have hPositive : forall outcome, (joint outcome).PosSemidef := by
    rintro ⟨a, b⟩
    cases a <;> cases b
    all_goals
      dsimp [joint]
      exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by norm_num)
  have hComplete : (∑ outcome, joint outcome) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [joint, zPlus, zMinus, xPlus, xMinus,
        Matrix.vecMulVec_apply, Matrix.smul_apply, Fintype.sum_prod_type,
        Fintype.sum_bool, Matrix.one_apply]
  have hFirstNonsharp : Not (IsRecordMeasurement first) := by
    intro hSharp
    have hEntry := congrFun (congrFun (hSharp.idempotent false) 0) 0
    norm_num [first, joint, zPlus, xPlus, Matrix.mul_apply,
      Matrix.vecMulVec_apply, Matrix.smul_apply, Fintype.sum_bool,
      Fin.sum_univ_two] at hEntry
  have hSecondNonsharp : Not (IsRecordMeasurement second) := by
    intro hSharp
    have hEntry := congrFun (congrFun (hSharp.idempotent false) 0) 0
    norm_num [second, joint, zPlus, xMinus, Matrix.mul_apply,
      Matrix.vecMulVec_apply, Matrix.smul_apply, Fintype.sum_bool,
      Fin.sum_univ_two] at hEntry
  have hNoncommuting :
      first false * second false ≠ second false * first false := by
    intro hCommute
    have hEntry := congrFun (congrFun hCommute 0) 1
    norm_num [first, second, joint, zPlus, xPlus, xMinus,
      Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply,
      Fintype.sum_bool, Fin.sum_univ_two] at hEntry
  exact ⟨hPositive, hComplete, hFirstNonsharp, hSecondNonsharp, hNoncommuting⟩

/-- Two arbitrary finite sharp measurements admit a joint sharp measurement
exactly when all cross-family projections commute. In contrast, the displayed
positive normalized qubit joint measurement has two nonsharp marginals with a
noncommuting pair of effects. -/
theorem sharp_measurement_compatibility
    {n A B : Type*}
    [Fintype n] [DecidableEq n]
    [Fintype A]
    [Fintype B]
    (P : A -> Matrix n n ℂ) (Q : B -> Matrix n n ℂ)
    (hP : IsRecordMeasurement P) (hQ : IsRecordMeasurement Q) :
    ((Exists fun R : A × B -> Matrix n n ℂ =>
        IsRecordMeasurement R /\
          (forall a, P a = ∑ b, R (a, b)) /\
          (forall b, Q b = ∑ a, R (a, b))) <->
        forall a b, P a * Q b = Q b * P a) /\
      (let zPlus : QubitState := ![1, 0]
       let zMinus : QubitState := ![0, 1]
       let xPlus : QubitState := ![1, 1]
       let xMinus : QubitState := ![1, -1]
       let joint : Bool × Bool -> QubitMatrix := fun outcome =>
         match outcome with
         | (false, false) =>
             (1 / 2 : Real) • Matrix.vecMulVec zPlus (star zPlus)
         | (false, true) =>
             (1 / 4 : Real) • Matrix.vecMulVec xPlus (star xPlus)
         | (true, false) =>
             (1 / 4 : Real) • Matrix.vecMulVec xMinus (star xMinus)
         | (true, true) =>
             (1 / 2 : Real) • Matrix.vecMulVec zMinus (star zMinus)
       let first : Bool -> QubitMatrix := fun a => ∑ b, joint (a, b)
       let second : Bool -> QubitMatrix := fun b => ∑ a, joint (a, b)
       (forall outcome, (joint outcome).PosSemidef) /\
         (∑ outcome, joint outcome) = 1 /\
         Not (IsRecordMeasurement first) /\
         Not (IsRecordMeasurement second) /\
         first false * second false ≠ second false * first false) := by
  exact
    ⟨finite_sharp_joint_iff_commute P Q hP hQ,
      jointly_measurable_noncommuting_effects⟩

#print axioms sharp_measurement_compatibility

end D5.S3.Quantum.Measurement.SharpMeasurementCompatibility
