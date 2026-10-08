/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207ThetaDifferential
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207ThetaDifferential
   mirror-E: none(waiver:formal-theta-differential-identity)
   anchors: [mathlib/module/Mathlib.Algebra.TrivSqZeroExt.Basic]
   utility: none
   digest: Square-zero Taylor jets extract the differential duplication identity from addition. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207ThetaNormalization
import Mathlib.Algebra.TrivSqZeroExt.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207ThetaDifferential

open InversionSeq207ThetaSpecialization InversionSeq207ThetaNormalization
open InversionSeq207TripleProduct

set_option maxHeartbeats 1600000 in
theorem theta_duplication_derivative :
    let theta := normalizedTheta (1 : ℚ)
    let derivative := fun series : PowerSeries (PowerSeries ℚ) =>
      PowerSeries.mk fun degree => PowerSeries.derivative ℚ (PowerSeries.coeff degree series)
    let linear := -PowerSeries.pentagonalSeries ℚ ^ 2
    derivative (derivative (derivative theta)) * theta ^ 3 -
        3 * derivative (derivative theta) * derivative theta * theta ^ 2 +
        2 * derivative theta ^ 3 * theta =
      PowerSeries.map PowerSeries.C (linear ^ 3) * normalizedTheta (2 : ℚ) := by
  classical
  let theta := normalizedTheta (1 : ℚ)
  let derivative := fun series : PowerSeries (PowerSeries ℚ) =>
    PowerSeries.mk fun degree => PowerSeries.derivative ℚ (PowerSeries.coeff degree series)
  let jet {R : Type} [CommRing R] [Algebra ℚ R] (order : ℕ) (direction : R) :=
    PowerSeries.map (PowerSeries.rescale direction)
      (PowerSeries.map (PowerSeries.map (algebraMap ℚ R)) (derivative^[order] theta))
  have hcoeff {R : Type} [CommRing R] [Algebra ℚ R]
      (order : ℕ) (direction : R) (degree index : ℕ) :
      PowerSeries.coeff index (PowerSeries.coeff degree (jet order direction)) =
        direction ^ index * algebraMap ℚ R
          (PowerSeries.coeff index (PowerSeries.coeff degree (derivative^[order] theta))) := by
    dsimp only [jet]
    rw [PowerSeries.coeff_map, PowerSeries.coeff_rescale, PowerSeries.coeff_map,
      PowerSeries.coeff_map]
  have hscale {R : Type} [CommRing R] [Algebra ℚ R] (direction : R) :
      normalizedTheta direction = jet 0 direction := by
    let character {S : Type} [CommRing S] [Algebra ℚ S] (value : S) :
        Multiplicative ℤ →* PowerSeries S :=
      { toFun := fun index => PowerSeries.rescale (value * (index.toAdd : S))
          (PowerSeries.exp S)
        map_one' := by simp [PowerSeries.rescale_zero]
        map_mul' := by
          intro first second
          change PowerSeries.rescale (value * ((first.toAdd + second.toAdd : ℤ) : S))
            (PowerSeries.exp S) = _
          rw [PowerSeries.exp_mul_exp_eq_exp_add]
          congr 1
          push_cast
          ring }
    let evaluate {S : Type} [CommRing S] [Algebra ℚ S] (value : S) :=
      AddMonoidAlgebra.liftNCRingHom (PowerSeries.C.comp (algebraMap ℚ S))
        (character value) (fun _ _ => Commute.all _ _)
    let transport := (PowerSeries.rescale direction).comp
      (PowerSeries.map (algebraMap ℚ R))
    have hexponential (value : ℚ) :
        transport (PowerSeries.rescale value (PowerSeries.exp ℚ)) =
          PowerSeries.rescale (direction * algebraMap ℚ R value) (PowerSeries.exp R) := by
      dsimp only [transport, RingHom.comp_apply]
      rw [← PowerSeries.rescale_map, PowerSeries.map_exp, PowerSeries.rescale_rescale]
      congr 1
      ring
    have hevaluate : evaluate direction = transport.comp (evaluate (1 : ℚ)) := by
      apply AddMonoidAlgebra.ringHom_ext'
      · apply RingHom.ext
        intro value
        change evaluate direction (AddMonoidAlgebra.single 0 value) =
          transport (evaluate (1 : ℚ) (AddMonoidAlgebra.single 0 value))
        change AddMonoidAlgebra.liftNCRingHom _ _ _
          (AddMonoidAlgebra.single 0 value) = transport
            (AddMonoidAlgebra.liftNCRingHom _ _ _ (AddMonoidAlgebra.single 0 value))
        rw [AddMonoidAlgebra.liftNCRingHom_single,
          AddMonoidAlgebra.liftNCRingHom_single]
        simp [transport, character, PowerSeries.rescale_zero]
      · apply MonoidHom.ext
        intro index
        change evaluate direction (AddMonoidAlgebra.single index.toAdd 1) =
          transport (evaluate (1 : ℚ) (AddMonoidAlgebra.single index.toAdd 1))
        simp only [evaluate, AddMonoidAlgebra.liftNCRingHom_single,
          map_one, one_mul, character, MonoidHom.coe_mk, OneHom.coe_mk]
        rw [hexponential]
        simp
    apply PowerSeries.ext
    intro degree
    change PowerSeries.coeff degree
        (PowerSeries.C (PowerSeries.rescale (-direction * algebraMap ℚ R (1 / 2))
          (PowerSeries.exp R)) * PowerSeries.map (evaluate direction) formalTheta) = _
    simp only [jet, Function.iterate_zero, id_eq, PowerSeries.coeff_map, theta]
    rw [PowerSeries.coeff_C_mul]
    change _ = transport (PowerSeries.coeff degree
      (PowerSeries.C (PowerSeries.rescale (-1 * algebraMap ℚ ℚ (1 / 2))
        (PowerSeries.exp ℚ)) * PowerSeries.map (evaluate (1 : ℚ)) formalTheta))
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_map]
    change _ = transport
      (PowerSeries.rescale (-(1 : ℚ) * algebraMap ℚ ℚ (1 / 2)) (PowerSeries.exp ℚ) *
        evaluate (1 : ℚ) (PowerSeries.coeff degree formalTheta))
    rw [map_mul, hexponential, hevaluate]
    simp [transport]
  let split {R : Type} [CommRing R] :
      PowerSeries (TrivSqZeroExt R R) →+*
        TrivSqZeroExt (PowerSeries R) (PowerSeries R) :=
    { toFun := fun series =>
        ((PowerSeries.mk fun degree => (PowerSeries.coeff degree series).fst,
          PowerSeries.mk fun degree => (PowerSeries.coeff degree series).snd) :
            TrivSqZeroExt (PowerSeries R) (PowerSeries R))
      map_one' := by
        apply TrivSqZeroExt.ext <;> apply PowerSeries.ext <;> intro degree <;>
          simp only [TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk, PowerSeries.coeff_mk,
            PowerSeries.coeff_one, TrivSqZeroExt.fst_one, TrivSqZeroExt.snd_one] <;>
          split_ifs <;> simp_all
      map_zero' := by
        apply TrivSqZeroExt.ext <;> apply PowerSeries.ext <;> intro degree <;>
          simp [TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk]
      map_add' := by
        intro first second
        apply TrivSqZeroExt.ext
        · change PowerSeries.mk (fun degree =>
              (PowerSeries.coeff degree (first + second)).fst) =
            PowerSeries.mk (fun degree => (PowerSeries.coeff degree first).fst) +
              PowerSeries.mk (fun degree => (PowerSeries.coeff degree second).fst)
          apply PowerSeries.ext
          intro degree
          simp
        · change PowerSeries.mk (fun degree =>
              (PowerSeries.coeff degree (first + second)).snd) =
            PowerSeries.mk (fun degree => (PowerSeries.coeff degree first).snd) +
              PowerSeries.mk (fun degree => (PowerSeries.coeff degree second).snd)
          apply PowerSeries.ext
          intro degree
          simp
      map_mul' := by
        intro first second
        apply TrivSqZeroExt.ext
        · change PowerSeries.mk (fun degree =>
              (PowerSeries.coeff degree (first * second)).fst) =
            PowerSeries.mk (fun degree => (PowerSeries.coeff degree first).fst) *
              PowerSeries.mk (fun degree => (PowerSeries.coeff degree second).fst)
          apply PowerSeries.ext
          intro degree
          simp [PowerSeries.coeff_mul, TrivSqZeroExt.fst_sum]
        · change PowerSeries.mk (fun degree =>
              (PowerSeries.coeff degree (first * second)).snd) =
            PowerSeries.mk (fun degree => (PowerSeries.coeff degree first).fst) *
                PowerSeries.mk (fun degree => (PowerSeries.coeff degree second).snd) +
              PowerSeries.mk (fun degree => (PowerSeries.coeff degree first).snd) *
                PowerSeries.mk (fun degree => (PowerSeries.coeff degree second).fst)
          apply PowerSeries.ext
          intro degree
          simp only [PowerSeries.coeff_mk, TrivSqZeroExt.snd_mul, smul_eq_mul,
            op_smul_eq_smul, PowerSeries.coeff_mul, TrivSqZeroExt.snd_sum,
            map_add, Finset.sum_add_distrib]
          congr 1
          apply Finset.sum_congr rfl
          intro pair _
          ring }
  let splitDouble {R : Type} [CommRing R] :=
    (@split (PowerSeries R) _).comp (PowerSeries.map (@split R _))
  have hsplitMul {R : Type} [CommRing R]
      (first second : PowerSeries (PowerSeries (TrivSqZeroExt R R))) :
      splitDouble (first * second) = splitDouble first * splitDouble second :=
    RingHom.map_mul _ _ _
  have hsplitAdd {R : Type} [CommRing R]
      (first second : PowerSeries (PowerSeries (TrivSqZeroExt R R))) :
      splitDouble (first + second) = splitDouble first + splitDouble second :=
    RingHom.map_add _ _ _
  have hsplitSub {R : Type} [CommRing R]
      (first second : PowerSeries (PowerSeries (TrivSqZeroExt R R))) :
      splitDouble (first - second) = splitDouble first - splitDouble second :=
    map_sub _ _ _
  have hsplitPow {R : Type} [CommRing R]
      (series : PowerSeries (PowerSeries (TrivSqZeroExt R R))) (index : ℕ) :
      splitDouble (series ^ index) = splitDouble series ^ index := map_pow _ _ _
  have hsplit {R : Type} [CommRing R] (series : PowerSeries (PowerSeries
      (TrivSqZeroExt R R))) :
      splitDouble series =
        ((PowerSeries.mk fun degree => PowerSeries.mk fun index =>
            (PowerSeries.coeff index (PowerSeries.coeff degree series)).fst,
          PowerSeries.mk fun degree => PowerSeries.mk fun index =>
            (PowerSeries.coeff index (PowerSeries.coeff degree series)).snd) :
          TrivSqZeroExt (PowerSeries (PowerSeries R)) (PowerSeries (PowerSeries R))) := by
    apply TrivSqZeroExt.ext <;> apply PowerSeries.ext <;> intro degree <;>
      apply PowerSeries.ext <;> intro index <;> rfl
  have hjet {R : Type} [CommRing R] [Algebra ℚ R] (order : ℕ) (first second : R) :
      splitDouble (R := R)
          (jet (R := TrivSqZeroExt R R) order ((first, second) : TrivSqZeroExt R R)) =
        (jet order first,
          PowerSeries.C (PowerSeries.X * PowerSeries.C second) * jet (order + 1) first) := by
    rw [hsplit (R := R)]
    apply TrivSqZeroExt.ext <;> apply PowerSeries.ext <;> intro degree <;>
      apply PowerSeries.ext <;> intro index
    · simp only [TrivSqZeroExt.fst_mk, PowerSeries.coeff_mk]
      rw [hcoeff, hcoeff]
      simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow,
        TrivSqZeroExt.fst_mk, TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.fst_inl]
    · cases index with
      | zero =>
          simp only [TrivSqZeroExt.snd_mk, PowerSeries.coeff_mk]
          rw [hcoeff]
          simp only [pow_zero, one_mul, TrivSqZeroExt.algebraMap_eq_inl',
            TrivSqZeroExt.snd_inl]
          rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
          simp only [map_mul, PowerSeries.constantCoeff_X, zero_mul]
      | succ index =>
          simp only [TrivSqZeroExt.snd_mk, PowerSeries.coeff_mk]
          rw [hcoeff]
          rw [PowerSeries.coeff_C_mul, mul_assoc, PowerSeries.coeff_succ_X_mul,
            PowerSeries.coeff_C_mul, hcoeff]
          simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_pow, TrivSqZeroExt.snd_pow,
            TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk, TrivSqZeroExt.algebraMap_eq_inl',
            TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, mul_zero,
            nsmul_eq_mul, smul_eq_mul, op_smul_eq_smul,
            Nat.pred_succ, Function.iterate_succ_apply', derivative,
            PowerSeries.coeff_mk, PowerSeries.coeff_derivative]
          push_cast
          ring
  have hzero {R : Type} [CommRing R] [Algebra ℚ R] : jet 0 (0 : R) = 0 := by
    rw [← hscale]
    have hconstant := (theta_exponential_normalization (1 : ℚ)).2.1
    apply PowerSeries.ext
    intro degree
    apply PowerSeries.ext
    intro index
    have hbase := congrArg (PowerSeries.coeff degree) hconstant
    simp only [PowerSeries.coeff_map, map_zero] at hbase
    rw [hscale]
    rw [hcoeff]
    cases index with
    | zero =>
        simp only [Function.iterate_zero, id_eq, theta, pow_zero, one_mul,
          PowerSeries.coeff_zero_eq_constantCoeff, hbase, map_zero]
    | succ index => simp
  have hodd {R : Type} [CommRing R] [Algebra ℚ R] (direction : R) :
      jet 0 (-direction) = -jet 0 direction := by
    have hbase := (theta_exponential_normalization (1 : ℚ)).1
    apply PowerSeries.ext
    intro degree
    apply PowerSeries.ext
    intro index
    have hcoefficient := congrArg
      (fun series => PowerSeries.coeff index (PowerSeries.coeff degree series)) hbase
    simp only [PowerSeries.coeff_map, PowerSeries.coeff_rescale,
      map_neg] at hcoefficient
    simp only [map_neg, hcoeff, Function.iterate_zero, id_eq]
    have hpower (exponent : ℕ) : (-direction) ^ exponent = direction ^ exponent *
        algebraMap ℚ R ((-1 : ℚ) ^ exponent) := by
      induction exponent with
      | zero => simp
      | succ exponent ih =>
          simp only [pow_succ, map_mul, ih, map_neg, map_one]
          ring
    rw [hpower]
    change (-1 : ℚ) ^ index * PowerSeries.coeff index (PowerSeries.coeff degree theta) =
      -PowerSeries.coeff index (PowerSeries.coeff degree theta) at hcoefficient
    rw [mul_assoc, ← map_mul, hcoefficient, map_neg]
    ring
  have hu {R : Type} [CommRing R] (first second : R) :
      splitDouble (R := R)
          (PowerSeries.C (R := PowerSeries (TrivSqZeroExt R R))
            (PowerSeries.X (R := TrivSqZeroExt R R) *
              PowerSeries.C (R := TrivSqZeroExt R R) (first, second))) =
        ((PowerSeries.C (PowerSeries.X * PowerSeries.C first),
          PowerSeries.C (PowerSeries.X * PowerSeries.C second)) :
          TrivSqZeroExt (PowerSeries (PowerSeries R)) (PowerSeries (PowerSeries R))) := by
    have hinner (index : ℕ) :
        PowerSeries.coeff (R := TrivSqZeroExt R R) index (PowerSeries.X *
          PowerSeries.C (R := TrivSqZeroExt R R) (first, second)) =
        if index = 1 then ((first, second) : TrivSqZeroExt R R) else 0 := by
      rw [PowerSeries.coeff_mul_C, PowerSeries.coeff_X]
      split_ifs <;> simp only [one_mul, zero_mul]
    have hinnerFirst (index : ℕ) :
        (PowerSeries.coeff (R := TrivSqZeroExt R R) index (PowerSeries.X *
          PowerSeries.C (R := TrivSqZeroExt R R) (first, second))).fst =
        PowerSeries.coeff index (PowerSeries.X * PowerSeries.C first) := by
      rw [hinner, PowerSeries.coeff_mul_C, PowerSeries.coeff_X]
      split_ifs <;> simp only [TrivSqZeroExt.fst_mk, TrivSqZeroExt.fst_zero,
        one_mul, zero_mul]
    have hinnerSecond (index : ℕ) :
        (PowerSeries.coeff (R := TrivSqZeroExt R R) index (PowerSeries.X *
          PowerSeries.C (R := TrivSqZeroExt R R) (first, second))).snd =
        PowerSeries.coeff index (PowerSeries.X * PowerSeries.C second) := by
      rw [hinner, PowerSeries.coeff_mul_C, PowerSeries.coeff_X]
      split_ifs <;> simp only [TrivSqZeroExt.snd_mk, TrivSqZeroExt.snd_zero,
        one_mul, zero_mul]
    rw [hsplit (R := R)]
    apply TrivSqZeroExt.ext <;> apply PowerSeries.ext <;> intro degree <;>
      apply PowerSeries.ext <;> intro index <;> by_cases hdegree : degree = 0 <;>
        simp only [TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk, PowerSeries.coeff_mk,
          PowerSeries.coeff_C, hdegree, if_true, if_false, hinnerFirst,
          hinnerSecond, map_zero, TrivSqZeroExt.fst_zero, TrivSqZeroExt.snd_zero]
  have hpairAdd {R : Type} [CommRing R] (first second third fourth : R) :
      ((first, second) : TrivSqZeroExt R R) +
          ((third, fourth) : TrivSqZeroExt R R) =
        ((first + third, second + fourth) : TrivSqZeroExt R R) := rfl
  have hpairSub {R : Type} [CommRing R] (first second third fourth : R) :
      ((first, second) : TrivSqZeroExt R R) -
          ((third, fourth) : TrivSqZeroExt R R) =
        ((first - third, second - fourth) : TrivSqZeroExt R R) := rfl
  have hpairNeg {R : Type} [CommRing R] (first second : R) :
      -((first, second) : TrivSqZeroExt R R) =
        ((-first, -second) : TrivSqZeroExt R R) := rfl
  have hwronskian {R : Type} [CommRing R] [Algebra ℚ R] (first second : R) :
      jet 1 (0 : R) ^ 2 * jet 0 (first + second) * jet 0 (first - second) =
        (jet 0 first * jet 2 first - jet 1 first ^ 2) * jet 0 second ^ 2 -
          jet 0 first ^ 2 * (jet 0 second * jet 2 second - jet 1 second ^ 2) := by
    let firstLift : TrivSqZeroExt (TrivSqZeroExt R R) (TrivSqZeroExt R R) :=
      (((first, 0) : TrivSqZeroExt R R), 0)
    let secondLift : TrivSqZeroExt (TrivSqZeroExt R R) (TrivSqZeroExt R R) :=
      (((second, 0) : TrivSqZeroExt R R), 0)
    let perturbation : TrivSqZeroExt (TrivSqZeroExt R R) (TrivSqZeroExt R R) :=
      (((0, 1) : TrivSqZeroExt R R), ((1, 0) : TrivSqZeroExt R R))
    have hadd := theta_exponential_addition
      (R := TrivSqZeroExt (TrivSqZeroExt R R) (TrivSqZeroExt R R))
      firstLift secondLift 0 perturbation
    simp only [zero_add, add_zero, sub_zero, zero_sub] at hadd
    simp only [hscale (R := TrivSqZeroExt (TrivSqZeroExt R R)
      (TrivSqZeroExt R R))] at hadd
    simp only [firstLift, secondLift, perturbation, hpairAdd, hpairSub, hpairNeg,
      add_zero, zero_add, sub_zero, zero_sub, neg_zero] at hadd
    have hfirst := congrArg
      (fun series => (splitDouble (R := TrivSqZeroExt R R) series).snd) hadd
    simp only [hsplitSub (R := TrivSqZeroExt R R), hsplitMul (R := TrivSqZeroExt R R),
      hjet (R := TrivSqZeroExt R R), TrivSqZeroExt.snd_sub,
      TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_mk,
      TrivSqZeroExt.snd_mk, smul_eq_mul, op_smul_eq_smul, map_zero,
      zero_mul, mul_zero, add_zero, zero_add] at hfirst
    have hsecond := congrArg (fun series => (splitDouble (R := R) series).snd) hfirst
    simp only [hsplitSub (R := R), hsplitMul (R := R), hsplitAdd (R := R),
      hjet (R := R), hu (R := R), TrivSqZeroExt.snd_sub,
      TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_add,
      TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk,
      smul_eq_mul, op_smul_eq_smul, hzero, hodd, add_zero, zero_add, mul_zero, zero_mul,
      map_zero, map_neg, map_one, mul_one, neg_mul, mul_neg] at hsecond
    let left := jet 1 (0 : R) ^ 2 * jet 0 (first + second) * jet 0 (first - second)
    let right := (jet 0 first * jet 2 first - jet 1 first ^ 2) * jet 0 second ^ 2 -
      jet 0 first ^ 2 * (jet 0 second * jet 2 second - jet 1 second ^ 2)
    have hpadded : PowerSeries.C (PowerSeries.X ^ 2) * (2 * (left - right)) = 0 := by
      dsimp only [left, right]
      rw [map_pow]
      linear_combination -hsecond
    have hequal : 2 * (left - right) = 0 := by
      apply PowerSeries.ext
      intro degree
      apply PowerSeries.X_pow_mul_cancel (k := 2)
      have hcoefficient := congrArg (PowerSeries.coeff degree) hpadded
      simpa only [PowerSeries.coeff_C_mul, map_zero, mul_zero] using hcoefficient
    have htwoBase : (2 : R) * algebraMap ℚ R (1 / 2) = 1 := by
      have hbase := congrArg (algebraMap ℚ R) (show (2 : ℚ) * (1 / 2) = 1 by norm_num)
      simpa only [map_mul, map_ofNat, map_one] using hbase
    have htwo : (2 : PowerSeries (PowerSeries R)) *
        PowerSeries.C (PowerSeries.C (algebraMap ℚ R (1 / 2))) = 1 := by
      change PowerSeries.C (PowerSeries.C (2 : R)) *
        PowerSeries.C (PowerSeries.C (algebraMap ℚ R (1 / 2))) = 1
      rw [← map_mul, ← map_mul, htwoBase, map_one, map_one]
    have hdifference : left - right = 0 := by
      calc
        left - right = (2 * (left - right)) *
            PowerSeries.C (PowerSeries.C (algebraMap ℚ R (1 / 2))) := by
              rw [show 2 * (left - right) *
                  PowerSeries.C (PowerSeries.C (algebraMap ℚ R (1 / 2))) =
                  (left - right) * (2 *
                    PowerSeries.C (PowerSeries.C (algebraMap ℚ R (1 / 2)))) by ring,
                htwo, mul_one]
        _ = 0 := by rw [hequal, zero_mul]
    exact sub_eq_zero.mp hdifference
  have hduplication := hwronskian (R := TrivSqZeroExt ℚ ℚ)
    ((1, 0) : TrivSqZeroExt ℚ ℚ)
    ((1, 1) : TrivSqZeroExt ℚ ℚ)
  norm_num only [hpairAdd, hpairSub] at hduplication
  have hzeroDual : (0 : TrivSqZeroExt ℚ ℚ) = ((0, 0) : TrivSqZeroExt ℚ ℚ) := rfl
  rw [hzeroDual] at hduplication
  have hfirst := congrArg (fun series => (splitDouble (R := ℚ) series).snd) hduplication
  simp only [hsplitMul (R := ℚ), hsplitSub (R := ℚ), hsplitPow (R := ℚ),
    hjet (R := ℚ), TrivSqZeroExt.snd_mul,
    TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_sub, TrivSqZeroExt.fst_sub,
    TrivSqZeroExt.fst_pow, TrivSqZeroExt.snd_pow, TrivSqZeroExt.fst_mk,
    TrivSqZeroExt.snd_mk, hzero, smul_eq_mul, op_smul_eq_smul, map_zero,
    map_one, map_neg, zero_mul, mul_zero, add_zero, zero_add, mul_one,
    neg_mul, mul_neg, nsmul_eq_mul, Nat.pred_succ, pow_one,
    Nat.cast_ofNat] at hfirst
  have hone (order : ℕ) : jet order (1 : ℚ) = derivative^[order] theta := by
    apply PowerSeries.ext
    intro degree
    apply PowerSeries.ext
    intro index
    simp [jet]
  let linear := -PowerSeries.pentagonalSeries ℚ ^ 2
  have hlinear : jet 1 (0 : ℚ) = PowerSeries.map PowerSeries.C linear := by
    have hnormalized := (theta_exponential_normalization (1 : ℚ)).2.2.1
    have hnormalizedCoeff (degree : ℕ) :
        PowerSeries.coeff 1 (PowerSeries.coeff degree theta) =
          PowerSeries.coeff degree linear := by
      have hcoefficient := congrArg (PowerSeries.coeff degree) hnormalized
      simpa [linear, theta] using hcoefficient
    apply PowerSeries.ext
    intro degree
    apply PowerSeries.ext
    intro index
    rw [hcoeff, PowerSeries.coeff_map, PowerSeries.coeff_C]
    cases index with
    | zero => simp [derivative, PowerSeries.coeff_derivative, hnormalizedCoeff]
    | succ index => simp
  have hpadded : PowerSeries.C PowerSeries.X *
      (derivative (derivative (derivative theta)) * theta ^ 3 -
          3 * derivative (derivative theta) * derivative theta * theta ^ 2 +
          2 * derivative theta ^ 3 * theta -
        PowerSeries.map PowerSeries.C (linear ^ 3) * normalizedTheta (2 : ℚ)) = 0 := by
    simp only [hone, Function.iterate_zero, id_eq, Function.iterate_succ_apply',
      ← hscale, hlinear] at hfirst
    rw [map_pow]
    linear_combination hfirst
  change derivative (derivative (derivative theta)) * theta ^ 3 -
      3 * derivative (derivative theta) * derivative theta * theta ^ 2 +
      2 * derivative theta ^ 3 * theta =
    PowerSeries.map PowerSeries.C (linear ^ 3) * normalizedTheta (2 : ℚ)
  apply sub_eq_zero.mp
  apply PowerSeries.ext
  intro degree
  apply PowerSeries.X_mul_cancel
  have hcoefficient := congrArg (PowerSeries.coeff degree) hpadded
  simpa only [PowerSeries.coeff_C_mul, map_zero, mul_zero] using hcoefficient

end D5.S3.Combinatorics.InversionSeq.InversionSeq207ThetaDifferential
