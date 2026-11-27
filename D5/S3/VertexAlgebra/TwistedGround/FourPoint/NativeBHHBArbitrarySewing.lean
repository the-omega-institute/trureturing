/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeBHHBArbitrarySewing
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal upper BHHB crossing for arbitrary actual Leech twisted states. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHBHBArbitrarySewing
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBHHBUpperCrossing

/-! The HHBB projected basis supplies the marked states. The mode maps evaluate
them in paper order `(w,u,v,b)`. A finite lowering exponential acts on the
detector in the marked theorem and is removed by triangular subtraction. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators Finset TensorProduct Topology VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBHHBArbitrarySewing

open Complex (I)
open ActualLeechHyperbolic (leechData)
open LatticeHalfFockChargedTensorCoefficients (ActualGround)
open LatticeHalfFockCorrectedField (correctedField)
open LatticeHalfFockGradedTrace (actual_basis_apply oddWeight)
open Orbifold.NativeOddTwistedIntertwiner (Twisted TwistedEven TwistedOdd leechUnit)
open Orbifold.NativeOddUpperRightSkew (lowering)
open Orbifold.NativeFixedPairField (nu)
open Orbifold.NativeFixedUpperRightSkew (rightField)
open Orbifold.NativeMixedPairField (mu)
open OriginalFourMActualChart (Puncture)
open OriginalFourMVariableSupport (wordAt)
open NativeFourHHomogeneousExtension (occupation_monomials_have_marked_words)
open NativeMixedWickChartTransport (MixedParity doubledOccupation)
open NativeMixedAIterateRadial (aJointTerm)
open NativeFixedCrossedProductToIterate (dJointTerm translatedDetector translationWeight)
open NativeBHHBUpperCrossing (bJointTerm bhhb_marked_upper_crossing)

open private BasisIndex ambientBasis coeffAt HSpace from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHHomogeneousExtension
open private BasisQuad HHBBLinear BSpace pairWithB project_basis_val component component_eq_zero
  basisTuples onComponents expand from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedArbitrarySewing
open private detectorExp detectorExp_apply component_lowering_tail from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHBHBArbitrarySewing
open private sum_projectedBasis from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairField

local notation "ℒ" => leechData
local notation "L₁" => lowering ℒ leechUnit true

private def aMode (E : Module.End ℂ TwistedOdd) (y : ℂ) (i : ℤ × ℤ) : HHBBLinear :=
  let inner := ((coeffAt i.1).comp (mu true)).flip
  let outer := ((coeffAt i.2).comp (correctedField ℒ leechUnit)).compl₁₂
    (LatticeInvolution.minusSpace ℒ).subtype HSpace.subtype
  let swap : (TwistedOdd →ₗ[ℂ] TwistedEven →ₗ[ℂ] TwistedOdd →ₗ[ℂ] ℂ) →ₗ[ℂ]
      TwistedEven →ₗ[ℂ] TwistedOdd →ₗ[ℂ] TwistedOdd →ₗ[ℂ] ℂ :=
    LinearMap.lflip.toLinearMap
  (I ^ i.1 * (-Complex.sqrt (1 - y)) ^ i.2) •
    swap.comp (inner.compr₂ (outer.compr₂ (pairWithB.compl₂ E)))

private def bMode (E : Module.End ℂ TwistedOdd) (y : ℂ) (i : ℤ × ℤ) : HHBBLinear :=
  let inner := (coeffAt i.1).comp (nu false)
  let outer := ((coeffAt i.2).comp (rightField ℒ leechUnit true)).flip
  ((-Complex.sqrt (1 - y)) ^ i.1 * (I * Complex.sqrt y) ^ i.2) •
    inner.compr₂ (outer.compr₂ ((pairWithB.compl₂ E).comp BSpace.subtype))

set_option maxHeartbeats 4000000 in
private theorem aMode_apply (E : Module.End ℂ TwistedOdd) (y : ℂ) (i : ℤ × ℤ)
    (u v : TwistedEven) (w b : TwistedOdd) :
    aMode E y i u v w b = aJointTerm true w u v.val (E b).val I (-Complex.sqrt (1 - y)) i :=
  mul_comm _ _

set_option maxHeartbeats 4000000 in
private theorem bMode_apply (E : Module.End ℂ TwistedOdd) (y : ℂ) (i : ℤ × ℤ)
    (u v : TwistedEven) (w b : TwistedOdd) :
    bMode E y i u v w b = bJointTerm w u v (E b) (I * Complex.sqrt y)
      (-Complex.sqrt (1 - y)) i := by
  unfold bJointTerm dJointTerm
  exact mul_comm _ _

set_option maxHeartbeats 4000000 in
private theorem component_crossing (u v : TwistedEven) (w b : TwistedOdd) (i : BasisQuad)
    {y : ℂ} (him : 0 < y.im) (hre : (1 / 2 : ℝ) < y.re)
    (hnorm : 1 < ‖y‖) (hcomp : 1 < ‖1 - y‖) (k : ℕ)
    (hk : oddWeight ℒ i.2.2.2.1 / 2 + 1 ≤ k) :
    let A := fun p => onComponents u v w b (aMode (detectorExp y k) y p) i
    let B := fun p => onComponents u v w b (bMode (detectorExp y k) y p) i
    HasSum A (∑' p, A p) ∧ HasSum B (-(∑' p, A p)) := by
  classical
  let A := fun p => onComponents u v w b (aMode (detectorExp y k) y p) i
  let B := fun p => onComponents u v w b (bMode (detectorExp y k) y p) i
  change HasSum A (∑' p, A p) ∧ HasSum B (-(∑' p, A p))
  let u' := component false u i.1
  let v' := component false v i.2.1
  let w' := component true w i.2.2.1
  let b' := component true b i.2.2.2
  let d : Puncture → BasisIndex
    | .P => i.1
    | .Q => i.2.1
    | .R => i.2.2.1
    | .S => i.2.2.2
  let odd : Puncture → Bool
    | .P => false
    | .Q => false
    | .R => true
    | .S => true
  have hsum : ∃ C, HasSum A C ∧ HasSum B (-C) := by
    by_cases h : ∀ t, oddWeight ℒ (d t).1 % 2 = (if odd t then 1 else 0)
    swap
    · obtain ⟨t, ht⟩ := not_forall.mp h
      have hzero (F : HHBBLinear) : F u' v' w' b' = 0 := by
        cases t with
        | P => simp [show u' = 0 from component_eq_zero false u i.1 ht]
        | Q => simp [show v' = 0 from component_eq_zero false v i.2.1 ht]
        | R => simp [show w' = 0 from component_eq_zero true w i.2.2.1 ht]
        | S => simp [show b' = 0 from component_eq_zero true b i.2.2.2 ht]
      have hz : HasSum (fun _ : ℤ × ℤ => (0 : ℂ)) 0 := hasSum_zero
      refine ⟨0, hz.congr_fun (fun p => hzero (aMode (detectorExp y k) y p)), ?_⟩
      rw [neg_zero]
      exact hz.congr_fun (fun p => hzero (bMode (detectorExp y k) y p))
    obtain ⟨m, slot, colour, n, hmarks⟩ :=
      occupation_monomials_have_marked_words (fun t => (d t).1)
    let l := List.finRange m
    let W := wordAt ℒ slot colour n l
    have hweight (t : Puncture) :
        doubledOccupation slot n l t % 2 = ((if odd t then 1 else 0 : ℕ) : ℤ) := by
      rw [(hmarks t).2]
      exact_mod_cast h t
    have hpar : MixedParity slot n l := ⟨hweight .P, hweight .Q, hweight .R, hweight .S⟩
    let ground (s : Bool) (a : Twisted ℒ leechUnit s) (t : Puncture) :
        ActualGround ℒ leechUnit :=
      ambientBasis.repr a.val (d t) • Pi.single (d t).2 (1 : ℂ)
    have hword (s : Bool) (a : Twisted ℒ leechUnit s) (t : Puncture) (ht : odd t = s) :
        (component s a (d t)).val = W t ⊗ₜ[ℂ] ground s a t := by
      have hp := h t
      rw [ht] at hp
      rw [component, Submodule.coe_smul, project_basis_val, ite_eq_left hp,
        actual_basis_apply ℒ leechUnit (d t).1 (d t).2]
      change ambientBasis.repr a.val (d t) •
          (MvPolynomial.monomial (d t).1 (1 : ℂ) ⊗ₜ[ℂ] Pi.single (d t).2 (1 : ℂ)) =
        W t ⊗ₜ[ℂ] (ambientBasis.repr a.val (d t) • Pi.single (d t).2 (1 : ℂ))
      have hW : W t = MvPolynomial.monomial (d t).1 (1 : ℂ) := (hmarks t).1
      rw [TensorProduct.tmul_smul, hW]
    let N := (doubledOccupation slot n l .S).toNat
    have hN : N = oddWeight ℒ i.2.2.2.1 := congrArg Int.toNat (hmarks .S).2
    -- A common cutoff pads the marked translation with vanishing lowering powers.
    have hdetector : detectorExp y k b' = translatedDetector true N y b' := by
      rw [detectorExp_apply, translatedDetector]
      simp only [translationWeight, div_eq_mul_inv]
      symm
      refine Finset.sum_subset (Finset.range_mono (by simpa only [hN] using hk)) ?_
      intro j _ hj
      have htail : oddWeight ℒ i.2.2.2.1 / 2 + 1 ≤ j := by
        rw [← hN]
        exact Nat.le_of_not_gt (fun hlt => hj (Finset.mem_range.mpr hlt))
      rw [show (L₁ ^ j) b' = 0 from component_lowering_tail b i.2.2.2 j htail, smul_zero]
    let detector := translatedDetector true N y b'
    let markedA := aJointTerm true w' u' v'.val detector.val I (-Complex.sqrt (1 - y))
    let markedB := bJointTerm w' u' v' detector (I * Complex.sqrt y) (-Complex.sqrt (1 - y))
    have hmarked : HasSum markedA (∑' p, markedA p) ∧ HasSum markedB (-(∑' p, markedA p)) :=
      bhhb_marked_upper_crossing slot colour n l (List.nodup_finRange m) hpar
        u' v' w' b' (ground false u .P) (ground false v .Q) (ground true w .R) (ground true b .S)
        (hword false u .P rfl) (hword false v .Q rfl) (hword true w .R rfl) (hword true b .S rfl)
        (y := y) him hnorm hre hcomp
    have ha : A = markedA := by
      funext p
      change aMode (detectorExp y k) y p u' v' w' b' = markedA p
      rw [aMode_apply, hdetector]
    have hb : B = markedB := by
      funext p
      change bMode (detectorExp y k) y p u' v' w' b' = markedB p
      rw [bMode_apply, hdetector]
    rw [ha, hb]
    exact ⟨_, hmarked.1, hmarked.2⟩
  obtain ⟨C, ha, hb⟩ := hsum
  rw [ha.tsum_eq]
  exact ⟨ha, hb⟩

/-- Detectors for which the literal A and B series have opposite sums. -/
private def crossingDetectors (u v : TwistedEven) (w : TwistedOdd) (y : ℂ) :
    Submodule ℂ TwistedOdd where
  carrier := {b | ∃ C,
    HasSum (fun i => aMode LinearMap.id y i u v w b) C ∧
    HasSum (fun i => bMode LinearMap.id y i u v w b) (-C)}
  zero_mem' := by
    refine ⟨0, ?_, ?_⟩ <;> simpa only [map_zero, neg_zero] using
      (hasSum_zero : HasSum (fun _ : ℤ × ℤ => (0 : ℂ)) 0)
  add_mem' := by
    rintro b d ⟨C, ha, hb⟩ ⟨D, ha', hb'⟩
    refine ⟨C + D, ?_, ?_⟩
    · simpa only [map_add, Pi.add_apply] using ha.add ha'
    · simpa only [map_add, Pi.add_apply, neg_add] using hb.add hb'
  smul_mem' := by
    rintro c b ⟨C, ha, hb⟩
    refine ⟨c * C, ?_, ?_⟩
    · simpa only [map_smul, smul_eq_mul] using ha.mul_left c
    · simpa only [map_smul, smul_eq_mul, mul_neg] using hb.mul_left c

set_option maxHeartbeats 4000000 in
private theorem translated_crossing (u v : TwistedEven) (w b : TwistedOdd)
    {y : ℂ} (him : 0 < y.im) (hre : (1 / 2 : ℝ) < y.re)
    (hnorm : 1 < ‖y‖) (hcomp : 1 < ‖1 - y‖) :
    ∃ k : ℕ, (L₁ ^ k) b = 0 ∧ detectorExp y (k + 1) b ∈ crossingDetectors u v w y := by
  classical
  let support := (ambientBasis.repr b.val).support
  let bound (i : BasisIndex) := oddWeight ℒ i.1 / 2 + 1
  let k := support.sup bound
  have hcut (i : BasisIndex) (hi : i ∈ support) : bound i ≤ k := Finset.le_sup hi
  refine ⟨k, ?_, ?_⟩
  · calc
      (L₁ ^ k) b = (L₁ ^ k) (∑ i ∈ support, component true b i) :=
        congrArg (fun d : TwistedOdd => (L₁ ^ k) d) (sum_projectedBasis true b).symm
      _ = 0 := by
        rw [map_sum]
        exact Finset.sum_eq_zero (fun i hi => component_lowering_tail b i k (hcut i hi))
  · let E := detectorExp y (k + 1)
    change (∃ C, HasSum (fun p => aMode LinearMap.id y p u v w (E b)) C ∧
      HasSum (fun p => bMode LinearMap.id y p u v w (E b)) (-C))
    let value (i : BasisQuad) := ∑' p, onComponents u v w b (aMode E y p) i
    have hcomponent (i : BasisQuad) (hi : i ∈ basisTuples u v w b) :
        HasSum (fun p => onComponents u v w b (aMode E y p) i) (value i) ∧
        HasSum (fun p => onComponents u v w b (bMode E y p) i) (-value i) := by
      simp only [basisTuples, Finset.mem_product] at hi
      exact component_crossing u v w b i him hre hnorm hcomp (k + 1)
        ((hcut i.2.2.2 hi.2.2.2).trans (Nat.le_succ k))
    refine ⟨∑ i ∈ basisTuples u v w b, value i, ?_, ?_⟩
    · refine (hasSum_sum (s := basisTuples u v w b) fun i hi => (hcomponent i hi).1).congr_fun ?_
      intro p
      simpa only [aMode_apply, LinearMap.id_apply] using expand u v w b (aMode E y p)
    · rw [← Finset.sum_neg_distrib]
      refine (hasSum_sum (s := basisTuples u v w b) fun i hi => (hcomponent i hi).2).congr_fun ?_
      intro p
      simpa only [bMode_apply, LinearMap.id_apply] using expand u v w b (bMode E y p)

set_option maxHeartbeats 4000000 in
private theorem crossing_of_lowering_power (u v : TwistedEven) (w b : TwistedOdd)
    {y : ℂ} (him : 0 < y.im) (hre : (1 / 2 : ℝ) < y.re)
    (hnorm : 1 < ‖y‖) (hcomp : 1 < ‖1 - y‖)
    (n : ℕ) (hnil : (L₁ ^ n) b = 0) : b ∈ crossingDetectors u v w y := by
  induction n generalizing b with
  | zero =>
      have hzero : b = 0 := by simpa only [pow_zero, Module.End.one_apply] using hnil
      rw [hzero]
      exact (crossingDetectors u v w y).zero_mem
  | succ n ih =>
      obtain ⟨k, _, htranslated⟩ := translated_crossing u v w b him hre hnorm hcomp
      let term (j : ℕ) := (y ^ j / (j.factorial : ℂ)) • (L₁ ^ j) b
      have htail : (∑ j ∈ Finset.range k, term (j + 1)) ∈ crossingDetectors u v w y := by
        refine Submodule.sum_mem _ fun j _ => (crossingDetectors u v w y).smul_mem _ (ih _ ?_)
        rw [← Module.End.mul_apply, ← pow_add,
          show n + (j + 1) = j + n.succ by omega, pow_add, Module.End.mul_apply, hnil, map_zero]
      have hsplit : detectorExp y (k + 1) b = b + ∑ j ∈ Finset.range k, term (j + 1) := by
        rw [detectorExp_apply]
        change (∑ j ∈ Finset.range (k + 1), term j) = _
        rw [Finset.sum_range_succ']
        have hzero : term 0 = b := by
          simp only [term, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
            Module.End.one_apply, one_smul]
        rw [hzero, add_comm]
      rw [hsplit] at htranslated
      simpa only [add_sub_cancel_right] using (crossingDetectors u v w y).sub_mem htranslated htail

set_option maxHeartbeats 4000000 in
/-- In paper order `(w,u,v,b)`, the actual BHHB iterate and fixed product have
opposite literal double-mode sums at the upper roots `I * sqrt y`,
`-sqrt (1 - y)` and separation root `I`. -/
theorem bhhb_actual_complex_sewing_of_states (w : TwistedOdd) (u v : TwistedEven)
    (b : TwistedOdd) {y : ℂ} (him : 0 < y.im) (hre : (1 / 2 : ℝ) < y.re)
    (hnorm : 1 < ‖y‖) (hcomp : 1 < ‖1 - y‖) :
    let A := aJointTerm true w u v.val b.val I (-Complex.sqrt (1 - y))
    let B := bJointTerm w u v b (I * Complex.sqrt y) (-Complex.sqrt (1 - y))
    HasSum A (∑' i : ℤ × ℤ, A i) ∧ HasSum B (-(∑' i : ℤ × ℤ, A i)) := by
  obtain ⟨n, hnil, _⟩ := translated_crossing u v w b him hre hnorm hcomp
  have h := crossing_of_lowering_power u v w b him hre hnorm hcomp n hnil
  change (∃ C, HasSum (fun i => aMode LinearMap.id y i u v w b) C ∧
    HasSum (fun i => bMode LinearMap.id y i u v w b) (-C)) at h
  let A := aJointTerm true w u v.val b.val I (-Complex.sqrt (1 - y))
  let B := bJointTerm w u v b (I * Complex.sqrt y) (-Complex.sqrt (1 - y))
  obtain ⟨C, ha, hb⟩ : ∃ C, HasSum A C ∧ HasSum B (-C) := by
    simpa only [A, B, aMode_apply, bMode_apply, LinearMap.id_apply] using h
  change HasSum A (∑' i, A i) ∧ HasSum B (-(∑' i, A i))
  rw [ha.tsum_eq]
  exact ⟨ha, hb⟩

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBHHBArbitrarySewing
