/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeHBHBArbitrarySewing
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal upper HBHB crossing for arbitrary actual Leech twisted states. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHBHBUpperCrossing

/-! Finite projected-basis expansion extends marked HBHB crossing to arbitrary
states. Local nilpotence removes the detector translation on the overlap. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators Finset TensorProduct Topology VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHBHBArbitrarySewing

open ActualLeechHyperbolic (leechData)
open ActualChargedAdjoint (actualForm)
open LatticeHalfFockChargedTensorCoefficients (ActualGround)
open LatticeHalfFockCorrectedField (correctedField)
open LatticeHalfFockGradedTrace (actualGrade actual_basis_apply oddWeight)
open Orbifold.NativeOddTwistedIntertwiner (Twisted TwistedEven TwistedOdd leechUnit)
open Orbifold.NativeFullMixedField (project)
open Orbifold.NativeMixedPairField (mu)
open Orbifold.NativeMixedPairSkew (swapInput)
open Orbifold.NativeOddUpperRightSkew (lowering mixedPairing_lowering_tail)
open OriginalFourMActualChart (Puncture)
open OriginalFourMVariableSupport (wordAt)
open NativeFourHHomogeneousExtension (occupation_monomials_have_marked_words)
open NativeMixedWickChartTransport (MixedParity doubledOccupation)
open NativeMixedAIterateRadial (aJointTerm)
open NativeMixedUpperProductCusp (bJointTerm)
open NativeHBHBUpperCrossing (hbhb_marked_upper_crossing upperTransportDomain)

open private BasisIndex ambientBasis basis_mem_grade coeffAt HSpace from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHHomogeneousExtension
open private BasisQuad HHBBLinear BSpace pairWithB oddRightCoeff oddRightCoeff_apply
  project_basis_val component component_eq_zero basisTuples onComponents expand from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedArbitrarySewing
open private sum_projectedBasis from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairField

local notation "ℒ" => leechData
local notation "L₁" => lowering ℒ leechUnit true

private def aMode (E : Module.End ℂ TwistedOdd) (y : ℂ) (i : ℤ × ℤ) : HHBBLinear :=
  let inner := (coeffAt i.1).comp (mu false)
  let outer := ((coeffAt i.2).comp (correctedField ℒ leechUnit)).compl₁₂
    (LatticeInvolution.minusSpace ℒ).subtype HSpace.subtype
  let swap : (TwistedOdd →ₗ[ℂ] TwistedEven →ₗ[ℂ] TwistedOdd →ₗ[ℂ] ℂ) →ₗ[ℂ]
      TwistedEven →ₗ[ℂ] TwistedOdd →ₗ[ℂ] TwistedOdd →ₗ[ℂ] ℂ :=
    LinearMap.lflip.toLinearMap
  ((1 : ℂ) ^ i.1 * (Complex.I * Complex.sqrt y) ^ i.2) •
    swap.comp (inner.compr₂ (outer.compr₂ (pairWithB.compl₂ E)))

private def bMode (E : Module.End ℂ TwistedOdd) (y : ℂ) (i : ℤ × ℤ) : HHBBLinear :=
  let inner := ((coeffAt i.1).comp (mu true)).flip
  let outer := (oddRightCoeff false i.2).flip
  let product := inner.compr₂ (outer.compr₂ ((pairWithB.compl₂ E).comp BSpace.subtype))
  let swap : (TwistedOdd →ₗ[ℂ] TwistedEven →ₗ[ℂ] TwistedOdd →ₗ[ℂ] ℂ) →ₗ[ℂ]
      TwistedEven →ₗ[ℂ] TwistedOdd →ₗ[ℂ] TwistedOdd →ₗ[ℂ] ℂ :=
    LinearMap.lflip.toLinearMap
  ((Complex.I * Complex.sqrt y) ^ i.1 * (Complex.sqrt (1 - y)) ^ i.2) •
    (swap.comp product).flip

set_option maxHeartbeats 4000000 in
-- Unfolds the restricted coefficient and the curried maps.
private theorem aMode_apply (E : Module.End ℂ TwistedOdd) (y : ℂ) (i : ℤ × ℤ)
    (u v : TwistedEven) (w b : TwistedOdd) :
    aMode E y i u v w b = aJointTerm false u w v.val (E b).val 1
      (Complex.I * Complex.sqrt y) i :=
  mul_comm _ _

set_option maxHeartbeats 4000000 in
-- Unfolds the coefficient of the odd right-skew field.
private theorem bMode_apply (E : Module.End ℂ TwistedOdd) (y : ℂ) (i : ℤ × ℤ)
    (u v : TwistedEven) (w b : TwistedOdd) :
    bMode E y i u v w b = bJointTerm true false w (swapInput (s := false) v) u (E b)
      (Complex.sqrt (1 - y)) (Complex.I * Complex.sqrt y) i := by
  have hswap : swapInput (s := false) v = v := Subtype.ext rfl
  rw [hswap]
  change ((Complex.I * Complex.sqrt y) ^ i.1 * (Complex.sqrt (1 - y)) ^ i.2) *
    actualForm ℒ leechUnit (E b).val (oddRightCoeff false i.2 u ((mu true w).coeff i.1 v)).val = _
  rw [oddRightCoeff_apply]
  exact mul_comm _ _

private def detectorExp (y : ℂ) (k : ℕ) : Module.End ℂ TwistedOdd :=
  ∑ j ∈ Finset.range k, (y ^ j / (j.factorial : ℂ)) • (L₁ ^ j)

private theorem detectorExp_apply (y : ℂ) (k : ℕ) (b : TwistedOdd) :
    detectorExp y k b =
      ∑ j ∈ Finset.range k, (y ^ j / (j.factorial : ℂ)) • (L₁ ^ j) b := by
  simp only [detectorExp, LinearMap.sum_apply, LinearMap.smul_apply]

private theorem component_lowering_tail (b : TwistedOdd) (i : BasisIndex) (j : ℕ)
    (hj : oddWeight ℒ i.1 / 2 + 1 ≤ j) : (L₁ ^ j) (component true b i) = 0 := by
  by_cases hi : oddWeight ℒ i.1 % 2 = 1
  · have hgrade : (component true b i).val ∈ actualGrade ℒ leechUnit (oddWeight ℒ i.1) := by
      have hp : (project true (ambientBasis i)).val = ambientBasis i := by
        rw [project_basis_val, ite_eq_left (show oddWeight ℒ i.1 % 2 =
          (if true then 1 else 0) from hi)]
      rw [component, Submodule.coe_smul, hp]
      exact (actualGrade ℒ leechUnit (oddWeight ℒ i.1)).smul_mem _ (basis_mem_grade i)
    exact mixedPairing_lowering_tail true _ _ hgrade j hj
  · rw [component_eq_zero true b i hi, map_zero]

set_option maxHeartbeats 4000000 in
-- Matches the marked series to both curried mode maps on each basis tuple.
private theorem component_crossing (u v : TwistedEven) (w b : TwistedOdd) (i : BasisQuad)
    {y : ℂ} (hy : y ∈ upperTransportDomain) (hnorm : 1 < ‖y‖) (k : ℕ)
    (hk : oddWeight ℒ i.2.2.2.1 / 2 + 1 ≤ k) :
    let A := fun p => onComponents u v w b (aMode (detectorExp y k) y p) i
    let B := fun p => onComponents u v w b (bMode (detectorExp y k) y p) i
    HasSum A (∑' p, B p) ∧ HasSum B (∑' p, B p) := by
  classical
  let A := fun p => onComponents u v w b (aMode (detectorExp y k) y p) i
  let B := fun p => onComponents u v w b (bMode (detectorExp y k) y p) i
  change HasSum A (∑' p, B p) ∧ HasSum B (∑' p, B p)
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
  have hsum : ∃ C, HasSum A C ∧ HasSum B C := by
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
      exact ⟨0, hz.congr_fun (fun p => hzero (aMode (detectorExp y k) y p)),
        hz.congr_fun (fun p => hzero (bMode (detectorExp y k) y p))⟩
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
    -- Every term added to the marked cutoff vanishes in the detector slot.
    have hexp (F : HHBBLinear) :
        F u' v' w' (detectorExp y k b') =
          ∑ j ∈ Finset.range (N / 2 + 1),
            (y ^ j / (j.factorial : ℂ)) * F u' v' w' ((L₁ ^ j) b') := by
      rw [detectorExp_apply, map_sum]
      simp only [map_smul, smul_eq_mul]
      symm
      refine Finset.sum_subset (Finset.range_mono (by simpa only [hN] using hk)) ?_
      intro j _ hj
      have htail : oddWeight ℒ i.2.2.2.1 / 2 + 1 ≤ j := by
        rw [← hN]
        exact Nat.le_of_not_gt (fun hlt => hj (Finset.mem_range.mpr hlt))
      have hz : (L₁ ^ j) b' = 0 := component_lowering_tail b i.2.2.2 j htail
      rw [hz, map_zero, mul_zero]
    have hmarked := hbhb_marked_upper_crossing slot colour n l (List.nodup_finRange m) hpar
      u' v' w' b' (ground false u .P) (ground false v .Q) (ground true w .R) (ground true b .S)
      (hword false u .P rfl) (hword false v .Q rfl) (hword true w .R rfl) (hword true b .S rfl)
    have hphysical := hmarked.2.2 y hy hnorm
    refine ⟨_, hphysical.2.2.1.congr_fun ?_, hphysical.2.2.2.congr_fun ?_⟩
    · intro p
      simpa only [A, onComponents, aMode_apply, LinearMap.id_apply] using
        hexp (aMode LinearMap.id y p)
    · intro p
      simpa only [B, onComponents, bMode_apply, LinearMap.id_apply] using
        hexp (bMode LinearMap.id y p)
  obtain ⟨C, ha, hb⟩ := hsum
  rw [hb.tsum_eq]
  exact ⟨ha, hb⟩

/-- At fixed insertion states and roots, detectors admitting a common literal
double-mode sum form a submodule. -/
private def crossingDetectors (u v : TwistedEven) (w : TwistedOdd) (y : ℂ) :
    Submodule ℂ TwistedOdd where
  carrier := {b | ∃ C,
    HasSum (fun i => aMode LinearMap.id y i u v w b) C ∧
    HasSum (fun i => bMode LinearMap.id y i u v w b) C}
  zero_mem' := by
    refine ⟨0, ?_, ?_⟩ <;> simpa only [map_zero] using
      (hasSum_zero : HasSum (fun _ : ℤ × ℤ => (0 : ℂ)) 0)
  add_mem' := by
    rintro b d ⟨C, ha, hb⟩ ⟨D, ha', hb'⟩
    refine ⟨C + D, ?_, ?_⟩
    · simpa only [map_add, Pi.add_apply] using ha.add ha'
    · simpa only [map_add, Pi.add_apply] using hb.add hb'
  smul_mem' := by
    rintro c b ⟨C, ha, hb⟩
    refine ⟨c * C, ?_, ?_⟩
    · simpa only [map_smul, smul_eq_mul] using ha.mul_left c
    · simpa only [map_smul, smul_eq_mul] using hb.mul_left c

set_option maxHeartbeats 4000000 in
-- Identifies both expanded sums with evaluation at the translated detector.
private theorem translated_crossing (u v : TwistedEven) (w b : TwistedOdd)
    {y : ℂ} (hy : y ∈ upperTransportDomain) (hnorm : 1 < ‖y‖) :
    ∃ k : ℕ, (L₁ ^ k) b = 0 ∧ detectorExp y (k + 1) b ∈ crossingDetectors u v w y := by
  classical
  let support := (ambientBasis.repr b.val).support
  let bound (i : BasisIndex) := oddWeight ℒ i.1 / 2 + 1
  let k := support.sup bound
  have hcut (i : BasisIndex) (hi : i ∈ support) : bound i ≤ k :=
    Finset.le_sup hi
  refine ⟨k, ?_, ?_⟩
  · calc
      (L₁ ^ k) b = (L₁ ^ k) (∑ i ∈ support, component true b i) :=
        congrArg (fun d : TwistedOdd => (L₁ ^ k) d) (sum_projectedBasis true b).symm
      _ = 0 := by
        rw [map_sum]
        exact Finset.sum_eq_zero (fun i hi => component_lowering_tail b i k (hcut i hi))
  · let E := detectorExp y (k + 1)
    change (∃ C, HasSum (fun p => aMode LinearMap.id y p u v w (E b)) C ∧
      HasSum (fun p => bMode LinearMap.id y p u v w (E b)) C)
    let value (i : BasisQuad) := ∑' p, onComponents u v w b (bMode E y p) i
    have hcomponent (i : BasisQuad) (hi : i ∈ basisTuples u v w b) :
        HasSum (fun p => onComponents u v w b (aMode E y p) i) (value i) ∧
        HasSum (fun p => onComponents u v w b (bMode E y p) i) (value i) := by
      simp only [basisTuples, Finset.mem_product] at hi
      exact component_crossing u v w b i hy hnorm (k + 1)
        ((hcut i.2.2.2 hi.2.2.2).trans (Nat.le_succ k))
    refine ⟨∑ i ∈ basisTuples u v w b, value i, ?_, ?_⟩
    · refine (hasSum_sum (s := basisTuples u v w b) fun i hi => (hcomponent i hi).1).congr_fun ?_
      intro p
      simpa only [aMode_apply, LinearMap.id_apply] using expand u v w b (aMode E y p)
    · refine (hasSum_sum (s := basisTuples u v w b) fun i hi => (hcomponent i hi).2).congr_fun ?_
      intro p
      simpa only [bMode_apply, LinearMap.id_apply] using expand u v w b (bMode E y p)

set_option maxHeartbeats 4000000 in
-- Elaborates the detector submodule and endomorphism powers in the induction.
private theorem crossing_of_lowering_power (u v : TwistedEven) (w b : TwistedOdd)
    {y : ℂ} (hy : y ∈ upperTransportDomain) (hnorm : 1 < ‖y‖)
    (n : ℕ) (hnil : (L₁ ^ n) b = 0) : b ∈ crossingDetectors u v w y := by
  induction n generalizing b with
  | zero =>
      have hzero : b = 0 := by simpa only [pow_zero, Module.End.one_apply] using hnil
      rw [hzero]
      exact (crossingDetectors u v w y).zero_mem
  | succ n ih =>
      obtain ⟨k, _, htranslated⟩ := translated_crossing u v w b hy hnorm
      let term (j : ℕ) := (y ^ j / (j.factorial : ℂ)) • (L₁ ^ j) b
      -- The positive powers lie in the crossing submodule by the induction hypothesis.
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
-- Identifies the curried maps with the native A and B terms in both sums.
/-- For arbitrary actual states in the order H, B, H, B, the literal double-mode
series at the target insertions `1 - y` and `-y` converge to the same value.
The A separation root is `1`, and the B roots are `sqrt (1 - y)` and
`I * sqrt y`. -/
theorem hbhb_actual_complex_sewing_of_states (u v : TwistedEven) (w b : TwistedOdd)
    {y : ℂ} (him : 0 < y.im) (hre : y.re < (1 / 2 : ℝ)) (hnorm : 1 < ‖y‖) :
    let A := aJointTerm false u w v.val b.val 1 (Complex.I * Complex.sqrt y)
    let B := bJointTerm true false w (swapInput (s := false) v) u b (Complex.sqrt (1 - y))
      (Complex.I * Complex.sqrt y)
    HasSum A (∑' i : ℤ × ℤ, B i) ∧ HasSum B (∑' i : ℤ × ℤ, B i) ∧
      (∑' i : ℤ × ℤ, A i) = ∑' i : ℤ × ℤ, B i := by
  have hy : y ∈ upperTransportDomain := ⟨him, hre⟩
  obtain ⟨n, hnil, _⟩ := translated_crossing u v w b hy hnorm
  have h := crossing_of_lowering_power u v w b hy hnorm n hnil
  change (∃ C, HasSum (fun i => aMode LinearMap.id y i u v w b) C ∧
    HasSum (fun i => bMode LinearMap.id y i u v w b) C) at h
  let A := aJointTerm false u w v.val b.val 1 (Complex.I * Complex.sqrt y)
  let B := bJointTerm true false w (swapInput (s := false) v) u b (Complex.sqrt (1 - y))
    (Complex.I * Complex.sqrt y)
  obtain ⟨C, ha, hb⟩ : ∃ C, HasSum A C ∧ HasSum B C := by
    simpa only [A, B, aMode_apply, bMode_apply, LinearMap.id_apply] using h
  change HasSum A (∑' i, B i) ∧ HasSum B (∑' i, B i) ∧ (∑' i, A i) = ∑' i, B i
  rw [hb.tsum_eq]
  exact ⟨ha, hb, ha.tsum_eq⟩

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHBHBArbitrarySewing
