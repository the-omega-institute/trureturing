/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeHBHBCanonicalContinuation
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Upper HBHB amplitude for fixed actual Leech detectors. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHBHBArbitrarySewing
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHBHBUpperAD

/-! The finite inverse detector translation preserves holomorphy and identifies
both literal HBHB double-mode sums on their upper radial domains. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators Finset TensorProduct Topology VertexOperator
open Filter Set

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHBHBCanonicalContinuation

open Complex (I)
open ActualChargedAdjoint (actualForm)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open Orbifold.NativeOddTwistedIntertwiner (paritySign)
open Orbifold.NativeFixedPairField (nu)
open Orbifold.NativeFixedUpperRightSkew (rightField)
open NativeFixedCrossedProductToIterate (dJointTerm translatedDetector translationWeight)
open ActualLeechHyperbolic (leechData)
open LatticeHalfFockChargedTensorCoefficients (ActualGround)
open LatticeHalfFockGradedTrace (actualGrade actual_basis_apply oddWeight)
open Orbifold.NativeOddTwistedIntertwiner (Twisted TwistedEven TwistedOdd leechUnit)
open Orbifold.NativeOddUpperRightSkew (lowering)
open Orbifold.NativeMixedPairSkew (swapInput)
open OriginalFourMActualChart (Puncture)
open OriginalFourMVariableSupport (wordAt)
open NativeFourHHomogeneousExtension (occupation_monomials_have_marked_words)
open NativeMixedWickChartTransport (MixedParity doubledOccupation)
open NativeMixedAIterateRadial (aJointTerm)
open NativeMixedUpperProductCusp (bJointTerm bSewnNumerator)
open NativeHHBBUpperHalfPlaneBD (hhbb_marked_rawD_eq_neg_rawB_upper_half_plane)
open NativeHBHBUpperCrossing
  (upperTransportDomain hbhb_target_b_descendant_holomorphic hbhb_marked_upper_crossing)
open NativeHBHBUpperAD (hbhb_marked_a_hasSum_upper_exterior hbhb_marked_d_hasSum_upper_right)

open private BasisIndex ambientBasis from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHHomogeneousExtension
open private BasisQuad HHBBLinear project_basis_val component component_eq_zero basisTuples
  onComponents expand from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedArbitrarySewing
open private aMode bMode aMode_apply bMode_apply detectorExp detectorExp_apply
  component_lowering_tail from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHBHBArbitrarySewing
open private isOpen_upperTransportDomain from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHBHBUpperCrossing
open private occupationGrade_eq from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedPhysicalOverlap
open private punctureExcitation_cast wordAt_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedUpperProductCusp
open private cancel_lowering_orders from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedInverseBPZ
open private sum_projectedBasis from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairField

local notation "ℒ" => leechData
local notation "L₁" => lowering ℒ leechUnit true

/-- The source coordinate on the open upper half-plane. -/
def upperHalfPlane : Set ℂ := {y | 0 < y.im}

/-- The analytic HBHB amplitude with its literal native coefficients on the
upper exterior for A and the upper left radial domain for B. -/
def IsHBHBUpperAmplitude (u v : TwistedEven) (w : TwistedOdd)
    (detector : ℂ → TwistedOdd) (F : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ F upperHalfPlane ∧
    (∀ y ∈ upperHalfPlane, 1 < ‖y‖ →
      HasSum (aJointTerm false u w v.val (detector y).val 1 (I * Complex.sqrt y)) (F y)) ∧
    ∀ y ∈ upperTransportDomain,
      HasSum (bJointTerm true false w (swapInput (s := false) v) u (detector y)
        (Complex.sqrt (1 - y)) (I * Complex.sqrt y)) (F y)

/-- The right radial domain for the fixed HBHB product. -/
def upperRightDomain : Set ℂ := {y | 0 < y.im ∧ (1 / 2 : ℝ) < y.re}

private def IsHBHBUpperAmplitudeWithD (u v : TwistedEven) (w : TwistedOdd)
    (detector : ℂ → TwistedOdd) (F : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ F upperHalfPlane ∧
    (∀ y ∈ upperHalfPlane, 1 < ‖y‖ →
      HasSum (aJointTerm false u w v.val (detector y).val 1 (I * Complex.sqrt y)) (F y)) ∧
    (∀ y ∈ upperTransportDomain,
      HasSum (bJointTerm true false w (swapInput (s := false) v) u (detector y)
        (Complex.sqrt (1 - y)) (I * Complex.sqrt y)) (F y)) ∧
    ∀ y ∈ upperRightDomain,
      HasSum (dJointTerm false true u v w (detector y)
        (Complex.sqrt (1 - y)) (I * Complex.sqrt y)) (F y)

private def dMode (E : Module.End ℂ TwistedOdd) (y : ℂ) (i : ℤ × ℤ) : HHBBLinear :=
  let inner := ((LinearMap.proj i.1).comp HVertexOperator.coeff).comp (nu false)
  let right := ((LinearMap.proj i.2).comp HVertexOperator.coeff).comp (rightField ℒ leechUnit true)
  let sub := (paritySpace ℒ leechUnit (paritySign true)).subtype
  let pair := ((actualForm ℒ leechUnit).flip.compl₂ (sub.comp E)).comp sub
  (Complex.sqrt (1 - y) ^ i.1 * (I * Complex.sqrt y) ^ i.2) •
    inner.compr₂ (right.flip.compr₂ pair)

private theorem dMode_apply (E : Module.End ℂ TwistedOdd) (y : ℂ) (i : ℤ × ℤ)
    (u v : TwistedEven) (w b : TwistedOdd) :
    dMode E y i u v w b = dJointTerm false true u v w (E b)
      (Complex.sqrt (1 - y)) (I * Complex.sqrt y) i :=
  mul_comm _ _

private theorem detectorExp_eq_translatedDetector (y : ℂ) (N : ℕ) (b : TwistedOdd) :
    detectorExp y (N / 2 + 1) b = translatedDetector true N y b := by
  rw [detectorExp_apply, translatedDetector]
  simp only [translationWeight, div_eq_mul_inv]

private theorem lowering_tail (b : TwistedOdd) {k j : ℕ}
    (hnil : (L₁ ^ k) b = 0) (hj : k ≤ j) : (L₁ ^ j) b = 0 := by
  calc
    (L₁ ^ j) b = (L₁ ^ (j - k)) ((L₁ ^ k) b) := by
      rw [← Module.End.mul_apply, ← pow_add, Nat.sub_add_cancel hj]
    _ = 0 := by rw [hnil, map_zero]

private theorem detectorExp_mono (y : ℂ) (b : TwistedOdd) {k l : ℕ} (hkl : k ≤ l)
    (hnil : (L₁ ^ k) b = 0) : detectorExp y k b = detectorExp y l b := by
  rw [detectorExp_apply, detectorExp_apply]
  refine Finset.sum_subset (Finset.range_mono hkl) fun j _ hj => ?_
  have hkj : k ≤ j := Nat.le_of_not_gt fun h => hj (Finset.mem_range.mpr h)
  rw [lowering_tail b hnil hkj, smul_zero]

private theorem detectorExp_eq_of_nilpotent (y : ℂ) (b : TwistedOdd) {k l : ℕ}
    (hk : (L₁ ^ k) b = 0) (hl : (L₁ ^ l) b = 0) :
    detectorExp y k b = detectorExp y l b :=
  (detectorExp_mono y b (le_max_left k l) hk).trans
    (detectorExp_mono y b (le_max_right k l) hl).symm

private theorem eval_detectorExp (f : TwistedOdd →ₗ[ℂ] ℂ) (y : ℂ) (k : ℕ)
    (b : TwistedOdd) :
    f (detectorExp y k b) =
      ∑ j ∈ Finset.range k, (y ^ j / (j.factorial : ℂ)) * f ((L₁ ^ j) b) := by
  rw [detectorExp_apply, map_sum]
  simp only [map_smul, smul_eq_mul]

set_option maxHeartbeats 4000000 in
-- The marked source value and the two target terms use concrete doubled modes.
private theorem marked_upper_amplitude {X : Type*} [Finite X]
    (slot : X → Puncture) (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X)
    (hl : l.Nodup) (hpar : MixedParity slot n l)
    (u v : TwistedEven) (w b : TwistedOdd) (p q r d : ActualGround ℒ leechUnit)
    (hu : u.val = wordAt ℒ slot colour n l .P ⊗ₜ[ℂ] p)
    (hv : v.val = wordAt ℒ slot colour n l .Q ⊗ₜ[ℂ] q)
    (hw : w.val = wordAt ℒ slot colour n l .R ⊗ₜ[ℂ] r)
    (hb : b.val = wordAt ℒ slot colour n l .S ⊗ₜ[ℂ] d) :
    ∃ F, IsHBHBUpperAmplitudeWithD u v w
      (fun y => detectorExp y ((doubledOccupation slot n l .S).toNat / 2 + 1) b) F := by
  let H (i : Puncture) := (doubledOccupation slot n l i).toNat
  let V := wordAt ℒ slot colour n l
  let M := H .P
  let K := H .Q
  let L := H .R
  let N := H .S
  let B₀ (y : ℂ) := Complex.sqrt y ^ (-(6 + (K : ℤ) + L)) *
    I ^ ((L : ℤ) + N - M - 2 * (K : ℤ) - 3) *
    bSewnNumerator K L N (V .P) (V .Q) (V .R) (V .S) p q r d y
  have hRaw := hhbb_marked_rawD_eq_neg_rawB_upper_half_plane slot colour n l hl hpar
    u v w b p q r d hu hv hw hb
  have hB₀ : AnalyticOnNhd ℂ B₀ upperHalfPlane := hRaw.1
  have hCast (i : Puncture) : (H i : ℤ) = doubledOccupation slot n l i := by
    change (((doubledOccupation slot n l i).toNat : ℕ) : ℤ) = _
    rw [occupationGrade_eq slot colour n l i, punctureExcitation_cast]
  have hM : (M : ℤ) % 2 = 0 := by simpa only [M, hCast] using hpar.1
  have hK : (K : ℤ) % 2 = 0 := by simpa only [K, hCast] using hpar.2.1
  have hL : (L : ℤ) % 2 = 1 := by simpa only [L, hCast] using hpar.2.2.1
  have hN : (N : ℤ) % 2 = 1 := by simpa only [N, hCast] using hpar.2.2.2
  have hKL : Odd ((K : ℤ) + L) := Int.odd_iff.mpr (by omega)
  have hNM : Odd ((N : ℤ) - M) := Int.odd_iff.mpr (by omega)
  have hGrade (i : Puncture) (g : ActualGround ℒ leechUnit) :
      V i ⊗ₜ[ℂ] g ∈ actualGrade ℒ leechUnit (H i) := by
    rw [show H i = _ from occupationGrade_eq slot colour n l i]
    exact wordAt_grade slot colour n l i g
  have huG : u.val ∈ actualGrade ℒ leechUnit M := hu.symm ▸ hGrade .P p
  have hvG : v.val ∈ actualGrade ℒ leechUnit K := hv.symm ▸ hGrade .Q q
  have hwG : w.val ∈ actualGrade ℒ leechUnit L := hw.symm ▸ hGrade .R r
  have hbG : b.val ∈ actualGrade ℒ leechUnit N := hb.symm ▸ hGrade .S d
  let term (j : ℕ) (y : ℂ) := bJointTerm true false w (swapInput (s := false) v) u ((L₁ ^ j) b)
    (Complex.sqrt (1 - y)) (I * Complex.sqrt y)
  let B (y : ℂ) := ∑ j ∈ Finset.range (N / 2 + 1), (y ^ j / (j.factorial : ℂ)) *
    (∑' i : ℤ × ℤ, term j y i)
  have hEq : EqOn B (-B₀) upperTransportDomain :=
    (hbhb_marked_upper_crossing slot colour n l hl hpar u v w b p q r d hu hv hw hb).2.1
  refine ⟨-B₀, hB₀.neg, ?_, ?_, ?_⟩
  · intro y him hy
    have hA := (hbhb_marked_a_hasSum_upper_exterior slot colour n l hl hpar
      u v w b p q r d hu hv hw hb him hy).1
    refine hA.congr_fun fun i => ?_
    simpa only [aMode_apply, LinearMap.id_apply] using
      eval_detectorExp (aMode LinearMap.id y i u v w) y (N / 2 + 1) b
  · intro y hy
    change HasSum (bJointTerm true false w (swapInput (s := false) v) u
      (detectorExp y (N / 2 + 1) b) (Complex.sqrt (1 - y)) (I * Complex.sqrt y)) ((-B₀) y)
    rw [← hEq hy]
    have hSummable (j : ℕ) (hj : j ∈ Finset.range (N / 2 + 1)) : Summable (term j y) :=
      (hbhb_target_b_descendant_holomorphic M K L N j u v w b (V .P) (V .Q) (V .R) (V .S)
        p q r d huG hvG hwG hbG hu hv hw hb hKL hNM
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).2 y hy
    have hB : HasSum (fun i => ∑ j ∈ Finset.range (N / 2 + 1),
        (y ^ j / (j.factorial : ℂ)) * term j y i) (B y) :=
      hasSum_sum (s := Finset.range (N / 2 + 1)) fun j hj => (hSummable j hj).hasSum.mul_left _
    refine hB.congr_fun fun i => ?_
    simpa only [term, bMode_apply, LinearMap.id_apply] using
      eval_detectorExp (bMode LinearMap.id y i u v w) y (N / 2 + 1) b
  · intro y hy
    change HasSum (dJointTerm false true u v w (detectorExp y (N / 2 + 1) b)
      (Complex.sqrt (1 - y)) (I * Complex.sqrt y)) (-(B₀ y))
    rw [detectorExp_eq_translatedDetector]
    exact hbhb_marked_d_hasSum_upper_right slot colour n l hl hpar u v w b
      p q r d hu hv hw hb hy.1 hy.2

set_option maxHeartbeats 4000000 in
-- Realize the projected basis tuple as marked words in each parity slot.
private theorem component_upper_amplitude (u v : TwistedEven) (w b : TwistedOdd)
    (i : BasisQuad) (k : ℕ) (hk : oddWeight ℒ i.2.2.2.1 / 2 + 1 ≤ k) :
    ∃ F, IsHBHBUpperAmplitudeWithD (component false u i.1) (component false v i.2.1)
      (component true w i.2.2.1) (fun y => detectorExp y k (component true b i.2.2.2)) F := by
  classical
  let u' := component false u i.1
  let v' := component false v i.2.1
  let w' := component true w i.2.2.1
  let b' := component true b i.2.2.2
  let index : Puncture → BasisIndex
    | .P => i.1
    | .Q => i.2.1
    | .R => i.2.2.1
    | .S => i.2.2.2
  let odd : Puncture → Bool
    | .P => false
    | .Q => false
    | .R => true
    | .S => true
  change ∃ F, IsHBHBUpperAmplitudeWithD u' v' w' (fun y => detectorExp y k b') F
  by_cases h : ∀ t, oddWeight ℒ (index t).1 % 2 = (if odd t then 1 else 0)
  swap
  · obtain ⟨t, ht⟩ := not_forall.mp h
    have hzero (F : HHBBLinear) : F u' v' w' b' = 0 := by
      cases t with
      | P => simp [show u' = 0 from component_eq_zero false u i.1 ht]
      | Q => simp [show v' = 0 from component_eq_zero false v i.2.1 ht]
      | R => simp [show w' = 0 from component_eq_zero true w i.2.2.1 ht]
      | S => simp [show b' = 0 from component_eq_zero true b i.2.2.2 ht]
    have hz : HasSum (fun _ : ℤ × ℤ => (0 : ℂ)) 0 := hasSum_zero
    refine ⟨fun _ => 0, fun _ _ => analyticAt_const, ?_, ?_, ?_⟩
    · intro y _ _
      exact hz.congr_fun fun m => by
        simpa only [aMode_apply] using hzero (aMode (detectorExp y k) y m)
    · intro y _
      exact hz.congr_fun fun m => by
        simpa only [bMode_apply] using hzero (bMode (detectorExp y k) y m)
    · intro y _
      simpa only [dMode_apply] using hz.congr_fun (fun i => hzero (dMode (detectorExp y k) y i))
  obtain ⟨m, slot, colour, n, hmarks⟩ :=
    occupation_monomials_have_marked_words (fun t => (index t).1)
  let l := List.finRange m
  let W := wordAt ℒ slot colour n l
  have hweight (t : Puncture) :
      doubledOccupation slot n l t % 2 = ((if odd t then 1 else 0 : ℕ) : ℤ) := by
    rw [(hmarks t).2]
    exact_mod_cast h t
  have hpar : MixedParity slot n l := ⟨hweight .P, hweight .Q, hweight .R, hweight .S⟩
  let ground (s : Bool) (a : Twisted ℒ leechUnit s) (t : Puncture) :
      ActualGround ℒ leechUnit :=
    ambientBasis.repr a.val (index t) • Pi.single (index t).2 (1 : ℂ)
  have hword (s : Bool) (a : Twisted ℒ leechUnit s) (t : Puncture) (ht : odd t = s) :
      (component s a (index t)).val = W t ⊗ₜ[ℂ] ground s a t := by
    have hp := h t
    rw [ht] at hp
    rw [component, Submodule.coe_smul, project_basis_val, ite_eq_left hp,
      actual_basis_apply ℒ leechUnit (index t).1 (index t).2]
    change ambientBasis.repr a.val (index t) •
        (MvPolynomial.monomial (index t).1 (1 : ℂ) ⊗ₜ[ℂ] Pi.single (index t).2 (1 : ℂ)) =
      W t ⊗ₜ[ℂ] (ambientBasis.repr a.val (index t) • Pi.single (index t).2 (1 : ℂ))
    have hW : W t = MvPolynomial.monomial (index t).1 (1 : ℂ) := (hmarks t).1
    rw [TensorProduct.tmul_smul, hW]
  let N := (doubledOccupation slot n l .S).toNat
  have hN : N = oddWeight ℒ i.2.2.2.1 := congrArg Int.toNat (hmarks .S).2
  have hcut : N / 2 + 1 ≤ k := by simpa only [hN] using hk
  have hnil : (L₁ ^ (N / 2 + 1)) b' = 0 :=
    component_lowering_tail b i.2.2.2 _ (by rw [hN])
  have hexp (y : ℂ) : detectorExp y (N / 2 + 1) b' = detectorExp y k b' :=
    detectorExp_mono y b' hcut hnil
  obtain ⟨F, hF⟩ := marked_upper_amplitude slot colour n l (List.nodup_finRange m) hpar
    u' v' w' b' (ground false u .P) (ground false v .Q) (ground true w .R) (ground true b .S)
    (hword false u .P rfl) (hword false v .Q rfl) (hword true w .R rfl) (hword true b .S rfl)
  refine ⟨F, hF.1, ?_, ?_, ?_⟩
  · intro y hy he
    change HasSum (aJointTerm false u' w' v'.val (detectorExp y k b').val
      1 (I * Complex.sqrt y)) (F y)
    rw [← hexp y]
    exact hF.2.1 y hy he
  · intro y hy
    change HasSum (bJointTerm true false w' (swapInput (s := false) v') u' (detectorExp y k b')
      (Complex.sqrt (1 - y)) (I * Complex.sqrt y)) (F y)
    rw [← hexp y]
    exact hF.2.2.1 y hy
  · intro y hy
    change HasSum (dJointTerm false true u' v' w' (detectorExp y k b')
      (Complex.sqrt (1 - y)) (I * Complex.sqrt y)) (F y)
    rw [← hexp y]
    exact hF.2.2.2 y hy

private def detectorBound (b : TwistedOdd) : ℕ :=
  (ambientBasis.repr b.val).support.sup fun i => oddWeight ℒ i.1 / 2 + 1

private theorem detectorBound_ge (b : TwistedOdd) (i : BasisIndex)
    (hi : i ∈ (ambientBasis.repr b.val).support) :
    oddWeight ℒ i.1 / 2 + 1 ≤ detectorBound b :=
  Finset.le_sup (f := fun i : BasisIndex => oddWeight ℒ i.1 / 2 + 1) hi

private theorem detectorBound_annihilates (b : TwistedOdd) :
    (L₁ ^ detectorBound b) b = 0 := by
  classical
  let support := (ambientBasis.repr b.val).support
  calc
    (L₁ ^ detectorBound b) b = (L₁ ^ detectorBound b) (∑ i ∈ support, component true b i) :=
      congrArg (fun d : TwistedOdd => (L₁ ^ detectorBound b) d) (sum_projectedBasis true b).symm
    _ = 0 := by
      rw [map_sum]
      exact Finset.sum_eq_zero fun i hi =>
        component_lowering_tail b i _ (detectorBound_ge b i hi)

set_option maxHeartbeats 4000000 in
-- Assemble the finitely many marked amplitudes supported by the four states.
private theorem translated_upper_amplitude (u v : TwistedEven) (w b : TwistedOdd)
    (k : ℕ) (hnil : (L₁ ^ k) b = 0) :
    ∃ F, IsHBHBUpperAmplitudeWithD u v w (fun y => detectorExp y k b) F := by
  classical
  let indices := basisTuples u v w b
  let m := detectorBound b
  have hComponent (i : BasisQuad) (hi : i ∈ indices) :
      ∃ F, IsHBHBUpperAmplitudeWithD (component false u i.1) (component false v i.2.1)
        (component true w i.2.2.1) (fun y => detectorExp y m (component true b i.2.2.2)) F := by
    change i ∈ basisTuples u v w b at hi
    simp only [basisTuples, Finset.mem_product] at hi
    exact component_upper_amplitude u v w b i m (detectorBound_ge b _ hi.2.2.2)
  let value (i : BasisQuad) : ℂ → ℂ :=
    if hi : i ∈ indices then Classical.choose (hComponent i hi) else 0
  have hValue (i : BasisQuad) (hi : i ∈ indices) :
      IsHBHBUpperAmplitudeWithD (component false u i.1) (component false v i.2.1)
        (component true w i.2.2.1) (fun y => detectorExp y m (component true b i.2.2.2))
        (value i) := by
    simpa only [value, dite_eq_left hi] using Classical.choose_spec (hComponent i hi)
  have hcut (y : ℂ) : detectorExp y k b = detectorExp y m b :=
    detectorExp_eq_of_nilpotent y b hnil (detectorBound_annihilates b)
  refine ⟨fun y => ∑ i ∈ indices, value i y, ?_, ?_, ?_, ?_⟩
  · intro y hy
    exact Finset.analyticAt_fun_sum indices fun i hi => (hValue i hi).1 y hy
  · intro y hy hr
    change HasSum (aJointTerm false u w v.val (detectorExp y k b).val 1 (I * Complex.sqrt y)) _
    rw [hcut y]
    have hA (i : BasisQuad) (hi : i ∈ indices) :
        HasSum (fun j => onComponents u v w b (aMode (detectorExp y m) y j) i) (value i y) := by
      simpa only [onComponents, aMode_apply] using (hValue i hi).2.1 y hy hr
    refine (hasSum_sum (s := indices) hA).congr_fun fun j => ?_
    simpa only [aMode_apply] using expand u v w b (aMode (detectorExp y m) y j)
  · intro y hy
    change HasSum (bJointTerm true false w (swapInput (s := false) v) u (detectorExp y k b)
      (Complex.sqrt (1 - y)) (I * Complex.sqrt y)) _
    rw [hcut y]
    have hB (i : BasisQuad) (hi : i ∈ indices) :
        HasSum (fun j => onComponents u v w b (bMode (detectorExp y m) y j) i) (value i y) := by
      simpa only [onComponents, bMode_apply] using (hValue i hi).2.2.1 y hy
    refine (hasSum_sum (s := indices) hB).congr_fun fun j => ?_
    simpa only [bMode_apply] using expand u v w b (bMode (detectorExp y m) y j)
  · intro y hy
    change HasSum (dJointTerm false true u v w (detectorExp y k b)
      (Complex.sqrt (1 - y)) (I * Complex.sqrt y)) _
    rw [hcut y]
    have hD (i : BasisQuad) (hi : i ∈ indices) :
        HasSum (fun j => onComponents u v w b (dMode (detectorExp y m) y j) i) (value i y) := by
      simpa only [onComponents, dMode_apply] using (hValue i hi).2.2.2 y hy
    refine (hasSum_sum (s := indices) hD).congr_fun fun j => ?_
    simpa only [dMode_apply] using expand u v w b (dMode (detectorExp y m) y j)

private theorem eval_detectorExp_inverse (f : TwistedOdd →ₗ[ℂ] ℂ) (y : ℂ)
    (n : ℕ) (b : TwistedOdd) :
    (∑ j ∈ Finset.range (n + 1), ((-y) ^ j / (j.factorial : ℂ)) *
      f (detectorExp y (n - j + 1) ((L₁ ^ j) b))) = f b := by
  let g (r : ℕ) := y ^ r * f ((L₁ ^ r) b)
  have hzero : g 0 = f b := by simp [g, Module.End.one_apply]
  rw [← hzero, ← cancel_lowering_orders n g]
  apply Finset.sum_congr rfl
  intro j _
  rw [eval_detectorExp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [← Module.End.mul_apply, ← pow_add, add_comm q j]
  have hneg : (-y) ^ j = (-1 : ℂ) ^ j * y ^ j := by
    rw [← mul_pow, neg_one_mul]
  rw [hneg]
  simp only [g, pow_add y j q, div_eq_mul_inv]
  ring

set_option maxHeartbeats 4000000 in
-- Transport the finite inverse of the lowered detector family to both sums.
private theorem fixed_upper_amplitude_of_bound (u v : TwistedEven) (w b : TwistedOdd)
    (n : ℕ) (hnil : (L₁ ^ (n + 1)) b = 0) :
    ∃ F, IsHBHBUpperAmplitudeWithD u v w (fun _ => b) F := by
  classical
  have hDesc (j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
      ∃ G, IsHBHBUpperAmplitudeWithD u v w
        (fun y => detectorExp y (n - j + 1) ((L₁ ^ j) b)) G := by
    apply translated_upper_amplitude
    have hj' := Finset.mem_range.mp hj
    rw [← Module.End.mul_apply, ← pow_add, show n - j + 1 + j = n + 1 by omega]
    exact hnil
  let value (j : ℕ) : ℂ → ℂ :=
    if hj : j ∈ Finset.range (n + 1) then Classical.choose (hDesc j hj) else 0
  have hValue (j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
      IsHBHBUpperAmplitudeWithD u v w (fun y => detectorExp y (n - j + 1) ((L₁ ^ j) b))
        (value j) := by
    simpa only [value, dite_eq_left hj] using Classical.choose_spec (hDesc j hj)
  let F (y : ℂ) := ∑ j ∈ Finset.range (n + 1), ((-y) ^ j / (j.factorial : ℂ)) * value j y
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro y hy
    refine Finset.analyticAt_fun_sum (Finset.range (n + 1)) fun j hj => ?_
    have hWeight : AnalyticAt ℂ (fun z : ℂ => (-z) ^ j / (j.factorial : ℂ)) y :=
      (((analyticAt_id (z := y)).neg).pow j).div_const
    exact hWeight.mul ((hValue j hj).1 y hy)
  · intro y hy hr
    have hA := hasSum_sum (s := Finset.range (n + 1)) fun j hj =>
      ((hValue j hj).2.1 y hy hr).mul_left ((-y) ^ j / (j.factorial : ℂ))
    refine hA.congr_fun fun i => ?_
    simpa only [aMode_apply, LinearMap.id_apply] using
      (eval_detectorExp_inverse (aMode LinearMap.id y i u v w) y n b).symm
  · intro y hy
    have hB := hasSum_sum (s := Finset.range (n + 1)) fun j hj =>
      ((hValue j hj).2.2.1 y hy).mul_left ((-y) ^ j / (j.factorial : ℂ))
    refine hB.congr_fun fun i => ?_
    simpa only [bMode_apply, LinearMap.id_apply] using
      (eval_detectorExp_inverse (bMode LinearMap.id y i u v w) y n b).symm

  · intro y hy
    have hD := hasSum_sum (s := Finset.range (n + 1)) fun j hj =>
      ((hValue j hj).2.2.2 y hy).mul_left ((-y) ^ j / (j.factorial : ℂ))
    refine hD.congr_fun fun i => ?_
    simpa only [dMode_apply, LinearMap.id_apply] using
      (eval_detectorExp_inverse (dMode LinearMap.id y i u v w) y n b).symm

private theorem fixed_upper_amplitude_with_d (u v : TwistedEven) (w b : TwistedOdd) :
    ∃ F, IsHBHBUpperAmplitudeWithD u v w (fun _ => b) F :=
  fixed_upper_amplitude_of_bound u v w b (detectorBound b)
    (lowering_tail b (detectorBound_annihilates b) (Nat.le_succ _))

private theorem IsHBHBUpperAmplitudeWithD.ab
    {u v : TwistedEven} {w : TwistedOdd} {b : ℂ → TwistedOdd} {F : ℂ → ℂ}
    (h : IsHBHBUpperAmplitudeWithD u v w b F) : IsHBHBUpperAmplitude u v w b F :=
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- For arbitrary actual Leech states in HBHB order, one function analytic on
`Im y > 0` sums the literal A modes on `1 < ‖y‖` and the literal B modes on
`Re y < 1/2`, with the detector held fixed in both channels. -/
theorem hbhb_actual_upper_amplitude (u v : TwistedEven) (w b : TwistedOdd) :
    ∃ F, IsHBHBUpperAmplitude u v w (fun _ => b) F := by
  obtain ⟨F, hF⟩ := fixed_upper_amplitude_with_d u v w b
  exact ⟨F, hF.ab⟩

/-- The raw HBHB amplitude on the upper half-plane with a fixed detector. -/
def hbhbUpperAmplitude (u v : TwistedEven) (w b : TwistedOdd) : ℂ → ℂ :=
  Classical.choose (fixed_upper_amplitude_with_d u v w b)

theorem hbhbUpperAmplitude_spec (u v : TwistedEven) (w b : TwistedOdd) :
    IsHBHBUpperAmplitude u v w (fun _ => b) (hbhbUpperAmplitude u v w b) :=
  (Classical.choose_spec (fixed_upper_amplitude_with_d u v w b)).ab

/-- The literal fixed D product has the same canonical value on the upper
right domain after finite inversion of the detector translation. -/
theorem hbhbUpperAmplitude_hasSum_d (u v : TwistedEven) (w b : TwistedOdd)
    {y : ℂ} (hy : y ∈ upperRightDomain) :
    HasSum (dJointTerm false true u v w b (Complex.sqrt (1 - y)) (I * Complex.sqrt y))
      (hbhbUpperAmplitude u v w b y) :=
  (Classical.choose_spec (fixed_upper_amplitude_with_d u v w b)).2.2.2 y hy

/-- The actual B sums determine the fixed-detector continuation throughout the
upper half-plane. In particular the choice of annihilating cutoff cannot alter it. -/
theorem hbhb_actual_upper_amplitude_unique (u v : TwistedEven) (w b : TwistedOdd)
    {F G : ℂ → ℂ} (hF : IsHBHBUpperAmplitude u v w (fun _ => b) F)
    (hG : IsHBHBUpperAmplitude u v w (fun _ => b) G) : EqOn F G upperHalfPlane := by
  have hi : I ∈ upperTransportDomain := by
    change 0 < I.im ∧ I.re < (1 / 2 : ℝ)
    norm_num
  have hConnected : IsPreconnected upperHalfPlane :=
    (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected
  have hgerm : F =ᶠ[𝓝 I] G := by
    filter_upwards [isOpen_upperTransportDomain.mem_nhds hi] with y hy
    exact (hF.2.2 y hy).unique (hG.2.2 y hy)
  exact hF.1.eqOn_of_preconnected_of_eventuallyEq hG.1 hConnected hi.1 hgerm

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHBHBCanonicalContinuation
