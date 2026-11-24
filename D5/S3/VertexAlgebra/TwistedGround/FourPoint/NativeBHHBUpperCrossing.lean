/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeBHHBUpperCrossing
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native marked BHHB crossing by exchanging the first two HBHB slots. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHBHBUpperAD
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedIterateSlot12Analytic

/-! The marked BHHB crossing obtained from HBHB by exchanging the first two slots. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBHHBUpperCrossing

open Complex (I)
open ActualLeechHyperbolic (leechData)
open LatticeHalfFockChargedTensorCoefficients (ActualGround)
open LatticeHalfFockGradedTrace (actualGrade)
open Orbifold.NativeOddTwistedIntertwiner (TwistedEven TwistedOdd leechUnit)
open Orbifold.NativeOddUpperRightSkew (lowering)
open Orbifold.NativeFixedPairField (nu_coeff_odd_zero)
open Orbifold.NativeMixedPairSkew (swapInput)
open OriginalFourMActualChart (Puncture)
open OriginalFourMVariableSupport (wordAt)
open NativeMixedWickChartTransport (MixedParity doubledOccupation)
open NativeFixedCrossedProductToIterate (dJointTerm translatedDetector)
open NativeMixedAIterateRadial (aJointTerm mixed_a_joint_summable_of_homogeneous)
open NativeMixedIterateSlot12Analytic (a_joint_iterate_hasSum_slot12 slot12_relative_root_sq)
open NativeHBHBUpperAD (hbhb_marked_upper_ad)

open private marked_grade aJointTerm_translated_detector from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHBHBUpperAD
open private sqrt_square from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedComplexSewing
open private occupationGrade_eq from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedPhysicalOverlap
open private punctureExcitation_cast from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedUpperProductCusp
open private lowered_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedInverseBPZ
open private sqrt_re_pos from D5.S3.Analytic.OriginalHalfBinomialSlitPeriod

local notation "ℒ" => leechData
local notation "L₁" => lowering ℒ leechUnit true

private theorem slit_of_im_ne {z : ℂ} (hz : z.im ≠ 0) : z ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inr hz)

private theorem sqrt_re_positive {z : ℂ} (hz : z.im ≠ 0) : 0 < (Complex.sqrt z).re := by
  change 0 < (z ^ ((2 : ℂ)⁻¹)).re
  simpa only [one_div] using sqrt_re_pos (slit_of_im_ne hz)

private theorem sqrt_im_positive {z : ℂ} (hz : 0 < z.im) : 0 < (Complex.sqrt z).im := by
  have hre := sqrt_re_positive (ne_of_gt hz)
  have hprod : 0 < 2 * (Complex.sqrt z).re * (Complex.sqrt z).im := by
    have hi := congrArg Complex.im (sqrt_square z)
    rw [pow_two, Complex.mul_im] at hi
    linarith
  by_contra! him
  exact hprod.not_ge (mul_nonpos_of_nonneg_of_nonpos (by positivity) him)

private theorem hbhb_outer_root_sq (y : ℂ) : (I * Complex.sqrt y) ^ (2 : ℕ) = -y := by
  rw [mul_pow, Complex.I_sq, sqrt_square, neg_one_mul]

/-- Exchanging the upper HBHB slots sends the outer A lift to the negative
square root of `1-y`. The relative factor is the principal root of `1-1/y`. -/
private theorem exchanged_outer_root {y : ℂ} (him : 0 < y.im) :
    -Complex.sqrt (1 - y) =
      (I * Complex.sqrt y) * (1 - ((-y) - (1 - y)) / (-y)) ^ ((2 : ℂ)⁻¹) := by
  have hy₀ : y ≠ 0 := Complex.slitPlane_ne_zero (slit_of_im_ne (ne_of_gt him))
  let r : ℂ := 1 - ((-y) - (1 - y)) / (-y)
  have hr : r = 1 - y⁻¹ := by
    dsimp only [r]
    rw [show -y - (1 - y) = -(1 : ℂ) by ring, neg_div_neg_eq, one_div]
  have hrIm : 0 < r.im := by
    rw [hr, Complex.sub_im, Complex.one_im, zero_sub, Complex.inv_im]
    exact neg_pos.mpr (div_neg_of_neg_of_pos (neg_lt_zero.mpr him)
      (Complex.normSq_pos.mpr hy₀))
  let z := (I * Complex.sqrt y) * Complex.sqrt r
  have hzSq : z ^ (2 : ℕ) = 1 - y :=
    slot12_relative_root_sq (x := 1 - y) (hbhb_outer_root_sq y) (neg_ne_zero.mpr hy₀)
  have hzRe : z.re < 0 := by
    have hReY := sqrt_re_positive (ne_of_gt him)
    have hImY := sqrt_im_positive him
    have hReR := sqrt_re_positive (ne_of_gt hrIm)
    have hImR := sqrt_im_positive hrIm
    dsimp only [z]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_sub, zero_add]
    linarith only [mul_neg_of_neg_of_pos (neg_lt_zero.mpr hImY) hReR, mul_pos hReY hImR]
  let w := Complex.sqrt (1 - y)
  have hwRe : 0 < w.re := sqrt_re_positive (by
    simpa only [Complex.sub_im, Complex.one_im, zero_sub, neg_ne_zero] using ne_of_gt him)
  have hprod : (z - w) * (z + w) = 0 := by
    calc
      _ = z ^ (2 : ℕ) - w ^ (2 : ℕ) := by ring
      _ = 0 := by rw [hzSq, show w ^ (2 : ℕ) = 1 - y from sqrt_square _, sub_self]
  rcases mul_eq_zero.mp hprod with h | h
  · have hre := congrArg Complex.re (sub_eq_zero.mp h)
    exact False.elim ((not_lt_of_ge (le_of_lt hwRe)) (hre ▸ hzRe))
  · change -w = z
    exact (eq_neg_of_add_eq_zero_left h).symm

private theorem fixed_d_neg_pair_root (u v : TwistedEven) (w b : TwistedOdd)
    (xR zR : ℂ) (i : ℤ × ℤ) :
    dJointTerm false true u v w b (-xR) zR i = dJointTerm false true u v w b xR zR i := by
  by_cases hi : Even i.1
  · simp only [dJointTerm, hi.neg_zpow]
  · simp only [dJointTerm, nu_coeff_odd_zero false i.1 u v (Int.not_even_iff_odd.mp hi),
      map_zero, Submodule.coe_zero, zero_mul]

/-- The BHHB B product in slot order `(w,u,v,b)`. The fixed field pairs
`u,v` at the second coordinate and the right field is attached to `w`
at the first coordinate. -/
def bJointTerm (w : TwistedOdd) (u v : TwistedEven) (b : TwistedOdd)
    (xR zR : ℂ) (i : ℤ × ℤ) : ℂ :=
  dJointTerm false true u v w b zR xR i

set_option maxHeartbeats 4000000 in
-- Elaborates the slot exchange for each lowered detector and sums the finite family.
/-- The marked BHHB A and B sums from the HHBB seed after `(2,3)` and
`(1,2)`. The B roots are `I * sqrt y` and `-sqrt (1-y)`; the A
difference root is `I`. The detector is carried through the second
exchange unchanged. The two sums have opposite values because the
exchanged first HBHB state has even grade. -/
theorem bhhb_marked_upper_crossing {X : Type*} [Finite X]
    (slot : X → Puncture) (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X)
    (hl : l.Nodup) (hpar : MixedParity slot n l)
    (u v : TwistedEven) (w b : TwistedOdd) (p q r d : ActualGround ℒ leechUnit)
    (hu : u.val = wordAt ℒ slot colour n l .P ⊗ₜ[ℂ] p)
    (hv : v.val = wordAt ℒ slot colour n l .Q ⊗ₜ[ℂ] q)
    (hw : w.val = wordAt ℒ slot colour n l .R ⊗ₜ[ℂ] r)
    (hb : b.val = wordAt ℒ slot colour n l .S ⊗ₜ[ℂ] d)
    {y : ℂ} (him : 0 < y.im) (hy : 1 < ‖y‖) (hre : (1 / 2 : ℝ) < y.re)
    (hcomp : 1 < ‖1 - y‖) :
    let N := (doubledOccupation slot n l .S).toNat
    let b' := translatedDetector true N y b
    let A := aJointTerm true w u v.val b'.val I (-Complex.sqrt (1 - y))
    let B := bJointTerm w u v b' (I * Complex.sqrt y) (-Complex.sqrt (1 - y))
    HasSum A (∑' i, A i) ∧ HasSum B (-(∑' i, A i)) := by
  let H (i : Puncture) := (doubledOccupation slot n l i).toNat
  let M := H .P
  let K := H .Q
  let L := H .R
  let N := H .S
  let b' := translatedDetector true N y b
  let xR := -Complex.sqrt (1 - y)
  let zR := I * Complex.sqrt y
  let A := aJointTerm true w u v.val b'.val I xR
  let B := bJointTerm w u v b' zR xR
  let A₀ := aJointTerm false u w v.val b'.val 1 zR
  let D₀ := dJointTerm false true u v w b' (Complex.sqrt (1 - y)) zR
  let T (j : ℕ) := (L₁ ^ j) b
  let a (j : ℕ) := aJointTerm false u w v.val (T j).val 1 zR
  let a' (j : ℕ) := aJointTerm true w u v.val (T j).val I xR
  let wt (j : ℕ) := y ^ j / (j.factorial : ℂ)
  let value := ∑ j ∈ Finset.range (N / 2 + 1), wt j * (∑' i : ℤ × ℤ, a' j i)
  change HasSum A (∑' i, A i) ∧ HasSum B (-(∑' i, A i))
  have hAD : HasSum A₀ (∑' i, D₀ i) ∧ HasSum D₀ (∑' i, D₀ i) :=
    hbhb_marked_upper_ad slot colour n l hl hpar u v w b p q r d hu hv hw hb him hy hre
  have huG : u.val ∈ actualGrade ℒ leechUnit M := hu.symm ▸ marked_grade slot colour n l .P p
  have hvG : v.val ∈ actualGrade ℒ leechUnit K := hv.symm ▸ marked_grade slot colour n l .Q q
  have hwG : w.val ∈ actualGrade ℒ leechUnit L := hw.symm ▸ marked_grade slot colour n l .R r
  have hbG : b.val ∈ actualGrade ℒ leechUnit N := hb.symm ▸ marked_grade slot colour n l .S d
  have hMcast : (M : ℤ) = doubledOccupation slot n l .P := by
    change (((doubledOccupation slot n l .P).toNat : ℕ) : ℤ) = _
    rw [occupationGrade_eq slot colour n l .P, punctureExcitation_cast]
  have hM : (M : ℤ) % 2 = 0 := by rw [hMcast]; exact hpar.1
  have hphase : (-1 : ℂ) ^ (3 + M) = -1 :=
    (Nat.odd_iff.mpr (by omega) : Odd (3 + M)).neg_one_pow
  have hgrade (j : ℕ) (hj : j ∈ Finset.range (N / 2 + 1)) :
      (T j).val ∈ actualGrade ℒ leechUnit (N - 2 * j) :=
    lowered_grade (s := true) (u := b) hbG (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  have hdiff : 1 - y - (-y) = 1 := by ring
  have hne : 1 - y ≠ -y := sub_ne_zero.mp (by rw [hdiff]; exact one_ne_zero)
  have hrad : ‖1 - y - (-y)‖ < min ‖1 - y‖ ‖-y‖ := by
    rw [hdiff, norm_one, norm_neg, lt_min_iff]
    exact ⟨hcomp, hy⟩
  have hxRad : ‖I‖ < ‖xR‖ := by
    rw [Complex.norm_I]
    apply (sq_lt_sq₀ zero_le_one (norm_nonneg xR)).mp
    simpa only [xR, norm_neg, one_pow, ← norm_pow, sqrt_square] using hcomp
  have hswap : swapInput (s := false) u = u := Subtype.ext rfl
  have hxLift : xR = zR * (1 - ((-y) - (1 - y)) / (-y)) ^ ((2 : ℂ)⁻¹) :=
    exchanged_outer_root him
  have hSlot (j : ℕ) (hj : j ∈ Finset.range (N / 2 + 1)) :
      HasSum (a j) (-(∑' i : ℤ × ℤ, a' j i)) := by
    have hs := a_joint_iterate_hasSum_slot12 false false M L K (N - 2 * j)
      u w v (T j) huG hwG hvG (hgrade j hj)
      (x := 1 - y) (z := -y) (xRoot := xR) (zRoot := zR) (dRoot := 1)
      (hbhb_outer_root_sq y) (by rw [hdiff, one_pow]) hne hrad hxLift
    simp only [hswap, hphase, mul_one, neg_one_mul] at hs
    change HasSum (a j)
      (-(∑' i : ℤ × ℤ, aJointTerm (!false) w u v.val (T j).val I xR i))
    exact hs
  have hSwap (j : ℕ) (hj : j ∈ Finset.range (N / 2 + 1)) : Summable (a' j) :=
    mixed_a_joint_summable_of_homogeneous true false L M K (N - 2 * j)
      w u v (T j) hwG huG hvG (hgrade j hj) Complex.I_ne_zero hxRad
  have hA : HasSum A value := by
    have hs : HasSum (fun i => ∑ j ∈ Finset.range (N / 2 + 1), wt j * a' j i) value :=
      hasSum_sum (s := Finset.range (N / 2 + 1)) fun j hj => (hSwap j hj).hasSum.mul_left _
    exact hs.congr_fun (aJointTerm_translated_detector true w u v b N y I xR)
  have hA₀ : HasSum A₀ (-value) := by
    have hs : HasSum (fun i => ∑ j ∈ Finset.range (N / 2 + 1), wt j * a j i)
        (∑ j ∈ Finset.range (N / 2 + 1), wt j * (-(∑' i : ℤ × ℤ, a' j i))) :=
      hasSum_sum (s := Finset.range (N / 2 + 1)) fun j hj => (hSlot j hj).mul_left _
    simp only [mul_neg, Finset.sum_neg_distrib] at hs
    exact hs.congr_fun (aJointTerm_translated_detector false u w v b N y 1 zR)
  have hDVal : (∑' i, D₀ i) = -value := hAD.1.unique hA₀
  have hD : HasSum D₀ (-value) := hDVal ▸ hAD.2
  have hB : HasSum B (-value) :=
    hD.congr_fun (fixed_d_neg_pair_root u v w b' (Complex.sqrt (1 - y)) zR)
  rw [hA.tsum_eq]
  exact ⟨hA, hB⟩

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBHHBUpperCrossing
