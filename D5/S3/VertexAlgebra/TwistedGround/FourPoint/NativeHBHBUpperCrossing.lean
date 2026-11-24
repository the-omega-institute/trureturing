/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeHBHBUpperCrossing
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Marked native Leech HBHB crossing on the upper oriented overlap. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBUpperHalfPlaneBD
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedCrossedProductToIterate
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedProductSlot23Analytic

/-! The slot-(2,3) transport of marked actual HHBB states to the upper HBHB overlap. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct Topology VertexOperator
open Filter Metric Set

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHBHBUpperCrossing

open Complex (I)
open ActualLeechHyperbolic (leechData)
open LatticeGeneratingFieldLocality (Oscillator)
open LatticeHalfFockChargedTensorCoefficients (ActualGround)
open LatticeHalfFockGradedTrace (actualGrade)
open Orbifold.NativeOddTwistedIntertwiner (TwistedEven TwistedOdd leechUnit)
open Orbifold.NativeOddUpperRightSkew (lowering)
open Orbifold.NativeMixedPairSkew (swapInput)
open OriginalFourMActualChart (Puncture)
open OriginalFourMChargeCoset (oscillatorLower)
open OriginalFourMVariableSupport (wordAt)
open NativeMixedWickChartTransport (MixedParity doubledOccupation sigma)
open NativeMixedUpperProductCusp (bJointTerm bSewnNumerator b_joint_product_hasSum)
open NativeMixedUpperDLip (dSlitProduct)
open NativeHHBBBSlitExtension (hhbb_marked_b_slit_extension)
open NativeHHBBUpperHalfPlaneBD
  (hhbb_marked_rawD_eq_neg_rawB_upper_half_plane hhbb_marked_rawD_hasSum_upper_exterior)
open NativeMixedProductSlot23Analytic (b_joint_product_hasSum_slot23)
open NativeMixedAIterateRadial (aJointTerm mixed_a_joint_summable_of_homogeneous)
open NativeMixedCrossedProductToIterate (mixed_d_joint_hasSum_crossed_a)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod
  (slitDomain isOpen_slitDomain ball_subset_slitDomain)

open private sqrt_square square_root_disk from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedComplexSewing
open private norm_one_sub_lt_iff from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHRealSewing
open private bSewnNumerator_differentiableOn punctureExcitation_cast wordAt_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedUpperProductCusp
open private occupationGrade_eq from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedPhysicalOverlap
open private lowered_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedInverseBPZ
open private lowered_tmul from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBProductInversion
open private swapInput_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairSkew

local notation "ℒ" => leechData
local notation "L₁" => lowering ℒ leechUnit

/-- The upper source domain where the slot-(2,3) B product is radial. -/
def upperTransportDomain : Set ℂ :=
  {y | 0 < y.im} ∩ {y | y.re < (1 / 2 : ℝ)}

private theorem isOpen_upperTransportDomain : IsOpen upperTransportDomain :=
  (isOpen_lt continuous_const Complex.continuous_im).inter
    (isOpen_lt Complex.continuous_re continuous_const)

private theorem source_mem_slit {y : ℂ} (him : 0 < y.im) : y ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inr (ne_of_gt him))

private theorem transported_inner_sq (y : ℂ) :
    (I * Complex.sqrt y) ^ (2 : ℕ) = -y := by
  rw [mul_pow, Complex.I_sq, sqrt_square, neg_one_mul]

set_option maxHeartbeats 1200000 in
-- Elaborate the analytic sum on the concrete twisted spaces.
/-- After swapping the middle slots, each actual lowered B product sums
at the transported roots. Its native double sum is holomorphic throughout
`upperTransportDomain`. -/
theorem hbhb_target_b_descendant_holomorphic (M K L N j : ℕ)
    (u v : TwistedEven) (w b : TwistedOdd) (P Q R S : Oscillator ℒ)
    (p q r d : ActualGround ℒ leechUnit)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (hw : w.val ∈ actualGrade ℒ leechUnit L) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    (huP : u.val = P ⊗ₜ[ℂ] p) (hvQ : v.val = Q ⊗ₜ[ℂ] q)
    (hwR : w.val = R ⊗ₜ[ℂ] r) (hbS : b.val = S ⊗ₜ[ℂ] d)
    (hKL : Odd ((K : ℤ) + L)) (hNM : Odd ((N : ℤ) - M)) (hj : j ≤ N / 2) :
    let term (y : ℂ) := bJointTerm true false w (swapInput (s := false) v) u ((L₁ true ^ j) b)
      (Complex.sqrt (1 - y)) (I * Complex.sqrt y)
    AnalyticOnNhd ℂ (fun y => ∑' i : ℤ × ℤ, term y i) upperTransportDomain ∧
      ∀ y ∈ upperTransportDomain, Summable (term y) := by
  let term (y : ℂ) := bJointTerm true false w (swapInput (s := false) v) u ((L₁ true ^ j) b)
    (Complex.sqrt (1 - y)) (I * Complex.sqrt y)
  change AnalyticOnNhd ℂ (fun y => ∑' i : ℤ × ℤ, term y i) upperTransportDomain ∧
    ∀ y ∈ upperTransportDomain, Summable (term y)
  let J := N - 2 * j
  let pole : ℤ := 6 + (L : ℤ) + K
  let phase : ℂ := I ^ ((K : ℤ) + J - M - 2 * (L : ℤ) - 3)
  let numerator := bSewnNumerator L K J P R Q ((oscillatorLower ℒ ^ j) S) p r q d
  let outer (y : ℂ) := Complex.sqrt (1 - y)
  let inner (y : ℂ) := I * Complex.sqrt y
  let ratio (y : ℂ) := inner y / outer y
  let value (y : ℂ) :=
    outer y ^ ((J : ℤ) - M - pole) *
      (ratio y ^ (-pole) * phase * numerator (ratio y ^ (2 : ℕ)))
  have hdesc := lowered_grade (s := true) (u := b) hb hj
  have hdescTensor := lowered_tmul (s := true) j b S d hbS
  have hv' : (swapInput (s := false) v).val ∈ actualGrade ℒ leechUnit K := by
    simpa only [swapInput_val] using hv
  have hvQ' : (swapInput (s := false) v).val = Q ⊗ₜ[ℂ] q := by
    simpa only [swapInput_val] using hvQ
  have hLK : Odd ((L : ℤ) + K) := by rwa [add_comm]
  have hj₂ : 2 * j ≤ N := by omega
  have hJM : Odd ((J : ℤ) - M) := by
    obtain ⟨m, hm⟩ := hNM
    refine ⟨m - (j : ℤ), ?_⟩
    dsimp only [J]
    rw [Nat.cast_sub hj₂]
    omega
  have hlocal (y : ℂ) (hy : y ∈ upperTransportDomain) :
      HasSum (term y) (value y) ∧ AnalyticAt ℂ value y := by
    have him : 0 < y.im := hy.1
    have hre : y.re < (1 / 2 : ℝ) := hy.2
    have hySlit : y ∈ Complex.slitPlane := source_mem_slit him
    have hComplementRe : (1 / 2 : ℝ) < (1 - y).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hComplementSlit : 1 - y ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl ((by norm_num : (0 : ℝ) < 1 / 2).trans hComplementRe))
    have houtSq : outer y ^ (2 : ℕ) = 1 - y := sqrt_square _
    have hratioSq : ratio y ^ (2 : ℕ) = -y / (1 - y) := by
      change (inner y / outer y) ^ (2 : ℕ) = -y / (1 - y)
      rw [div_pow, houtSq]
      exact congrArg (fun z : ℂ => z / (1 - y)) (transported_inner_sq y)
    have hnorm : ‖y‖ < ‖1 - y‖ := by
      simpa only [sub_sub_cancel] using (norm_one_sub_lt_iff (1 - y)).mpr hComplementRe
    have hout₀ : outer y ≠ 0 := fun h =>
      Complex.slitPlane_ne_zero hComplementSlit (by simpa [h] using houtSq.symm)
    have harg₀ : -y / (1 - y) ≠ 0 :=
      div_ne_zero (neg_ne_zero.mpr (Complex.slitPlane_ne_zero hySlit))
        (Complex.slitPlane_ne_zero hComplementSlit)
    have harg₁ : ‖-y / (1 - y)‖ < 1 := by
      rw [norm_div, norm_neg, div_lt_one (norm_pos_iff.mpr (Complex.slitPlane_ne_zero hComplementSlit))]
      exact hnorm
    obtain ⟨hratio₀, hratio₁⟩ := square_root_disk hratioSq harg₀ harg₁
    refine ⟨b_joint_product_hasSum true false M L K J w (swapInput (s := false) v) u ((L₁ true ^ j) b)
      P R Q ((oscillatorLower ℒ ^ j) S) p r q d hw hv' hu hdesc hwR hvQ' huP
      hdescTensor hLK hJM hout₀ (norm_pos_iff.mpr hratio₀) hratio₁, ?_⟩
    have hsqrt : AnalyticAt ℂ Complex.sqrt y :=
      Complex.differentiableOn_sqrt.analyticOnNhd Complex.isOpen_slitPlane y hySlit
    have hComplement : AnalyticAt ℂ (fun z : ℂ => 1 - z) y :=
      analyticAt_const.sub analyticAt_id
    have houter : AnalyticAt ℂ outer y :=
      (Complex.differentiableOn_sqrt.analyticOnNhd Complex.isOpen_slitPlane
        (1 - y) hComplementSlit).comp hComplement
    have hinner : AnalyticAt ℂ inner y := analyticAt_const.mul hsqrt
    have hratio : AnalyticAt ℂ ratio y := hinner.div houter hout₀
    have hargMem : ratio y ^ (2 : ℕ) ∈ slitDomain := by
      apply ball_subset_slitDomain
      rw [hratioSq]
      exact mem_ball_zero_iff.mpr harg₁
    have hnum : AnalyticAt ℂ numerator (ratio y ^ (2 : ℕ)) :=
      (bSewnNumerator_differentiableOn L K J P R Q ((oscillatorLower ℒ ^ j) S) p r q d).analyticOnNhd
        isOpen_slitDomain _ hargMem
    have hnumAt : AnalyticAt ℂ (fun z : ℂ => numerator (ratio z ^ (2 : ℕ))) y :=
      hnum.comp (f := fun z : ℂ => ratio z ^ (2 : ℕ)) (hratio.pow 2)
    have hphase : AnalyticAt ℂ (fun _ : ℂ => phase) y := analyticAt_const
    exact (houter.zpow (n := (J : ℤ) - M - pole) hout₀).mul
      (((hratio.zpow (n := -pole) hratio₀).mul hphase).mul hnumAt)
  refine ⟨AnalyticOnNhd.congr isOpen_upperTransportDomain (fun y hy => (hlocal y hy).2) ?_, ?_⟩
  · intro y hy
    exact (hlocal y hy).1.tsum_eq.symm
  · exact fun y hy => (hlocal y hy).1.summable

set_option maxHeartbeats 1800000 in
-- Elaborate the finite translated sums and marked grade specializations.
/-- On the upper domain `y.re < 1 / 2`, the translated HBHB B sum
is the negative of the original HHBB B value. On the physical exterior
`1 < ‖y‖`, it also equals the translated HBHB A iterate. The target insertion
coordinates are `1 - y` and `-y`, with difference `1`. The actual B roots
are `sqrt (1 - y)` and `I * sqrt y`, and the actual A roots are `1` and
`I * sqrt y`. On the overlap both translated series have sum `-B₀ y`. -/
theorem hbhb_marked_upper_crossing {X : Type*} [Finite X]
    (slot : X → Puncture) (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X)
    (hl : l.Nodup) (hpar : MixedParity slot n l)
    (u v : TwistedEven) (w b : TwistedOdd) (p q r d : ActualGround ℒ leechUnit)
    (hu : u.val = wordAt ℒ slot colour n l .P ⊗ₜ[ℂ] p)
    (hv : v.val = wordAt ℒ slot colour n l .Q ⊗ₜ[ℂ] q)
    (hw : w.val = wordAt ℒ slot colour n l .R ⊗ₜ[ℂ] r)
    (hb : b.val = wordAt ℒ slot colour n l .S ⊗ₜ[ℂ] d) :
    let H (i : Puncture) := (doubledOccupation slot n l i).toNat
    let V := wordAt ℒ slot colour n l
    let M := H .P
    let K := H .Q
    let L := H .R
    let N := H .S
    let B₀ (y : ℂ) := Complex.sqrt y ^ (-(6 + (K : ℤ) + L)) *
      I ^ ((L : ℤ) + N - M - 2 * (K : ℤ) - 3) *
      bSewnNumerator K L N (V .P) (V .Q) (V .R) (V .S) p q r d y
    let S (j : ℕ) := (L₁ true ^ j) b
    let bTerm (j : ℕ) (y : ℂ) := bJointTerm true false w (swapInput (s := false) v) u (S j)
      (Complex.sqrt (1 - y)) (I * Complex.sqrt y)
    let aTerm (j : ℕ) (y : ℂ) := aJointTerm false u w v.val (S j).val 1 (I * Complex.sqrt y)
    let B (y : ℂ) := ∑ j ∈ Finset.range (N / 2 + 1),
      (y ^ j / (j.factorial : ℂ)) * (∑' i : ℤ × ℤ, bTerm j y i)
    let A (y : ℂ) := ∑ j ∈ Finset.range (N / 2 + 1),
      (y ^ j / (j.factorial : ℂ)) * (∑' i : ℤ × ℤ, aTerm j y i)
    AnalyticOnNhd ℂ B upperTransportDomain ∧ EqOn B (-B₀) upperTransportDomain ∧
      ∀ y ∈ upperTransportDomain, 1 < ‖y‖ →
        A y = B y ∧
          (∀ j ∈ Finset.range (N / 2 + 1), Summable (aTerm j y) ∧ Summable (bTerm j y)) ∧
          HasSum (fun i => ∑ j ∈ Finset.range (N / 2 + 1),
            (y ^ j / (j.factorial : ℂ)) * aTerm j y i) (-(B₀ y)) ∧
          HasSum (fun i => ∑ j ∈ Finset.range (N / 2 + 1),
            (y ^ j / (j.factorial : ℂ)) * bTerm j y i) (-(B₀ y)) := by
  let G := doubledOccupation slot n l
  let H (i : Puncture) := (G i).toNat
  let V := wordAt ℒ slot colour n l
  let M := H .P
  let K := H .Q
  let L := H .R
  let N := H .S
  let B₀ (y : ℂ) := Complex.sqrt y ^ (-(6 + (K : ℤ) + L)) *
    I ^ ((L : ℤ) + N - M - 2 * (K : ℤ) - 3) *
    bSewnNumerator K L N (V .P) (V .Q) (V .R) (V .S) p q r d y
  let D₀ (y : ℂ) := y ^ (-sigma (M : ℤ) K L N) *
    dSlitProduct M K L N (V .P) (V .Q) (V .R) (V .S) p q r d y⁻¹
  let S (j : ℕ) := (L₁ true ^ j) b
  let bTerm (j : ℕ) (y : ℂ) := bJointTerm true false w (swapInput (s := false) v) u (S j)
    (Complex.sqrt (1 - y)) (I * Complex.sqrt y)
  let aTerm (j : ℕ) (y : ℂ) := aJointTerm false u w v.val (S j).val 1 (I * Complex.sqrt y)
  let B (y : ℂ) := ∑ j ∈ Finset.range (N / 2 + 1),
    (y ^ j / (j.factorial : ℂ)) * (∑' i : ℤ × ℤ, bTerm j y i)
  let A (y : ℂ) := ∑ j ∈ Finset.range (N / 2 + 1),
    (y ^ j / (j.factorial : ℂ)) * (∑' i : ℤ × ℤ, aTerm j y i)
  change AnalyticOnNhd ℂ B upperTransportDomain ∧ EqOn B (-B₀) upperTransportDomain ∧
    ∀ y ∈ upperTransportDomain, 1 < ‖y‖ →
      A y = B y ∧
        (∀ j ∈ Finset.range (N / 2 + 1), Summable (aTerm j y) ∧ Summable (bTerm j y)) ∧
        HasSum (fun i => ∑ j ∈ Finset.range (N / 2 + 1),
          (y ^ j / (j.factorial : ℂ)) * aTerm j y i) (-(B₀ y)) ∧
        HasSum (fun i => ∑ j ∈ Finset.range (N / 2 + 1),
          (y ^ j / (j.factorial : ℂ)) * bTerm j y i) (-(B₀ y))
  have hH (i : Puncture) := occupationGrade_eq slot colour n l i
  have hG (i : Puncture) : (H i : ℤ) = G i := by
    change (((G i).toNat : ℕ) : ℤ) = G i
    rw [hH i, punctureExcitation_cast]
  have hM : (M : ℤ) % 2 = 0 := by simpa only [M, hG] using hpar.1
  have hK : (K : ℤ) % 2 = 0 := by simpa only [K, hG] using hpar.2.1
  have hL : (L : ℤ) % 2 = 1 := by simpa only [L, hG] using hpar.2.2.1
  have hN : (N : ℤ) % 2 = 1 := by simpa only [N, hG] using hpar.2.2.2
  have hKL : Odd ((K : ℤ) + L) := Int.odd_iff.mpr (by omega)
  have hNM : Odd ((N : ℤ) - M) := Int.odd_iff.mpr (by omega)
  have hsign : (-1 : ℂ) ^ (3 + K) = -1 := by
    have hodd : Odd (3 + K) := Nat.odd_iff.mpr (by omega)
    exact hodd.neg_one_pow
  have hGrade (i : Puncture) (g : ActualGround ℒ leechUnit) :
      V i ⊗ₜ[ℂ] g ∈ actualGrade ℒ leechUnit (H i) := by
    rw [show H i = _ from hH i]
    exact wordAt_grade slot colour n l i g
  have huGrade : u.val ∈ actualGrade ℒ leechUnit M := by
    rw [hu]
    exact hGrade .P p
  have hvGrade : v.val ∈ actualGrade ℒ leechUnit K := by
    rw [hv]
    exact hGrade .Q q
  have hwGrade : w.val ∈ actualGrade ℒ leechUnit L := by
    rw [hw]
    exact hGrade .R r
  have hbGrade : b.val ∈ actualGrade ℒ leechUnit N := by
    rw [hb]
    exact hGrade .S d
  have hDesc (j : ℕ) (hj : j ∈ Finset.range (N / 2 + 1)) :
      AnalyticOnNhd ℂ (fun y => ∑' i : ℤ × ℤ, bTerm j y i) upperTransportDomain ∧
        ∀ y ∈ upperTransportDomain, Summable (bTerm j y) :=
    hbhb_target_b_descendant_holomorphic M K L N j u v w b (V .P) (V .Q) (V .R) (V .S)
      p q r d huGrade hvGrade hwGrade hbGrade hu hv hw hb hKL hNM
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  have hB : AnalyticOnNhd ℂ B upperTransportDomain := by
    intro y hy
    refine Finset.analyticAt_fun_sum (Finset.range (N / 2 + 1)) fun j hj => ?_
    have hWeight : AnalyticAt ℂ (fun z : ℂ => z ^ j / (j.factorial : ℂ)) y :=
      ((analyticAt_id (z := y)).pow j).div_const
    exact hWeight.mul ((hDesc j hj).1 y hy)
  have hBD := hhbb_marked_rawD_eq_neg_rawB_upper_half_plane slot colour n l hl hpar
    u v w b p q r d hu hv hw hb
  have hB₀ : AnalyticOnNhd ℂ B₀ upperTransportDomain := hBD.1.mono (fun _ hy => hy.1)
  have hSource {y : ℂ} (hy : ‖y‖ < 1) :
      HasSum (bJointTerm false false v w u b 1 (Complex.sqrt y)) (B₀ y) :=
    (hhbb_marked_b_slit_extension slot colour n l hpar u v w b p q r d hu hv hw hb).2 hy
  let y₀ : ℂ := ⟨0, 1 / 4⟩
  have hy₀ : y₀ ∈ upperTransportDomain := by
    constructor
    · change (0 : ℝ) < 1 / 4
      norm_num
    · change (0 : ℝ) < 1 / 2
      norm_num
  have hy₀Ball : y₀ ∈ Metric.ball (0 : ℂ) (1 / 2) := by
    apply mem_ball_zero_iff.mpr
    apply (sq_lt_sq₀ (norm_nonneg y₀) (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp
    rw [Complex.sq_norm, Complex.normSq_apply]
    change (0 : ℝ) * 0 + (1 / 4) * (1 / 4) < (1 / 2) ^ (2 : ℕ)
    norm_num
  have hnear : ∀ᶠ y in 𝓝 y₀, y ∈ upperTransportDomain ∩ Metric.ball (0 : ℂ) (1 / 2) :=
    (isOpen_upperTransportDomain.inter Metric.isOpen_ball).mem_nhds ⟨hy₀, hy₀Ball⟩
  have hgerm : B =ᶠ[𝓝 y₀] -B₀ := by
    filter_upwards [hnear] with y hy
    have hsmall : ‖y‖ < (1 / 2 : ℝ) := mem_ball_zero_iff.mp hy.2
    have hyNe : y ≠ 0 := Complex.slitPlane_ne_zero (source_mem_slit hy.1.1)
    have hSlot := b_joint_product_hasSum_slot23 false false M K L N v w u b
      hvGrade hwGrade huGrade hbGrade hKL hNM hyNe hsmall
    change HasSum (bJointTerm false false v w u b 1 (Complex.sqrt y))
      ((-1 : ℂ) ^ (3 + K) * B y) at hSlot
    rw [hsign, neg_one_mul] at hSlot
    have heq : -(B y) = B₀ y := hSlot.unique (hSource (hsmall.trans (by norm_num)))
    change B y = -(B₀ y)
    rw [← heq, neg_neg]
  have hPreconnected : IsPreconnected upperTransportDomain :=
    ((convex_halfSpace_im_gt (0 : ℝ)).inter (convex_halfSpace_re_lt (1 / 2 : ℝ))).isPreconnected
  have hEq : EqOn B (-B₀) upperTransportDomain :=
    hB.eqOn_of_preconnected_of_eventuallyEq hB₀.neg hPreconnected hy₀ hgerm
  refine ⟨hB, hEq, ?_⟩
  intro y hy hExterior
  have him : 0 < y.im := hy.1
  have hRootSq : ‖Complex.sqrt y‖ ^ (2 : ℕ) = ‖y‖ := by rw [← norm_pow, sqrt_square]
  have hRad : ‖(1 : ℂ)‖ < ‖Complex.sqrt y‖ := by
    rw [norm_one]
    apply (sq_lt_sq₀ (zero_le_one : (0 : ℝ) ≤ 1) (norm_nonneg (Complex.sqrt y))).mp
    rw [one_pow, hRootSq]
    exact hExterior
  have hRoot : Complex.sqrt y ≠ 0 := norm_pos_iff.mp ((by simp : 0 < ‖(1 : ℂ)‖).trans hRad)
  have hRaw := (hhbb_marked_rawD_hasSum_upper_exterior slot colour n l hpar
    u v w b p q r d hu hv hw hb him hExterior).1
  change HasSum (bJointTerm false false u w v b (Complex.sqrt y) 1) (D₀ y) at hRaw
  have hRawEq : D₀ y = -(B₀ y) := hBD.2.2 him
  have hCross := mixed_d_joint_hasSum_crossed_a false false M L K N u w v b
    huGrade hwGrade hvGrade hbGrade one_ne_zero hRoot hRad
  simp only [pow_mul, sqrt_square] at hCross
  change HasSum (bJointTerm false false u w v b (Complex.sqrt y) 1) (A y) at hCross
  have hAValue : A y = -(B₀ y) := (hCross.unique hRaw).trans hRawEq
  have hRadA : ‖(1 : ℂ)‖ < ‖I * Complex.sqrt y‖ := by
    simpa only [norm_mul, Complex.norm_I, one_mul] using hRad
  have hSums (j : ℕ) (hj : j ∈ Finset.range (N / 2 + 1)) :
      Summable (aTerm j y) ∧ Summable (bTerm j y) := by
    have hj' : j ≤ N / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact ⟨mixed_a_joint_summable_of_homogeneous false false M L K (N - 2 * j) u w v (S j)
      huGrade hwGrade hvGrade (lowered_grade (s := true) (u := b) hbGrade hj') one_ne_zero hRadA,
      (hDesc j hj).2 y hy⟩
  refine ⟨hAValue.trans (hEq hy).symm, hSums, ?_, ?_⟩
  · rw [← hAValue]
    exact hasSum_sum (s := Finset.range (N / 2 + 1)) fun j hj =>
      (hSums j hj).1.hasSum.mul_left _
  · have hBValue : B y = -(B₀ y) := hEq hy
    rw [← hBValue]
    exact hasSum_sum (s := Finset.range (N / 2 + 1)) fun j hj =>
      (hSums j hj).2.hasSum.mul_left _

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHBHBUpperCrossing
