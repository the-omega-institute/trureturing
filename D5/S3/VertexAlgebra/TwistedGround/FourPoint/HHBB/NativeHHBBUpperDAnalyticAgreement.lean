/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/HHBB/NativeHHBBUpperDAnalyticAgreement
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The native Leech HHBB A iterate agrees with the D continuation on the upper physical lens. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedComplexSewing

/-! The marked HHBB A iterate and native upper D continuation agree on the
upper part of the physical lens. Inversion maps the upper physical half-plane
to the lower half-plane in the D coordinate, which is `dLip true`. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped TensorProduct Topology
open Filter Metric Set

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBUpperDAnalyticAgreement

open ActualLeechHyperbolic (leechData)
open LatticeHalfFockChargedTensorCoefficients (ActualGround)
open Orbifold.NativeOddTwistedIntertwiner (TwistedEven TwistedOdd leechUnit)
open NativeFixedPairAIterate (fixedAIterate_hasSum_on_overlap fixedA_laurentRoot fixedASlitSewn)
open NativeMixedComplexSewing (aJointTerm hhbb_actual_complex_sewing)
open NativeMixedPhysicalOverlap (hhbb_actual_A_eq_upper_D_limit)
open NativeMixedUpperDLip (dLaurentRoot dLaurentRoot_eq_cpow dLipProduct
  dLipProduct_analyticAt dLipProduct_eq_slit dSlitProduct dSlitProduct_analyticOnNhd
  dSlitProduct_tendsto_dLip)
open NativeMixedUpperProductCusp (bJointTerm bSewnNumerator)
open NativeMixedWickChartTransport (MixedParity doubledOccupation sigma)
open OriginalFourMActualChart (Puncture parameter)
open OriginalFourMPeriodSource (dLip dLip_mem_doubleSlit)
open OriginalFourMVariableSupport (wordAt)

open private a_lens_analytic cap_ratio sqrt_square zpow_double from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedComplexSewing
open private fixedASlitSewn_differentiableOn from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedPairAIterate
open private occupationGrade_eq from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedPhysicalOverlap
open private punctureExcitation_cast wordAt_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedUpperProductCusp
open private dLip_neBot isOpen_dLip from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPeriodSource

local notation "ℒ" => leechData

/-- The open physical lens on the side selecting the native upper D lift. -/
def upperCap : Set ℂ :=
  (ball (0 : ℂ) 1 ∩ {y | (1 / 2 : ℝ) < y.re}) ∩ dLip false

theorem isOpen_upperCap : IsOpen upperCap :=
  (isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)).inter
    (isOpen_dLip false)

private theorem upperCap_preconnected : IsPreconnected upperCap :=
  (((convex_ball (0 : ℂ) 1).inter (convex_halfSpace_re_gt (1 / 2 : ℝ))).inter
    (convex_halfSpace_im_gt (0 : ℝ))).isPreconnected

private theorem inv_mem_upperDLip {y : ℂ} (hy : 0 < y.im) : y⁻¹ ∈ dLip true := by
  have hy₀ : y ≠ 0 := by
    rintro rfl
    simp at hy
  change y⁻¹.im < 0
  rw [Complex.inv_im]
  exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hy) (Complex.normSq_pos.mpr hy₀)

set_option maxHeartbeats 4000000 in
/-- The unscaled native A expression agrees as a complex germ with the D lip
representative composed with inversion at every real center in `(1/2, 1)`.
On the entire open upper cap it agrees with the slit D product in its native
order `(P, R, Q, S)`, with positive relative sign. -/
theorem hhbb_actual_upper_D_analytic_agreement {X : Type*} [Finite X]
    (slot : X → Puncture) (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X)
    (hl : l.Nodup) (hpar : MixedParity slot n l)
    (u v : TwistedEven) (w b : TwistedOdd) (p q r d : ActualGround ℒ leechUnit)
    (hu : u.val = wordAt ℒ slot colour n l .P ⊗ₜ[ℂ] p)
    (hv : v.val = wordAt ℒ slot colour n l .Q ⊗ₜ[ℂ] q)
    (hw : w.val = wordAt ℒ slot colour n l .R ⊗ₜ[ℂ] r)
    (hb : b.val = wordAt ℒ slot colour n l .S ⊗ₜ[ℂ] d) :
    let H (i : Puncture) := (doubledOccupation slot n l i).toNat
    let V := wordAt ℒ slot colour n l
    let A (y : ℂ) := ((1 - y) / y) ^ (-(((H .P : ℤ) + H .Q + 6) / 2)) *
      fixedASlitSewn (H .P) (H .Q) (V .P) (V .Q) (V .R) (V .S) p q r d (-((1 - y) / y))
    let D (y : ℂ) := dSlitProduct (H .P) (H .Q) (H .R) (H .S)
      (V .P) (V .Q) (V .R) (V .S) p q r d y⁻¹
    let DLip (y : ℂ) := dLipProduct (H .P) (H .Q) (H .R) (H .S)
      (V .P) (V .Q) (V .R) (V .S) p q r d y⁻¹
    (∀ y₀ : ℝ, (1 / 2 : ℝ) < y₀ → y₀ < 1 → A =ᶠ[𝓝 (y₀ : ℂ)] DLip) ∧
      AnalyticOnNhd ℂ A upperCap ∧ AnalyticOnNhd ℂ D upperCap ∧ EqOn A D upperCap := by
  let H (i : Puncture) := (doubledOccupation slot n l i).toNat
  let V := wordAt ℒ slot colour n l
  let M := H .P
  let K := H .Q
  let L := H .R
  let N := H .S
  let a : ℤ := ((M : ℤ) + K + 6) / 2
  let t (y : ℂ) := (1 - y) / y
  let ANum := fixedASlitSewn M K (V .P) (V .Q) (V .R) (V .S) p q r d
  let A (y : ℂ) := t y ^ (-a) * ANum (-(t y))
  let DSlit := dSlitProduct M K L N (V .P) (V .Q) (V .R) (V .S) p q r d
  let D (y : ℂ) := DSlit y⁻¹
  let DLip (y : ℂ) := dLipProduct M K L N (V .P) (V .Q) (V .R) (V .S) p q r d y⁻¹
  change (∀ y₀ : ℝ, (1 / 2 : ℝ) < y₀ → y₀ < 1 → A =ᶠ[𝓝 (y₀ : ℂ)] DLip) ∧
    AnalyticOnNhd ℂ A upperCap ∧ AnalyticOnNhd ℂ D upperCap ∧ EqOn A D upperCap
  have hH (i : Puncture) := occupationGrade_eq slot colour n l i
  have hG (i : Puncture) : (H i : ℤ) = doubledOccupation slot n l i := by
    change (((doubledOccupation slot n l i).toNat : ℕ) : ℤ) = _
    rw [hH i, punctureExcitation_cast]
  have hM : (M : ℤ) % 2 = 0 := by simpa only [M, hG] using hpar.1
  have hK : (K : ℤ) % 2 = 0 := by simpa only [K, hG] using hpar.2.1
  have hMK : Even ((M : ℤ) + K) := Int.even_iff.mpr (by omega)
  have hExp : -((M : ℤ) + K + 6) = 2 * (-a) := by
    dsimp only [a]
    omega

  have hReal (y : ℝ) (hy : (1 / 2 : ℝ) < y) (hy₁ : y < 1) :
      A (y : ℂ) = DLip (y : ℂ) := by
    have hyPos : 0 < y := by linarith
    have hy₀ : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hyPos.ne'
    have hLimitA := hhbb_actual_A_eq_upper_D_limit slot colour n l hl hpar
      u v w b p q r d hu hv hw hb hy hy₁
    have hLimitD := dSlitProduct_tendsto_dLip M K L N (V .P) (V .Q) (V .R) (V .S)
      p q r d ((one_lt_inv₀ hyPos).2 hy₁)
    have hDCoord : ((y⁻¹ : ℝ) : ℂ) = parameter .D (y : ℂ) := Complex.ofReal_inv y
    rw [hDCoord] at hLimitD
    let : (𝓝[dLip true] (parameter .D (y : ℂ))).NeBot := by
      rw [← hDCoord]
      exact dLip_neBot true y⁻¹
    have hLimitEq := tendsto_nhds_unique hLimitA hLimitD

    have hSum := fixedAIterate_hasSum_on_overlap false M K L N
      u v (V .P) (V .Q) (V .R) (V .S) p q r d
      (by rw [hu, show M = _ from hH .P]; exact wordAt_grade slot colour n l .P p)
      (by rw [hv, show K = _ from hH .Q]; exact wordAt_grade slot colour n l .Q q)
      hu hv
      (by rw [show L = _ from hH .R]; exact wordAt_grade slot colour n l .R r)
      (by rw [show N = _ from hH .S]; exact wordAt_grade slot colour n l .S d)
      hMK hy hy₁
    have hACoord : parameter .A (y : ℂ) = -(t (y : ℂ)) := by
      change 1 - (y : ℂ)⁻¹ = -((1 - (y : ℂ)) / (y : ℂ))
      simp only [sub_div, div_self hy₀, one_div, neg_sub]
    have hRoot : NativeMixedWickChartTransport.laurentRoot .A y ^ (2 : ℕ) = t (y : ℂ) := by
      rw [(fixedA_laurentRoot hy hy₁).2.2, hACoord, neg_neg]
    dsimp only at hSum
    rw [← hw, ← hb, hExp, zpow_double, hRoot, hACoord] at hSum
    exact hSum.tsum_eq.symm.trans hLimitEq

  have hAnalyticA (y : ℂ) (hy : ‖y‖ < 1) (hre : (1 / 2 : ℝ) < y.re) :
      AnalyticAt ℂ A y := by
    simpa only [A, t, neg_zero, zpow_zero, one_mul] using
      a_lens_analytic ANum 0 a hy hre
        (fixedASlitSewn_differentiableOn M K (V .P) (V .Q) (V .R) (V .S) p q r d)

  have hGerm (y₀ : ℝ) (hy₀ : (1 / 2 : ℝ) < y₀) (hy₁ : y₀ < 1) :
      A =ᶠ[𝓝 (y₀ : ℂ)] DLip := by
    have hyPos : 0 < y₀ := by linarith
    have hyNorm : ‖(y₀ : ℂ)‖ < 1 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hyPos] using hy₁
    have hyRe : (1 / 2 : ℝ) < (y₀ : ℂ).re := by simpa only [Complex.ofReal_re] using hy₀
    have hLipAnalytic : AnalyticAt ℂ DLip (y₀ : ℂ) := by
      have hLip := dLipProduct_analyticAt M K L N (V .P) (V .Q) (V .R) (V .S) p q r d
        ((one_lt_inv₀ hyPos).2 hy₁)
      rw [Complex.ofReal_inv] at hLip
      exact hLip.comp (analyticAt_inv (Complex.ofReal_ne_zero.mpr hyPos.ne'))
    have hCast : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[≠] y₀) (𝓝[≠] (y₀ : ℂ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        simpa only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_inj] using hs
    have hRealNear : ∀ᶠ y : ℝ in 𝓝 y₀, A (y : ℂ) = DLip (y : ℂ) :=
      (show ∀ᶠ y in 𝓝 y₀, y ∈ Ioo (1 / 2 : ℝ) 1 from Ioo_mem_nhds hy₀ hy₁).mono
        fun y hy => hReal y hy.1 hy.2
    have hFrequent : ∃ᶠ y in 𝓝[≠] (y₀ : ℂ), A y = DLip y :=
      hCast.frequently (hRealNear.filter_mono nhdsWithin_le_nhds).frequently
    exact ((hAnalyticA _ hyNorm hyRe).frequently_eq_iff_eventually_eq hLipAnalytic).mp hFrequent

  have hA : AnalyticOnNhd ℂ A upperCap := fun y hy =>
    hAnalyticA y (mem_ball_zero_iff.mp hy.1.1) hy.1.2
  have hD : AnalyticOnNhd ℂ D upperCap := by
    intro y hy
    have hy₀ := (cap_ratio (mem_ball_zero_iff.mp hy.1.1) hy.1.2).1
    exact (dSlitProduct_analyticOnNhd M K L N (V .P) (V .Q) (V .R) (V .S) p q r d _
      (dLip_mem_doubleSlit (inv_mem_upperDLip hy.2))).comp (analyticAt_inv hy₀)
  refine ⟨hGerm, hA, hD, ?_⟩

  let y₀ : ℝ := 3 / 4
  have hy₀ : (1 / 2 : ℝ) < y₀ := by norm_num [y₀]
  have hy₁ : y₀ < 1 := by norm_num [y₀]
  have hUpperGerm : A =ᶠ[𝓝[dLip false] (y₀ : ℂ)] D := by
    filter_upwards [(hGerm y₀ hy₀ hy₁).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with y he hy
    exact he.trans (dLipProduct_eq_slit M K L N (V .P) (V .Q) (V .R) (V .S) p q r d
      (inv_mem_upperDLip hy))
  let lens : Set ℂ := ball 0 1 ∩ {y | (1 / 2 : ℝ) < y.re}
  have hLensOpen : IsOpen lens := isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hCenter : (y₀ : ℂ) ∈ lens := by
    change (y₀ : ℂ) ∈ ball 0 1 ∧ (1 / 2 : ℝ) < (y₀ : ℂ).re
    norm_num [Metric.mem_ball, y₀, Complex.norm_real]
  have hLensNear : ∀ᶠ y in 𝓝[dLip false] (y₀ : ℂ), y ∈ lens :=
    (show ∀ᶠ y in 𝓝 (y₀ : ℂ), y ∈ lens from hLensOpen.mem_nhds hCenter).filter_mono
      nhdsWithin_le_nhds
  let : (𝓝[dLip false] (y₀ : ℂ)).NeBot := dLip_neBot false y₀
  obtain ⟨z, hzEq, hzLens, hzUpper⟩ :=
    ((eventually_eventually_nhdsWithin.mpr hUpperGerm).and
      (hLensNear.and self_mem_nhdsWithin)).exists
  rw [(isOpen_dLip false).nhdsWithin_eq hzUpper] at hzEq
  exact hA.eqOn_of_preconnected_of_eventuallyEq hD upperCap_preconnected
    (show z ∈ upperCap from ⟨hzLens, hzUpper⟩) hzEq

set_option maxHeartbeats 4000000 in
/-- Physical specialization at `xRoot = 1`, with the principal square roots
in A and B. The D argument is `y⁻¹` on `dLip true` and the Laurent root
is the principal square root of `-y⁻¹`. The raw D value includes the same
outer factor `y^(-sigma)` as A. The marked joint sums have values `D` and
`-D` in A and B respectively. -/
theorem hhbb_actual_upper_D_physical_agreement {X : Type*} [Finite X]
    (slot : X → Puncture) (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X)
    (hl : l.Nodup) (hpar : MixedParity slot n l)
    (u v : TwistedEven) (w b : TwistedOdd) (p q r d : ActualGround ℒ leechUnit)
    (hu : u.val = wordAt ℒ slot colour n l .P ⊗ₜ[ℂ] p)
    (hv : v.val = wordAt ℒ slot colour n l .Q ⊗ₜ[ℂ] q)
    (hw : w.val = wordAt ℒ slot colour n l .R ⊗ₜ[ℂ] r)
    (hb : b.val = wordAt ℒ slot colour n l .S ⊗ₜ[ℂ] d)
    {y : ℂ} (hy : ‖y‖ < 1) (hre : (1 / 2 : ℝ) < y.re) (him : 0 < y.im) :
    let H (i : Puncture) := (doubledOccupation slot n l i).toNat
    let V := wordAt ℒ slot colour n l
    let M := H .P
    let K := H .Q
    let L := H .R
    let N := H .S
    let s := sigma (M : ℤ) K L N
    let t := (1 - y) / y
    let rawD := y ^ (-s) * dSlitProduct M K L N (V .P) (V .Q) (V .R) (V .S) p q r d y⁻¹
    let B := Complex.sqrt y ^ (-(6 + (K : ℤ) + L)) *
      Complex.I ^ ((L : ℤ) + N - M - 2 * (K : ℤ) - 3) *
      bSewnNumerator K L N (V .P) (V .Q) (V .R) (V .S) p q r d y
    y⁻¹ ∈ dLip true ∧ dLaurentRoot y⁻¹ = (-(y⁻¹)) ^ (1 / 2 : ℂ) ∧
      y ^ (-s) * (t ^ (-(((M : ℤ) + K + 6) / 2)) *
        fixedASlitSewn M K (V .P) (V .Q) (V .R) (V .S) p q r d (-t)) = rawD ∧
      rawD = -B ∧
      HasSum (aJointTerm u v w b (Complex.sqrt y * Complex.sqrt t) (Complex.sqrt y)) rawD ∧
      HasSum (bJointTerm false false v w u b 1 (Complex.sqrt y)) (-rawD) := by
  dsimp only
  have hLip := inv_mem_upperDLip him
  have hCap : y ∈ upperCap := ⟨⟨mem_ball_zero_iff.mpr hy, hre⟩, him⟩
  have hNormalized :=
    (hhbb_actual_upper_D_analytic_agreement slot colour n l hl hpar
      u v w b p q r d hu hv hw hb).2.2.2 hCap
  dsimp only at hNormalized
  have hSew := hhbb_actual_complex_sewing slot colour n l hl hpar u v w b p q r d
    hu hv hw hb (xRoot := 1) (ξ := Complex.sqrt ((1 - y) / y))
    one_ne_zero hy hre (sqrt_square _)
  dsimp only at hSew
  simp only [one_pow, one_mul, one_zpow] at hSew
  obtain ⟨_, _, _, hAB, hASum, hBSum⟩ := hSew
  refine ⟨hLip, dLaurentRoot_eq_cpow hLip, ?_, ?_, ?_, ?_⟩
  · rw [hNormalized]
  · rw [← hNormalized]
    exact hAB
  · rw [← hNormalized, hAB]
    exact hASum
  · rw [← hNormalized, hAB, neg_neg]
    exact hBSum

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBUpperDAnalyticAgreement
