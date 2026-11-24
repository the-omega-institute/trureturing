import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBUpperDAnalyticAgreement
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBBSlitExtension

/-! Analytic agreement of the raw HHBB B and D products on the upper half-plane. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped TensorProduct Topology
open Filter Metric Set

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBUpperHalfPlaneBD

open ActualLeechHyperbolic (leechData)
open LatticeHalfFockChargedTensorCoefficients (ActualGround)
open LatticeHalfFockGradedTrace (actualGrade)
open Orbifold.NativeOddTwistedIntertwiner (TwistedEven TwistedOdd leechUnit)
open NativeHHBBBSlitExtension (hhbb_marked_b_slit_extension)
open NativeHHBBUpperDAnalyticAgreement
  (hhbb_actual_upper_D_physical_agreement isOpen_upperCap upperCap)
open NativeMixedUpperDLip (dProductCoeff dSlitProduct dSlitProduct_analyticOnNhd)
open NativeMixedUpperProductCusp
  (bJointTerm bSewnNumerator b_joint_product_hasSum b_product_hasSum_complex)
open NativeMixedWickChartTransport (MixedParity bpzPhase doubledOccupation sigma)
open OriginalFourMActualChart (Puncture)
open OriginalFourMPeriodSource (dLip dLip_mem_doubleSlit)
open OriginalFourMVariableSupport (wordAt)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod (doubleSlit)

open private sqrt_square square_root_disk zpow_double from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedComplexSewing
open private occupationGrade_eq from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedPhysicalOverlap
open private punctureExcitation_cast wordAt_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedUpperProductCusp

local notation "ℒ" => leechData

set_option maxHeartbeats 4000000 in
-- Unfolding the native product at the marked grades uses extra heartbeats.
/-- At outer root one, the marked HHBB raw B value uses the principal
square root of `y`. The raw D value uses the inverted slit argument and
carries the homogeneous factor `y ^ (-sigma)`. Both are analytic throughout
the open upper half-plane, where the raw D value equals the negative of the
raw B value. -/
theorem hhbb_marked_rawD_eq_neg_rawB_upper_half_plane {X : Type*} [Finite X]
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
    let s := sigma (M : ℤ) K L N
    let B (y : ℂ) := Complex.sqrt y ^ (-(6 + (K : ℤ) + L)) *
      Complex.I ^ ((L : ℤ) + N - M - 2 * (K : ℤ) - 3) *
      bSewnNumerator K L N (V .P) (V .Q) (V .R) (V .S) p q r d y
    let D (y : ℂ) := y ^ (-s) * dSlitProduct M K L N (V .P) (V .Q) (V .R) (V .S) p q r d y⁻¹
    let upper : Set ℂ := {y | 0 < y.im}
    AnalyticOnNhd ℂ B upper ∧ AnalyticOnNhd ℂ D upper ∧ EqOn D (-B) upper := by
  let H (i : Puncture) := (doubledOccupation slot n l i).toNat
  let V := wordAt ℒ slot colour n l
  let M := H .P
  let K := H .Q
  let L := H .R
  let N := H .S
  let s := sigma (M : ℤ) K L N
  let B (y : ℂ) := Complex.sqrt y ^ (-(6 + (K : ℤ) + L)) *
    Complex.I ^ ((L : ℤ) + N - M - 2 * (K : ℤ) - 3) *
    bSewnNumerator K L N (V .P) (V .Q) (V .R) (V .S) p q r d y
  let DSlit := dSlitProduct M K L N (V .P) (V .Q) (V .R) (V .S) p q r d
  let D (y : ℂ) := y ^ (-s) * DSlit y⁻¹
  let upper : Set ℂ := {y | 0 < y.im}
  change AnalyticOnNhd ℂ B upper ∧ AnalyticOnNhd ℂ D upper ∧ EqOn D (-B) upper
  have hBSlit : AnalyticOnNhd ℂ B doubleSlit :=
    (hhbb_marked_b_slit_extension slot colour n l hpar u v w b p q r d hu hv hw hb).1
  have hB : AnalyticOnNhd ℂ B upper := hBSlit.mono fun _ hy =>
    dLip_mem_doubleSlit (upperA := false) hy
  have hDSlit : AnalyticOnNhd ℂ DSlit doubleSlit :=
    dSlitProduct_analyticOnNhd M K L N (V .P) (V .Q) (V .R) (V .S) p q r d
  have hD : AnalyticOnNhd ℂ D upper := by
    intro y hy
    have him : 0 < y.im := hy
    have hy₀ : y ≠ 0 := by
      rintro rfl
      simp at him
    have hinv : y⁻¹ ∈ dLip true := by
      change (y⁻¹).im < 0
      rw [Complex.inv_im]
      exact div_neg_of_neg_of_pos (neg_lt_zero.mpr him) (Complex.normSq_pos.mpr hy₀)
    have hcomp := (hDSlit _ (dLip_mem_doubleSlit hinv)).comp (analyticAt_inv hy₀)
    exact ((analyticAt_id (z := y)).zpow (n := -s) hy₀).mul hcomp
  let y₀ : ℂ := ⟨3 / 4, 1 / 4⟩
  have hy₀norm : ‖y₀‖ < 1 := by
    apply (sq_lt_sq₀ (norm_nonneg y₀) (zero_le_one : (0 : ℝ) ≤ 1)).mp
    rw [Complex.sq_norm, Complex.normSq_apply]
    change (3 / 4 : ℝ) * (3 / 4) + (1 / 4) * (1 / 4) < 1 ^ (2 : ℕ)
    norm_num
  have hy₀re : (1 / 2 : ℝ) < y₀.re := by
    change (1 / 2 : ℝ) < 3 / 4
    norm_num
  have hy₀im : 0 < y₀.im := by
    change (0 : ℝ) < 1 / 4
    norm_num
  have hy₀cap : y₀ ∈ upperCap := ⟨⟨mem_ball_zero_iff.mpr hy₀norm, hy₀re⟩, hy₀im⟩
  have hnear : ∀ᶠ y in 𝓝 y₀, y ∈ upperCap := isOpen_upperCap.mem_nhds hy₀cap
  have hgerm : D =ᶠ[𝓝 y₀] -B := by
    filter_upwards [hnear] with y hy
    exact (hhbb_actual_upper_D_physical_agreement slot colour n l hl hpar
      u v w b p q r d hu hv hw hb (mem_ball_zero_iff.mp hy.1.1) hy.1.2 hy.2).2.2.2.1
  have hupper : IsPreconnected upper := (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected
  exact ⟨hB, hD, hD.eqOn_of_preconnected_of_eventuallyEq hB.neg hupper hy₀im hgerm⟩

set_option maxHeartbeats 4000000 in
-- Unfolding the native product at the marked grades uses extra heartbeats.
/-- On the upper exterior, the raw D value sums the doubled-mode product
in D order at the physical roots `sqrt y` and `1`. After removing the
homogeneous prefactor, the energy series in `d_upper_product_hasSum` sums
to the same unscaled slit product at the inverted coordinate. -/
theorem hhbb_marked_rawD_hasSum_upper_exterior {X : Type*}
    (slot : X → Puncture) (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X)
    (hpar : MixedParity slot n l)
    (u v : TwistedEven) (w b : TwistedOdd) (p q r d : ActualGround ℒ leechUnit)
    (hu : u.val = wordAt ℒ slot colour n l .P ⊗ₜ[ℂ] p)
    (hv : v.val = wordAt ℒ slot colour n l .Q ⊗ₜ[ℂ] q)
    (hw : w.val = wordAt ℒ slot colour n l .R ⊗ₜ[ℂ] r)
    (hb : b.val = wordAt ℒ slot colour n l .S ⊗ₜ[ℂ] d)
    {y : ℂ} (him : 0 < y.im) (hy : 1 < ‖y‖) :
    let H (i : Puncture) := (doubledOccupation slot n l i).toNat
    let V := wordAt ℒ slot colour n l
    let M := H .P
    let K := H .Q
    let L := H .R
    let N := H .S
    let s := sigma (M : ℤ) K L N
    let D := dSlitProduct M K L N (V .P) (V .Q) (V .R) (V .S) p q r d y⁻¹
    HasSum (bJointTerm false false u w v b (Complex.sqrt y) 1) (y ^ (-s) * D) ∧
      HasSum (fun E : ℕ => dProductCoeff false false M K L N u w v b E *
        ((y⁻¹) ^ (1 / 2 : ℂ)) ^ (2 * (E : ℤ) - (6 + (M : ℤ) + L))) D := by
  let G := doubledOccupation slot n l
  let H (i : Puncture) := (G i).toNat
  let V := wordAt ℒ slot colour n l
  let M := H .P
  let K := H .Q
  let L := H .R
  let N := H .S
  let s := sigma (M : ℤ) K L N
  let A : ℤ := 6 + (M : ℤ) + L
  let phase : ℤ := (L : ℤ) + N - K - 2 * (M : ℤ) - 3
  let F := bSewnNumerator M L N (V .Q) (V .P) (V .R) (V .S) q p r d
  let D := dSlitProduct M K L N (V .P) (V .Q) (V .R) (V .S) p q r d y⁻¹
  let ρ := (1 : ℂ) / Complex.sqrt y
  change HasSum (bJointTerm false false u w v b (Complex.sqrt y) 1) (y ^ (-s) * D) ∧
    HasSum (fun E : ℕ => dProductCoeff false false M K L N u w v b E *
      ((y⁻¹) ^ (1 / 2 : ℂ)) ^ (2 * (E : ℤ) - A)) D
  have hH (i : Puncture) := occupationGrade_eq slot colour n l i
  have hG (i : Puncture) : (H i : ℤ) = G i := by
    change (((G i).toNat : ℕ) : ℤ) = G i
    rw [hH i, punctureExcitation_cast]
  have hM : (M : ℤ) % 2 = 0 := by simpa only [M, hG] using hpar.1
  have hK : (K : ℤ) % 2 = 0 := by simpa only [K, hG] using hpar.2.1
  have hL : (L : ℤ) % 2 = 1 := by simpa only [L, hG] using hpar.2.2.1
  have hN : (N : ℤ) % 2 = 1 := by simpa only [N, hG] using hpar.2.2.2
  have hML : Odd ((M : ℤ) + L) := Int.odd_iff.mpr (by omega)
  have hNK : Odd ((N : ℤ) - K) := Int.odd_iff.mpr (by omega)
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
  have hdegree : (N : ℤ) - K - A = 2 * (-s) := by
    dsimp only [A, s, sigma]
    omega
  have hy₀ : y ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans hy)
  have hroot₀ : Complex.sqrt y ≠ 0 := fun h => hy₀ (by simpa [h] using (sqrt_square y).symm)
  have hyInv : ‖y⁻¹‖ < 1 := by
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ hy
  have hρSq : ρ ^ (2 : ℕ) = y⁻¹ := by
    rw [show ρ = (Complex.sqrt y)⁻¹ from one_div _, inv_pow, sqrt_square]
  obtain ⟨hρ₀, hρ₁⟩ := square_root_disk hρSq (inv_ne_zero hy₀) hyInv
  have hArg : y.arg ≠ Real.pi := fun h => him.ne' (Complex.arg_eq_pi_iff.mp h).2
  have hρ : ρ = (y⁻¹) ^ (1 / 2 : ℂ) := by
    simpa only [ρ, Complex.sqrt, one_div] using (Complex.inv_cpow y (1 / 2 : ℂ) hArg).symm
  have hPhase : Complex.I ^ (-A) * bpzPhase M K L N .D = Complex.I ^ phase := by
    rw [bpzPhase, ← zpow_add₀ Complex.I_ne_zero,
      show -A + (3 + 2 * (L : ℤ) + N - M - K) = phase by
        dsimp only [A, phase]
        ring]
  have hD : D = ρ ^ (-A) * Complex.I ^ phase * F y⁻¹ := by
    change (Complex.I * ((y⁻¹) ^ (1 / 2 : ℂ))) ^ (-A) *
      bpzPhase M K L N .D * F y⁻¹ = _
    rw [← hρ, mul_zpow, ← hPhase]
    ring
  have hJoint := b_joint_product_hasSum false false K M L N u w v b
    (V .Q) (V .P) (V .R) (V .S) q p r d huGrade hwGrade hvGrade hbGrade hu hw hv hb hML hNK
    (xRoot := Complex.sqrt y) (zRoot := 1) hroot₀ (norm_pos_iff.mpr hρ₀) hρ₁
  change HasSum (bJointTerm false false u w v b (Complex.sqrt y) 1)
    (Complex.sqrt y ^ ((N : ℤ) - K - A) * (ρ ^ (-A) * Complex.I ^ phase * F (ρ ^ 2))) at hJoint
  rw [hdegree, zpow_double, sqrt_square, hρSq, ← hD] at hJoint
  have hEnergy := b_product_hasSum_complex false false K M L N u w v b
    (V .Q) (V .P) (V .R) (V .S) q p r d huGrade hwGrade hvGrade hbGrade hu hw hv hb hML hNK
    (norm_pos_iff.mpr hρ₀) hρ₁
  change HasSum (fun E : ℕ => dProductCoeff false false M K L N u w v b E *
    ρ ^ (2 * (E : ℤ) - A)) (ρ ^ (-A) * Complex.I ^ phase * F (ρ ^ 2)) at hEnergy
  rw [hρSq, ← hD, hρ] at hEnergy
  exact ⟨hJoint, hEnergy⟩

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBUpperHalfPlaneBD
