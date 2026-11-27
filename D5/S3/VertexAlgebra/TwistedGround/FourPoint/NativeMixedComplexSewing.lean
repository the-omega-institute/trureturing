/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedComplexSewing
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedComplexSewing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual Leech HHBB A/B double-mode series sew on the complex physical lens. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedPhysicalOverlap
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedUpperProductCusp
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHRealSewing
import Mathlib.Analysis.Complex.SqrtDeriv

/-! Complex A/B sewing for the native Leech HHBB marked tensors.
The coordinate is `y = z / x` on the overlap `‖y‖ < 1`, `1 / 2 < y.re`.
The B coordinate uses the principal square root, positive on the positive real axis. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped TensorProduct VertexOperator ComplexOrder Topology
open Metric

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedComplexSewing

open ActualLeechHyperbolic (leechData)
open ActualChargedAdjoint (actualForm)
open LatticeHalfFockCorrectedField (correctedField)
open LatticeHalfFockGradedTrace (actualGrade)
open LatticeHalfFockChargedTensorCoefficients (ActualGround)
open Orbifold.NativeOddTwistedIntertwiner (TwistedEven TwistedOdd leechUnit)
open Orbifold.NativeFixedPairField (nu)
open NativeFixedPairFourPoint (nu_fourPoint_off_right_grade)
open NativeFixedPairAIterate (fixedAExponent fixedAIterateCoeff fixedAIterate_hasSum fixedASlitSewn)
open NativeMixedPhysicalOverlap (hhbb_actual_overlap)
open NativeMixedUpperProductCusp
  (bJointTerm bProductCoeff bSewnNumerator b_joint_product_hasSum b_product_hasSum_complex)
open NativeMixedWickChartTransport
  (MixedParity doubledOccupation laurentRoot laurentRoot_values sigma)
open OriginalFourMActualChart (Puncture)
open OriginalFourMVariableSupport (wordAt)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod
  (ball_subset_slitDomain isOpen_slitDomain slitDomain)

open private fixedASlitSewn_differentiableOn from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedPairAIterate
open private aModes norm_one_sub_lt_iff pair_off_energy ratio_analytic sewing_on_cap from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHRealSewing
open private occupationGrade_eq from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedPhysicalOverlap
open private bSewnNumerator_differentiableOn punctureExcitation_cast wordAt_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedUpperProductCusp

local notation "ℒ" => leechData

/-- The literal A iterate at independent doubled modes. The two root
coordinates square to `x - z` and `z`, respectively. -/
def aJointTerm (u v : TwistedEven) (w b : TwistedOdd)
    (differenceRoot zRoot : ℂ) (i : ℤ × ℤ) : ℂ :=
  actualForm ℒ leechUnit b.val
    ((correctedField ℒ leechUnit ((nu false u).coeff i.1 v).val).coeff i.2 w.val) *
      (differenceRoot ^ i.1 * zRoot ^ i.2)

private theorem a_joint_from_diagonal (M K L N : ℕ)
    (u v : TwistedEven) (w b : TwistedOdd)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (hw : w.val ∈ actualGrade ℒ leechUnit L) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    (hM : Even M) (hK : Even K)
    {zRoot ξ value : ℂ} (hz : zRoot ≠ 0)
    (hsum : HasSum (fun j : ℤ => fixedAIterateCoeff false M K L N j u v w.val b.val * ξ ^ j)
      value) :
    HasSum (aJointTerm u v w b (zRoot * ξ) zRoot)
      (zRoot ^ ((N : ℤ) - L - ((M : ℤ) + K + 6)) * value) := by
  have hinj : Function.Injective (aModes M K L N) := fun _ _ h => congrArg Prod.fst h
  have hoff (i : ℤ × ℤ) (hi : i ∉ Set.range (aModes M K L N)) :
      aJointTerm u v w b (zRoot * ξ) zRoot i = 0 := by
    rcases i with ⟨j, e⟩
    by_cases hj : ∃ E : ℕ, j = fixedAExponent M K E
    · obtain ⟨E, rfl⟩ := hj
      have he : e ≠ (N : ℤ) - L - 2 * (E : ℤ) := by
        intro he
        apply hi
        refine ⟨fixedAExponent M K E, Prod.ext rfl ?_⟩
        dsimp only [aModes, fixedAExponent]
        omega
      let m : ℤ := ((M : ℤ) + K + 4) / 2 - E
      obtain ⟨m₀, hm₀⟩ := hM
      obtain ⟨k₀, hk₀⟩ := hK
      have hE : 2 * (E : ℤ) = (M : ℤ) + K + 4 - 2 * m := by
        dsimp only [m]
        omega
      have hmode : fixedAExponent M K E = -2 * m - 2 := by
        unfold fixedAExponent
        omega
      change actualForm ℒ leechUnit b.val
        ((correctedField ℒ leechUnit ((nu false u).coeff (fixedAExponent M K E) v).val).coeff
          e w.val) * _ = 0
      rw [hmode, nu_fourPoint_off_right_grade false M K L N m (E : ℤ) e
        u v w.val b.val hu hv hw hb hE he, zero_mul]
    · have hpair := pair_off_energy M K u v hu hv j (fun E h => hj ⟨E, h⟩)
      simp [aJointTerm, hpair]
  apply (hinj.hasSum_iff hoff).mp
  refine (hsum.mul_left (zRoot ^ ((N : ℤ) - L - ((M : ℤ) + K + 6)))).congr_fun ?_
  intro j
  let d : ℤ := (N : ℤ) - L - ((M : ℤ) + K + 6)
  let e : ℤ := (N : ℤ) - L - (j + ((M : ℤ) + K + 6))
  have hpow : (zRoot * ξ) ^ j * zRoot ^ e = zRoot ^ d * ξ ^ j := by
    rw [mul_zpow]
    calc
      _ = (zRoot ^ j * zRoot ^ e) * ξ ^ j := by ring
      _ = _ := by rw [← zpow_add₀ hz, show j + e = d by dsimp only [e, d]; ring]
  change fixedAIterateCoeff false M K L N j u v w.val b.val *
    ((zRoot * ξ) ^ j * zRoot ^ e) =
      zRoot ^ d * (fixedAIterateCoeff false M K L N j u v w.val b.val * ξ ^ j)
  rw [hpow]
  ring

private theorem cap_ratio {y : ℂ} (hy : ‖y‖ < 1) (hre : (1 / 2 : ℝ) < y.re) :
    y ≠ 0 ∧ (1 - y) / y ≠ 0 ∧ ‖(1 - y) / y‖ < 1 := by
  have hy₀ : y ≠ 0 := by
    rintro rfl
    norm_num at hre
  have hy₁ : y ≠ 1 := by
    rintro rfl
    simp at hy
  refine ⟨hy₀, div_ne_zero (sub_ne_zero.mpr hy₁.symm) hy₀, ?_⟩
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hy₀)]
  exact (norm_one_sub_lt_iff y).mpr hre

private theorem square_root_disk {ξ t : ℂ} (hξ : ξ ^ (2 : ℕ) = t)
    (ht₀ : t ≠ 0) (ht₁ : ‖t‖ < 1) : ξ ≠ 0 ∧ ‖ξ‖ < 1 := by
  refine ⟨fun h => ht₀ (by simpa [h] using hξ.symm), ?_⟩
  apply (sq_lt_sq₀ (norm_nonneg ξ) zero_le_one).mp
  simpa only [← norm_pow, hξ, one_pow] using ht₁

private theorem sqrt_square (y : ℂ) : Complex.sqrt y ^ (2 : ℕ) = y :=
  Complex.cpow_nat_inv_pow y (by decide : (2 : ℕ) ≠ 0)

private theorem zpow_double (x : ℂ) (k : ℤ) :
    x ^ (2 * k) = (x ^ (2 : ℕ)) ^ k := by
  rw [zpow_mul, zpow_ofNat]

private theorem a_lens_analytic (num : ℂ → ℂ) (s a : ℤ) {y : ℂ}
    (hy : ‖y‖ < 1) (hre : (1 / 2 : ℝ) < y.re)
    (hnum : DifferentiableOn ℂ num slitDomain) :
    AnalyticAt ℂ (fun z => z ^ (-s) * (((1 - z) / z) ^ (-a) * num (-((1 - z) / z)))) y := by
  obtain ⟨hy₀, ht₀, ht₁⟩ := cap_ratio hy hre
  have ht : AnalyticAt ℂ (fun z : ℂ => (1 - z) / z) y := ratio_analytic hy₀
  have hneg : AnalyticAt ℂ (fun z : ℂ => -((1 - z) / z)) y := ht.neg
  have ha : AnalyticAt ℂ num (-((1 - y) / y)) :=
    hnum.analyticOnNhd isOpen_slitDomain _ (ball_subset_slitDomain (by
      rw [mem_ball_zero_iff, norm_neg]
      exact ht₁))
  have hc := AnalyticAt.comp (f := fun z : ℂ => -((1 - z) / z)) (g := num) ha hneg
  exact ((analyticAt_id (z := y)).zpow (n := -s) hy₀).mul
    ((ht.zpow (n := -a) ht₀).mul hc)

private theorem b_lens_analytic (num : ℂ → ℂ) (phase : ℂ) (k : ℤ) {y : ℂ}
    (hy : ‖y‖ < 1) (hre : (1 / 2 : ℝ) < y.re)
    (hnum : DifferentiableOn ℂ num slitDomain) :
    AnalyticAt ℂ (fun z => -(Complex.sqrt z ^ k * phase * num z)) y := by
  obtain ⟨hy₀, _, _⟩ := cap_ratio hy hre
  have hroot₀ := (square_root_disk (sqrt_square y) hy₀ hy).1
  have hroot : AnalyticAt ℂ Complex.sqrt y :=
    Complex.differentiableOn_sqrt.analyticOnNhd Complex.isOpen_slitPlane y
      (Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith)))
  have hb := hnum.analyticOnNhd isOpen_slitDomain y
    (ball_subset_slitDomain (mem_ball_zero_iff.mpr hy))
  have hphase : AnalyticAt ℂ (fun _ : ℂ => phase) y := analyticAt_const
  exact (((hroot.zpow (n := k) hroot₀).mul hphase).mul hb).neg

set_option maxHeartbeats 4000000 in
/-- The HHBB marked-tensor A and upper right-skew B series sew on the full
complex physical lens. The physical coordinates are `x = xRoot ^ 2` and
`z = x * y`. The B root of `z / x` is `Complex.sqrt y`. Either square root
of `(1 - y) / y` gives the same A value, whose closed formula uses an
integer power. The two mode-pair sums have opposite values with the
common homogeneity factor `x ^ (-sigma)`. At source energy `E`, the doubled
modes are `(2*E - (M + K + 6), N - L - 2*E)` in A and
`(2*E - (6 + K + L), N - M - 2*E)` in B. -/
theorem hhbb_actual_complex_sewing {X : Type*} [Finite X]
    (slot : X → Puncture) (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X)
    (hl : l.Nodup) (hpar : MixedParity slot n l)
    (u v : TwistedEven) (w b : TwistedOdd) (p q r d : ActualGround ℒ leechUnit)
    (hu : u.val = wordAt ℒ slot colour n l .P ⊗ₜ[ℂ] p)
    (hv : v.val = wordAt ℒ slot colour n l .Q ⊗ₜ[ℂ] q)
    (hw : w.val = wordAt ℒ slot colour n l .R ⊗ₜ[ℂ] r)
    (hb : b.val = wordAt ℒ slot colour n l .S ⊗ₜ[ℂ] d)
    {xRoot y ξ : ℂ} (hx : xRoot ≠ 0) (hy : ‖y‖ < 1) (hre : (1 / 2 : ℝ) < y.re)
    (hξ : ξ ^ (2 : ℕ) = (1 - y) / y) :
    let G := doubledOccupation slot n l
    let M := (G .P).toNat
    let K := (G .Q).toNat
    let L := (G .R).toNat
    let N := (G .S).toNat
    let V := wordAt ℒ slot colour n l
    let s := sigma (M : ℤ) K L N
    let t := (1 - y) / y
    let A := y ^ (-s) * (t ^ (-(((M : ℤ) + K + 6) / 2)) *
      fixedASlitSewn M K (V .P) (V .Q) (V .R) (V .S) p q r d (-t))
    let B := Complex.sqrt y ^ (-(6 + (K : ℤ) + L)) *
      Complex.I ^ ((L : ℤ) + N - M - 2 * (K : ℤ) - 3) *
      bSewnNumerator K L N (V .P) (V .Q) (V .R) (V .S) p q r d y
    let x := xRoot ^ (2 : ℕ)
    let z := x * y
    let zRoot := xRoot * Complex.sqrt y
    let scale := x ^ (-s)
    zRoot ^ (2 : ℕ) = z ∧ (zRoot * ξ) ^ (2 : ℕ) = x - z ∧ scale ≠ 0 ∧
      A = -B ∧
      HasSum (aJointTerm u v w b (zRoot * ξ) zRoot) (-(scale * B)) ∧
      HasSum (bJointTerm false false v w u b xRoot zRoot) (scale * B) := by
  let G := doubledOccupation slot n l
  let H (i : Puncture) := (G i).toNat
  let M := H .P
  let K := H .Q
  let L := H .R
  let N := H .S
  let V := wordAt ℒ slot colour n l
  let s := sigma (M : ℤ) K L N
  let a := ((M : ℤ) + K + 6) / 2
  let phase := Complex.I ^ ((L : ℤ) + N - M - 2 * (K : ℤ) - 3)
  let t (z : ℂ) := (1 - z) / z
  let aNumerator := fixedASlitSewn M K (V .P) (V .Q) (V .R) (V .S) p q r d
  let bNumerator := bSewnNumerator K L N (V .P) (V .Q) (V .R) (V .S) p q r d
  let A (z : ℂ) := z ^ (-s) * ((t z) ^ (-a) * aNumerator (-(t z)))
  let B (z : ℂ) := Complex.sqrt z ^ (-(6 + (K : ℤ) + L)) * phase * bNumerator z
  have hH (i : Puncture) := occupationGrade_eq slot colour n l i
  have hG (i : Puncture) : (H i : ℤ) = G i := by
    change (((G i).toNat : ℕ) : ℤ) = G i
    rw [hH i, punctureExcitation_cast]
  have hM₀ : (M : ℤ) % 2 = 0 := by simpa only [M, hG] using hpar.1
  have hK₀ : (K : ℤ) % 2 = 0 := by simpa only [K, hG] using hpar.2.1
  have hL₁ : (L : ℤ) % 2 = 1 := by simpa only [L, hG] using hpar.2.2.1
  have hN₁ : (N : ℤ) % 2 = 1 := by simpa only [N, hG] using hpar.2.2.2
  have hM : Even M := (Int.even_coe_nat M).mp (Int.even_iff.mpr hM₀)
  have hK : Even K := (Int.even_coe_nat K).mp (Int.even_iff.mpr hK₀)
  have hMK : Even ((M : ℤ) + K) := Int.even_iff.mpr (by omega)
  have hKL : Odd ((K : ℤ) + L) := Int.odd_iff.mpr (by omega)
  have hNM : Odd ((N : ℤ) - M) := Int.odd_iff.mpr (by omega)
  have huGrade : u.val ∈ actualGrade ℒ leechUnit M := by
    rw [hu, show M = _ from hH .P]
    exact wordAt_grade slot colour n l .P p
  have hvGrade : v.val ∈ actualGrade ℒ leechUnit K := by
    rw [hv, show K = _ from hH .Q]
    exact wordAt_grade slot colour n l .Q q
  have hRGrade : V .R ⊗ₜ[ℂ] r ∈ actualGrade ℒ leechUnit L := by
    rw [show L = _ from hH .R]
    exact wordAt_grade slot colour n l .R r
  have hSGrade : V .S ⊗ₜ[ℂ] d ∈ actualGrade ℒ leechUnit N := by
    rw [show N = _ from hH .S]
    exact wordAt_grade slot colour n l .S d
  have hwGrade : w.val ∈ actualGrade ℒ leechUnit L := by
    rw [hw]
    exact hRGrade
  have hbGrade : b.val ∈ actualGrade ℒ leechUnit N := by
    rw [hb]
    exact hSGrade
  have aSum {z η : ℂ} (hz : ‖z‖ < 1) (hzre : (1 / 2 : ℝ) < z.re)
      (hη : η ^ (2 : ℕ) = t z) :
      HasSum (fun j : ℤ => fixedAIterateCoeff false M K L N j u v w.val b.val * η ^ j)
        ((t z) ^ (-a) * aNumerator (-(t z))) := by
    obtain ⟨_, ht₀, ht₁⟩ := cap_ratio hz hzre
    obtain ⟨hη₀, hη₁⟩ := square_root_disk hη ht₀ ht₁
    have hsum := fixedAIterate_hasSum false M K L N u v (V .P) (V .Q) (V .R) (V .S) p q r d
      huGrade hvGrade hu hv hRGrade hSGrade hMK hη₀ hη₁
    have hexp : -((M : ℤ) + K + 6) = 2 * (-a) := by
      dsimp only [a]
      omega
    rw [hexp, zpow_double, hη] at hsum
    simpa only [hw, hb, aNumerator] using hsum
  have bSum {z : ℂ} (hz : ‖z‖ < 1) (hzre : (1 / 2 : ℝ) < z.re) :
      HasSum (fun E : ℕ => bProductCoeff false false M K L N v w u b E *
        Complex.sqrt z ^ (2 * (E : ℤ) - (6 + (K : ℤ) + L))) (B z) := by
    obtain ⟨hz₀, _, _⟩ := cap_ratio hz hzre
    obtain ⟨hroot₀, hroot₁⟩ := square_root_disk (sqrt_square z) hz₀ hz
    simpa only [B, phase, bNumerator, sqrt_square] using
      b_product_hasSum_complex false false M K L N v w u b (V .P) (V .Q) (V .R) (V .S) p q r d
        hvGrade hwGrade huGrade hbGrade hv hw hu hb hKL hNM (norm_pos_iff.mpr hroot₀) hroot₁
  have hAanalytic (z : ℂ) (hz : ‖z‖ < 1) (hzre : (1 / 2 : ℝ) < z.re) :
      AnalyticAt ℂ A z :=
    a_lens_analytic aNumerator s a hz hzre
      (fixedASlitSewn_differentiableOn M K (V .P) (V .Q) (V .R) (V .S) p q r d)
  have hBanalytic (z : ℂ) (hz : ‖z‖ < 1) (hzre : (1 / 2 : ℝ) < z.re) :
      AnalyticAt ℂ (fun z => -B z) z :=
    b_lens_analytic bNumerator phase (-(6 + (K : ℤ) + L)) hz hzre
      (bSewnNumerator_differentiableOn K L N (V .P) (V .Q) (V .R) (V .S) p q r d)
  have hCompare : A y = -B y := by
    refine sewing_on_cap A (fun z => -B z) hAanalytic hBanalytic ?_ y hy hre
    intro r₀ hr hr₁
    have hrPos : 0 < r₀ := by linarith
    have hrNorm : ‖(r₀ : ℂ)‖ < 1 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrPos] using hr₁
    have hrRe : (1 / 2 : ℝ) < (r₀ : ℂ).re := by simpa only [Complex.ofReal_re] using hr
    have hξr : laurentRoot .A r₀ ^ (2 : ℕ) = t (r₀ : ℂ) := by
      rw [(laurentRoot_values hr₁).1, ← Complex.ofReal_pow,
        Real.sq_sqrt (div_nonneg (sub_nonneg.mpr hr₁.le) hrPos.le)]
      simp only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one, t]
    have hρr : Complex.sqrt (r₀ : ℂ) = (Real.sqrt r₀ : ℂ) := by
      simpa only [Complex.ofReal_re] using
        (Complex.sqrt_of_nonneg (RCLike.ofReal_nonneg.mpr hrPos.le) :
          Complex.sqrt (r₀ : ℂ) = (Real.sqrt (r₀ : ℂ).re : ℂ))
    have hAr := aSum hrNorm hrRe hξr
    have hBr := bSum hrNorm hrRe
    rw [hρr] at hBr
    have hReal := (hhbb_actual_overlap slot colour n l hl hpar u v w b p q r d
      hu hv hw hb hr hr₁).1
    have hsG : sigma (G .P) (G .Q) (G .R) (G .S) = s := by
      dsimp only [s, M, K, L, N]
      simp only [hG]
    dsimp only at hReal
    rw [show sigma (doubledOccupation slot n l .P) (doubledOccupation slot n l .Q)
      (doubledOccupation slot n l .R) (doubledOccupation slot n l .S) = s from hsG] at hReal
    rw [hBr.tsum_eq] at hReal
    have hArValue := hAr.unique hReal
    change (r₀ : ℂ) ^ (-s) * ((t (r₀ : ℂ)) ^ (-a) * aNumerator (-(t (r₀ : ℂ)))) = _
    rw [hArValue, mul_neg, ← mul_assoc, ← zpow_add₀ (Complex.ofReal_ne_zero.mpr hrPos.ne'),
      neg_add_cancel, zpow_zero, one_mul]
  have hDegreeA : (N : ℤ) - L - ((M : ℤ) + K + 6) = 2 * (-s) := by
    dsimp only [s, sigma]
    omega
  have hDegreeB : (N : ℤ) - M - (6 + (K : ℤ) + L) = 2 * (-s) := by
    rw [← hDegreeA]
    ring
  let zRoot := xRoot * Complex.sqrt y
  let scale := (xRoot ^ (2 : ℕ)) ^ (-s)
  have hy₀ := (cap_ratio hy hre).1
  obtain ⟨hroot₀, hroot₁⟩ := square_root_disk (sqrt_square y) hy₀ hy
  have hzRoot : zRoot ≠ 0 := mul_ne_zero hx hroot₀
  have hzSquare : zRoot ^ (2 : ℕ) = xRoot ^ (2 : ℕ) * y := by
    rw [show zRoot = xRoot * Complex.sqrt y from rfl, mul_pow, sqrt_square]
  have hDifference : (zRoot * ξ) ^ (2 : ℕ) =
      xRoot ^ (2 : ℕ) - xRoot ^ (2 : ℕ) * y := by
    rw [mul_pow, hzSquare, hξ, mul_assoc, mul_div_cancel₀ _ hy₀, mul_sub, mul_one]
  have hScale : scale ≠ 0 := zpow_ne_zero _ (pow_ne_zero _ hx)
  have hRatio : zRoot / xRoot = Complex.sqrt y := mul_div_cancel_left₀ _ hx
  have hA := a_joint_from_diagonal M K L N u v w b huGrade hvGrade hwGrade hbGrade hM hK
    hzRoot (aSum hy hre hξ)
  have hAPower : zRoot ^ ((N : ℤ) - L - ((M : ℤ) + K + 6)) = scale * y ^ (-s) := by
    rw [hDegreeA, zpow_double, hzSquare, mul_zpow]
  rw [hAPower, mul_assoc scale (y ^ (-s))] at hA
  change HasSum (aJointTerm u v w b (zRoot * ξ) zRoot) (scale * A y) at hA
  rw [hCompare, mul_neg] at hA
  have hB := b_joint_product_hasSum false false M K L N v w u b (V .P) (V .Q) (V .R) (V .S)
    p q r d hvGrade hwGrade huGrade hbGrade hv hw hu hb hKL hNM
    (xRoot := xRoot) (zRoot := zRoot) hx
    (by rw [hRatio]; exact norm_pos_iff.mpr hroot₀) (by rw [hRatio]; exact hroot₁)
  rw [hRatio, sqrt_square, hDegreeB, zpow_double] at hB
  exact ⟨hzSquare, hDifference, hScale, hCompare, hA, hB⟩

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedComplexSewing
