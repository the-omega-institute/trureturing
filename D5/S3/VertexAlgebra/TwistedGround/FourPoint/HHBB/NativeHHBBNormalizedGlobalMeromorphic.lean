import D5.S3.VertexAlgebra.TwistedGround.FourPoint.HHBB.NativeHHBBUpperCuspGerms
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourPointChartGluing
import Mathlib.Analysis.Meromorphic.Order

/-! The single-valued meromorphic continuation of the normalized marked HHBB amplitude. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section

open scoped TensorProduct Topology
open Filter Metric Set

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBNormalizedGlobalMeromorphic

open Complex (I)
open ActualLeechHyperbolic (leechData)
open LatticeHalfFockChargedTensorCoefficients (ActualGround)
open Orbifold.NativeOddTwistedIntertwiner (TwistedEven TwistedOdd leechUnit)
open OriginalFourMActualChart (Puncture)
open OriginalFourMVariableSupport (wordAt)
open NativeMixedWickChartTransport (MixedParity doubledOccupation)
open NativeFixedPairAIterate (fixedAExponent fixedAIterateCoeff fixedASlitSewn)
open NativeMixedUpperProductCusp (bJointTerm bProductCoeff bSewnNumerator)
open NativeMixedUpperDLip (dProductCoeff)
open NativeHHBBUpperCuspGerms (hhbb_marked_upper_cusp_germs)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod
  (slitDomain ball_subset_slitDomain isOpen_slitDomain)
open D5.S3.VertexAlgebra.TwistedGround.OriginalFourPointChartGluing
  (U_D U_D_eq puncturedPlane)

open private mem_slitDomain from D5.S3.Analytic.OriginalHalfBinomialSlitPeriod
open private isPreconnected_U_D U_D_subset_puncturedPlane from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourPointChartGluing
open private sqrt_square zpow_double from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedComplexSewing
open private bSewnNumerator_differentiableOn punctureExcitation_cast from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedUpperProductCusp
open private occupationGrade_eq from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedPhysicalOverlap

local notation "ℒ" => leechData

private def rightHalf : Set ℂ := {y | (1 / 2 : ℝ) < y.re}

private theorem slit_right_preconnected : IsPreconnected (slitDomain ∩ rightHalf) := by
  let c : ℂ := ((3 / 4 : ℝ) : ℂ)
  have hcS : c ∈ slitDomain := (mem_slitDomain _).2 (Or.inl (by norm_num [c]))
  have hcR : c ∈ rightHalf := by norm_num [c, rightHalf]
  have hS : StarConvex ℝ c slitDomain := by
    have hstar : StarConvex ℝ (1 - c) Complex.slitPlane := by
      rw [show 1 - c = (((1 / 4 : ℝ)) : ℂ) by norm_num [c, ← Complex.ofReal_sub]]
      exact Complex.starConvex_ofReal_slitPlane (by norm_num)
    intro y hy a b ha hb hab
    change 1 - (a • c + b • y) ∈ Complex.slitPlane
    rw [show 1 - (a • c + b • y) = a • (1 - c) + b • (1 - y) by
      simp only [smul_sub, ← add_sub_add_comm, ← add_smul, hab, one_smul]]
    exact hstar hy ha hb hab
  exact ((hS.inter ((convex_halfSpace_re_gt (1 / 2 : ℝ)).starConvex hcR)).isPathConnected
    ⟨hcS, hcR⟩).isConnected.isPreconnected

private theorem sqrt_ne_zero {y : ℂ} (hy : y ≠ 0) : Complex.sqrt y ≠ 0 :=
  fun h => hy (by simpa [h] using (sqrt_square y).symm)

private theorem meromorphic_order_of_cusp {f t g : ℂ → ℂ} {x : ℂ} (k : ℤ)
    (ht : AnalyticAt ℂ t x) (ht₀ : t x = 0) (ht' : deriv t x ≠ 0)
    (hg : AnalyticAt ℂ g x) (he : f =ᶠ[𝓝[≠] x] fun y => t y ^ k * g y) :
    MeromorphicAt f x ∧ meromorphicOrderAt f x = (k : WithTop ℤ) + meromorphicOrderAt g x := by
  have hpow : MeromorphicAt (t ^ k) x := ht.meromorphicAt.zpow k
  have horder : meromorphicOrderAt (t ^ k) x = (k : WithTop ℤ) := by
    change meromorphicOrderAt (((fun z : ℂ => z) ^ k) ∘ t) x = _
    rw [meromorphicOrderAt_comp_of_deriv_ne_zero ht ht', ht₀]
    simpa only [sub_zero] using
      (meromorphicOrderAt_zpow_id_sub_const (x := (0 : ℂ)) (n := k))
  refine ⟨(hpow.mul hg.meromorphicAt).congr he.symm, ?_⟩
  rw [meromorphicOrderAt_congr he]
  change meromorphicOrderAt ((t ^ k) * g) x = _
  rw [meromorphicOrderAt_mul hpow hg.meromorphicAt, horder]

set_option maxHeartbeats 4000000 in
/-- Multiplying the physical HHBB amplitude by the upper principal square root
gives a single meromorphic function of the base coordinate. Its only possible
poles are at zero, one and infinity. The exact orders include any vanishing
of the native cusp numerators. At one the A series uses the coordinate
`(1-y)/y` and the analytic unit `sqrt(y) ^ (N-L+1)`. -/
theorem hhbb_marked_normalized_global_meromorphic {X : Type*} [Finite X]
    (slot : X → Puncture) (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X)
    (hl : l.Nodup) (hpar : MixedParity slot n l)
    (u v : TwistedEven) (w b : TwistedOdd) (p q r d : ActualGround ℒ leechUnit)
    (hu : u.val = wordAt ℒ slot colour n l .P ⊗ₜ[ℂ] p)
    (hv : v.val = wordAt ℒ slot colour n l .Q ⊗ₜ[ℂ] q)
    (hw : w.val = wordAt ℒ slot colour n l .R ⊗ₜ[ℂ] r)
    (hb : b.val = wordAt ℒ slot colour n l .S ⊗ₜ[ℂ] d) :
    let grade (i : Puncture) := (doubledOccupation slot n l i).toNat
    let V := wordAt ℒ slot colour n l
    let M := grade .P
    let K := grade .Q
    let L := grade .R
    let N := grade .S
    let a₀ : ℤ := (5 + (K : ℤ) + L) / 2
    let a₁ : ℤ := (6 + (M : ℤ) + K) / 2
    let aInf : ℤ := (1 + (N : ℤ) - K) / 2
    let Z := Complex.sqrt
    let t (y : ℂ) := (1 - y) / y
    let G₀ (y : ℂ) := -(I ^ ((L : ℤ) + N - M - 2 * (K : ℤ) - 3) *
      bSewnNumerator K L N (V .P) (V .Q) (V .R) (V .S) p q r d y)
    let A (z : ℂ) := fixedASlitSewn M K (V .P) (V .Q) (V .R) (V .S) p q r d (-z)
    let G₁ (y : ℂ) := Z y ^ ((N : ℤ) - L) * A (t y)
    let GInf (z : ℂ) := I ^ ((L : ℤ) + N - K - 2 * (M : ℤ) - 3) *
      bSewnNumerator M L N (V .Q) (V .P) (V .R) (V .S) q p r d z
    let F (y : ℂ) := -(Z y ^ (-(6 + (K : ℤ) + L)) *
      I ^ ((L : ℤ) + N - M - 2 * (K : ℤ) - 3) *
      bSewnNumerator K L N (V .P) (V .Q) (V .R) (V .S) p q r d y)
    ∃ H : ℂ → ℂ,
      AnalyticOnNhd ℂ H ({0, 1} : Set ℂ)ᶜ ∧
      Meromorphic H ∧ MeromorphicAt (fun z => H z⁻¹) 0 ∧
      (∀ y : ℂ, 0 < y.im → H y = Z y * F y) ∧
      ((AnalyticOnNhd ℂ G₀ slitDomain ∧
        ∀ y ∈ slitDomain, y ≠ 0 → H y = y ^ (-a₀) * G₀ y) ∧
        (AnalyticOnNhd ℂ (fun y => Z y * G₁ y) {y : ℂ | (1 / 2 : ℝ) < y.re} ∧
        ∀ y : ℂ, (1 / 2 : ℝ) < y.re → y ≠ 1 →
          H y = (1 - y) ^ (-a₁) * (Z y * G₁ y)) ∧
        (AnalyticOnNhd ℂ GInf (ball (0 : ℂ) 1) ∧
        ∀ y : ℂ, 1 < ‖y‖ → H y = y ^ aInf * GInf y⁻¹)) ∧
      (meromorphicOrderAt H 0 = ((-a₀ : ℤ) : WithTop ℤ) + meromorphicOrderAt G₀ 0 ∧
        meromorphicOrderAt H 1 = ((-a₁ : ℤ) : WithTop ℤ) + meromorphicOrderAt A 0 ∧
        meromorphicOrderAt (fun z => H z⁻¹) 0 =
          ((-aInf : ℤ) : WithTop ℤ) + meromorphicOrderAt GInf 0) ∧
      (AnalyticOnNhd ℂ A (ball (0 : ℂ) 1) ∧
        (∀ z ∈ ball (0 : ℂ) 1, HasSum
          (fun E : ℕ => -(bProductCoeff false false M K L N v w u b E) * z ^ E) (G₀ z)) ∧
        (∀ z ∈ ball (0 : ℂ) 1, HasSum
          (fun E : ℕ => fixedAIterateCoeff false M K L N (fixedAExponent M K E)
            u v w.val b.val * z ^ E) (A z)) ∧
        (∀ z ∈ ball (0 : ℂ) 1, HasSum
          (fun E : ℕ => dProductCoeff false false M K L N u w v b E * z ^ E) (GInf z))) ∧
      ((∀ y ∈ ball (0 : ℂ) 1, 0 < y.im →
          HasSum (bJointTerm false false v w u b 1 (Z y)) (-(F y))) ∧
        (∀ y : ℂ, 0 < y.im → (1 / 2 : ℝ) < y.re →
          HasSum (NativeMixedComplexSewing.aJointTerm u v w b (Z (1 - y)) (Z y)) (F y)) ∧
        (∀ y : ℂ, 0 < y.im → 1 < ‖y‖ →
          HasSum (bJointTerm false false u w v b (Z y) 1) (F y))) := by
  intro grade V M K L N a₀ a₁ aInf Z t G₀ A G₁ GInf F
  obtain ⟨_, ⟨_, hBsum, hBupper⟩, ⟨hG₁, hA, hAsum, hAupper⟩,
    ⟨hGInf, hDsum, hDupper⟩⟩ :=
    hhbb_marked_upper_cusp_germs slot colour n l hl hpar u v w b p q r d hu hv hw hb
  have hgrade (i : Puncture) : (grade i : ℤ) = doubledOccupation slot n l i := by
    change (((doubledOccupation slot n l i).toNat : ℕ) : ℤ) = _
    rw [occupationGrade_eq slot colour n l i, punctureExcitation_cast]
  have hM : (M : ℤ) % 2 = 0 := by simpa only [M, hgrade] using hpar.1
  have hK : (K : ℤ) % 2 = 0 := by simpa only [K, hgrade] using hpar.2.1
  have hL : (L : ℤ) % 2 = 1 := by simpa only [L, hgrade] using hpar.2.2.1
  have hN : (N : ℤ) % 2 = 1 := by simpa only [N, hgrade] using hpar.2.2.2
  have hexp₀ : 1 + (-(6 + (K : ℤ) + L)) = 2 * (-a₀) := by dsimp only [a₀]; omega
  have hexp₁ : 2 * a₁ = (M : ℤ) + K + 6 := by dsimp only [a₁]; omega
  have hexpInf : 2 * aInf + ((K : ℤ) - N) = 1 := by dsimp only [aInf]; omega
  let U₀ := slitDomain \ ({0} : Set ℂ)
  let U₁ := rightHalf \ ({1} : Set ℂ)
  let upper : Set ℂ := {y | 0 < y.im}
  let H₀ (y : ℂ) := y ^ (-a₀) * G₀ y
  let H₁ (y : ℂ) := (1 - y) ^ (-a₁) * (Z y * G₁ y)
  let HInf (y : ℂ) := y ^ aInf * GInf y⁻¹
  have hOpenR : IsOpen rightHalf := isOpen_lt continuous_const Complex.continuous_re
  have hOpen₀ : IsOpen U₀ := isOpen_slitDomain.sdiff isClosed_singleton
  have hOpen₁ : IsOpen U₁ := hOpenR.sdiff isClosed_singleton
  have hOpenUpper : IsOpen upper := isOpen_lt continuous_const Complex.continuous_im
  have hSlit₁ {y : ℂ} (hy : y ∈ slitDomain) : y ≠ 1 := by
    rintro rfl
    simpa using (mem_slitDomain _).1 hy
  have hRight₀ {y : ℂ} (hy : y ∈ rightHalf) : y ≠ 0 := by
    rintro rfl
    norm_num [rightHalf] at hy
  have hUpper₀ {y : ℂ} (hy : y ∈ upper) : y ∈ U₀ := by
    change 0 < y.im at hy
    refine ⟨(mem_slitDomain _).2 (Or.inr hy.ne'), ?_⟩
    rintro rfl
    simp at hy
  have hU₁₀ : U₀ ∩ U₁ = slitDomain ∩ rightHalf := by
    ext y
    exact ⟨fun ⟨hs, hr⟩ => ⟨hs.1, hr.1⟩,
      fun ⟨hs, hr⟩ => ⟨⟨hs, hRight₀ hr⟩, ⟨hr, hSlit₁ hs⟩⟩⟩
  have hCover : U₀ ∪ U₁ = puncturedPlane := by
    ext y
    change (y ∈ slitDomain ∧ y ≠ 0) ∨ (y ∈ rightHalf ∧ y ≠ 1) ↔ _
    simp only [puncturedPlane, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    refine ⟨fun h => h.elim (fun ⟨hs, h₀⟩ => ⟨h₀, hSlit₁ hs⟩)
      (fun ⟨hr, h₁⟩ => ⟨hRight₀ hr, h₁⟩), ?_⟩
    intro ⟨h₀, h₁⟩
    by_cases hs : y ∈ slitDomain
    · exact Or.inl ⟨hs, h₀⟩
    · have hre : 1 ≤ y.re := le_of_not_gt fun h => hs ((mem_slitDomain _).2 (Or.inl h))
      exact Or.inr ⟨lt_of_lt_of_le (by norm_num : (1 / 2 : ℝ) < 1) hre, h₁⟩
  have hG₀ : AnalyticOnNhd ℂ G₀ slitDomain := by
    intro y hy
    exact ((analyticAt_const (v := I ^ ((L : ℤ) + N - M - 2 * (K : ℤ) - 3))).mul
      ((bSewnNumerator_differentiableOn K L N (V .P) (V .Q) (V .R) (V .S) p q r d)
        |>.analyticOnNhd isOpen_slitDomain y hy)).neg
  have hZ : AnalyticOnNhd ℂ Z rightHalf := by
    intro y hy
    change (1 / 2 : ℝ) < y.re at hy
    exact Complex.differentiableOn_sqrt.analyticOnNhd Complex.isOpen_slitPlane y
      (Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith)))
  have hZG₁ : AnalyticOnNhd ℂ (fun y => Z y * G₁ y) rightHalf := hZ.mul hG₁
  have hAn₀ : AnalyticOnNhd ℂ H₀ U₀ :=
    fun y hy => (analyticAt_id.zpow hy.2).mul (hG₀ y hy.1)
  have hAn₁ : AnalyticOnNhd ℂ H₁ U₁ := by
    intro y hy
    have hbase : AnalyticAt ℂ (fun z : ℂ => 1 - z) y := analyticAt_const.sub analyticAt_id
    exact (hbase.zpow (sub_ne_zero.mpr (Ne.symm hy.2))).mul (hZG₁ y hy.1)
  have h₀upper {y : ℂ} (hy : y ∈ upper) : H₀ y = Z y * F y := by
    have hScale : Z y * Z y ^ (-(6 + (K : ℤ) + L)) = y ^ (-a₀) := calc
      _ = Z y ^ (1 + (-(6 + (K : ℤ) + L))) := by
        rw [zpow_add₀ (sqrt_ne_zero (hUpper₀ hy).2), zpow_one]
      _ = _ := by rw [hexp₀, zpow_double, sqrt_square]
    dsimp only [H₀, G₀, F]
    rw [← hScale]
    simp only [mul_neg, mul_assoc]
  have h₁upper {y : ℂ} (hy : y ∈ upper) (hr : y ∈ rightHalf) : H₁ y = Z y * F y := by
    have he : (1 - y) ^ a₁ * F y = G₁ y := by
      have hpow : (1 - y) ^ a₁ = Z (1 - y) ^ ((M : ℤ) + K + 6) := by
        rw [← hexp₁, zpow_double, sqrt_square]
      rw [hpow]
      exact (hAupper _ hy hr).2
    have hne : 1 - y ≠ 0 := sub_ne_zero.mpr (hSlit₁ (hUpper₀ hy).1).symm
    change (1 - y) ^ (-a₁) * (Z y * G₁ y) = Z y * F y
    rw [← he, show (1 - y) ^ (-a₁) * (Z y * ((1 - y) ^ a₁ * F y)) =
      ((1 - y) ^ (-a₁) * (1 - y) ^ a₁) * (Z y * F y) by ring,
      ← zpow_add₀ hne, neg_add_cancel, zpow_zero, one_mul]
  have hOverlap : EqOn H₀ H₁ (U₀ ∩ U₁) := by
    let y₀ : ℂ := ⟨3 / 4, 1 / 4⟩
    have hyu : y₀ ∈ upper := by norm_num [y₀, upper]
    have hyr : y₀ ∈ rightHalf := by norm_num [y₀, rightHalf]
    have hy₁ : y₀ ∈ U₁ := ⟨hyr, hSlit₁ (hUpper₀ hyu).1⟩
    refine (hAn₀.mono inter_subset_left).eqOn_of_preconnected_of_eventuallyEq
      (hAn₁.mono inter_subset_right) (hU₁₀.symm ▸ slit_right_preconnected) ⟨hUpper₀ hyu, hy₁⟩ ?_
    filter_upwards [hOpenUpper.eventually_mem hyu, hOpenR.eventually_mem hyr] with y hy hr
    exact (h₀upper hy).trans (h₁upper hy hr).symm
  classical
  let H := U₀.piecewise H₀ H₁
  have hH₀ : EqOn H H₀ U₀ := fun _ hy => piecewise_eq_of_mem _ _ _ hy
  have hH₁ : EqOn H H₁ U₁ := by
    intro y hy
    by_cases hy₀ : y ∈ U₀
    · exact (hH₀ hy₀).trans (hOverlap ⟨hy₀, hy⟩)
    · exact piecewise_eq_of_notMem _ _ _ hy₀
  have hHol : AnalyticOnNhd ℂ H puncturedPlane := by
    rw [← hCover]
    rintro y (hy | hy)
    · exact (hAn₀ y hy).congr ((hOpen₀.eventually_mem hy).mono fun _ hz => (hH₀ hz).symm)
    · exact (hAn₁ y hy).congr ((hOpen₁.eventually_mem hy).mono fun _ hz => (hH₁ hz).symm)
  have hUpper {y : ℂ} (hy : y ∈ upper) : H y = Z y * F y :=
    (hH₀ (hUpper₀ hy)).trans (h₀upper hy)
  have hExtD {y : ℂ} (hy : 1 < ‖y‖) : y ∈ U_D := by
    rw [U_D_eq]
    intro h
    change y.im = 0 ∧ 0 ≤ y.re ∧ y.re ≤ 1 at h
    have hre : (y.re : ℂ) = y := Complex.ext rfl (by simpa using h.1.symm)
    have hnorm : ‖y‖ = y.re := calc
      ‖y‖ = ‖(y.re : ℂ)‖ := congrArg (fun z : ℂ => ‖z‖) hre.symm
      _ = y.re := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h.2.1]
    exact hy.not_ge (hnorm.symm ▸ h.2.2)
  have hDchart : AnalyticOnNhd ℂ HInf U_D := by
    have hNum : AnalyticOnNhd ℂ GInf slitDomain := by
      intro y hy
      exact (analyticAt_const (v := I ^ ((L : ℤ) + N - K - 2 * (M : ℤ) - 3))).mul
        ((bSewnNumerator_differentiableOn M L N (V .Q) (V .P) (V .R) (V .S) q p r d)
          |>.analyticOnNhd isOpen_slitDomain y hy)
    intro y hy
    have hy' : y ≠ 0 ∧ y⁻¹ ∈ slitDomain ∧ y⁻¹ ≠ 0 := hy
    exact (analyticAt_id.zpow hy'.1).mul ((hNum _ hy'.2.1).comp (analyticAt_inv hy'.1))
  have hExtUpper {y : ℂ} (hy : y ∈ upper) (he : 1 < ‖y‖) : H y = HInf y := by
    have hz := sqrt_ne_zero (hUpper₀ hy).2
    have hScale : y ^ aInf * Z y ^ ((K : ℤ) - N) = Z y := by
      calc
        _ = Z y ^ (2 * aInf) * Z y ^ ((K : ℤ) - N) := by rw [zpow_double, sqrt_square]
        _ = _ := by rw [← zpow_add₀ hz, hexpInf, zpow_one]
    rw [hUpper hy]
    change Z y * F y = y ^ aInf * GInf y⁻¹
    have hval : Z y ^ ((K : ℤ) - N) * F y = GInf y⁻¹ := (hDupper _ hy he).2
    rw [← hval, ← mul_assoc, hScale]
  have hExt : ∀ y : ℂ, 1 < ‖y‖ → H y = HInf y := by
    let y₀ : ℂ := (2 : ℂ) * I
    have hyu : y₀ ∈ upper := by norm_num [y₀, upper, Complex.mul_im]
    have hye : 1 < ‖y₀‖ := by norm_num [y₀, norm_mul]
    have hOpenExt : IsOpen {y : ℂ | 1 < ‖y‖} :=
      isOpen_lt continuous_const continuous_norm
    have heq : H =ᶠ[𝓝 y₀] HInf := by
      filter_upwards [hOpenUpper.eventually_mem hyu, hOpenExt.eventually_mem hye] with y hu' he'
      exact hExtUpper hu' he'
    have hEq := (hHol.mono U_D_subset_puncturedPlane).eqOn_of_preconnected_of_eventuallyEq
      hDchart isPreconnected_U_D (hExtD hye) heq
    exact fun _ hy => hEq (hExtD hy)
  have hNear₀ : H =ᶠ[𝓝[≠] (0 : ℂ)] H₀ := by
    have hBall := isOpen_ball.eventually_mem (mem_ball_self zero_lt_one : (0 : ℂ) ∈ ball 0 1)
    filter_upwards [hBall.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy hn
    exact hH₀ ⟨ball_subset_slitDomain hy, hn⟩
  have hOne : (1 : ℂ) ∈ rightHalf := by norm_num [rightHalf]
  have hNear₁ : H =ᶠ[𝓝[≠] (1 : ℂ)] H₁ := by
    filter_upwards [(hOpenR.eventually_mem hOne).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with y hy hn
    exact hH₁ ⟨hy, hn⟩
  have hNearInf : (fun z => H z⁻¹) =ᶠ[𝓝[≠] (0 : ℂ)] fun z => z ^ (-aInf) * GInf z := by
    have hBall := isOpen_ball.eventually_mem (mem_ball_self zero_lt_one : (0 : ℂ) ∈ ball 0 1)
    filter_upwards [hBall.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hn
    have hExt' : 1 < ‖z⁻¹‖ := by
      rw [norm_inv, one_lt_inv₀ (norm_pos_iff.mpr hn)]
      exact mem_ball_zero_iff.mp hz
    simpa only [HInf, inv_zpow', inv_inv] using hExt _ hExt'
  have hOrder₀ := meromorphic_order_of_cusp (-a₀) (t := fun z => z)
    analyticAt_id rfl (by simp) (hG₀ _ (ball_subset_slitDomain (mem_ball_self zero_lt_one))) hNear₀
  have hOrderInf := meromorphic_order_of_cusp (-aInf) (t := fun z => z)
    analyticAt_id rfl (by simp) (hGInf _ (mem_ball_self zero_lt_one)) hNearInf
  have hOrder₁ := meromorphic_order_of_cusp (-a₁) (t := fun y : ℂ => 1 - y)
    (analyticAt_const.sub analyticAt_id) (by simp) (by simp)
    (hZG₁ 1 hOne) hNear₁
  have hAorder : meromorphicOrderAt (fun y => Z y * G₁ y) 1 = meromorphicOrderAt A 0 := by
    have hZ₁ := hZ 1 hOne
    have hn := sqrt_ne_zero (one_ne_zero : (1 : ℂ) ≠ 0)
    let unit (y : ℂ) := Z y * Z y ^ ((N : ℤ) - L)
    have hu₁ : AnalyticAt ℂ unit 1 := hZ₁.mul (hZ₁.zpow hn)
    have hnu₁ : unit 1 ≠ 0 := mul_ne_zero hn (zpow_ne_zero _ hn)
    have ht : AnalyticAt ℂ t 1 :=
      (analyticAt_const.sub analyticAt_id).div analyticAt_id one_ne_zero
    have ht' : deriv t 1 ≠ 0 := by
      have hnum : HasDerivAt (fun y : ℂ => 1 - y) (-1) 1 := by
        simpa using (hasDerivAt_const (1 : ℂ) (1 : ℂ)).fun_sub (hasDerivAt_id' (1 : ℂ))
      have hderiv : HasDerivAt t (-1) 1 := by
        simpa [t] using hnum.fun_div (hasDerivAt_id' (1 : ℂ)) one_ne_zero
      rw [hderiv.deriv]
      simp
    have hAt : t 1 = 0 := by simp [t]
    simp only [G₁, ← mul_assoc]
    change meromorphicOrderAt (unit * (A ∘ t)) 1 = _
    rw [meromorphicOrderAt_mul_of_ne_zero hu₁ hnu₁,
      meromorphicOrderAt_comp_of_deriv_ne_zero ht ht', hAt]
  have hMer : Meromorphic H := by
    intro y
    by_cases h₀ : y = 0
    · simpa only [h₀] using hOrder₀.1
    by_cases h₁ : y = 1
    · simpa only [h₁] using hOrder₁.1
    exact (hHol y (by simp [puncturedPlane, h₀, h₁])).meromorphicAt
  exact ⟨H, hHol, hMer, hOrderInf.1, fun _ hy => hUpper hy,
    ⟨⟨hG₀, fun _ hy hn => hH₀ ⟨hy, hn⟩⟩, ⟨hZG₁, fun _ hy hn => hH₁ ⟨hy, hn⟩⟩,
      ⟨hGInf, hExt⟩⟩,
    ⟨hOrder₀.2, hOrder₁.2.trans (by rw [hAorder]), hOrderInf.2⟩,
    ⟨hA, hBsum, hAsum, hDsum⟩,
    ⟨fun y hy him => (hBupper y hy him).1,
      fun y him hre => (hAupper y him hre).1, fun y him he => (hDupper y him he).1⟩⟩

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBNormalizedGlobalMeromorphic
