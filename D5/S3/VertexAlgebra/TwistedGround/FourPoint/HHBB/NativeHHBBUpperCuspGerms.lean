import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHBHBUpperAD

/-! Holomorphic cusp representatives for the marked actual HHBB upper amplitude. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section

open scoped BigOperators TensorProduct Topology
open Metric Set

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBUpperCuspGerms

open Complex (I)
open ActualLeechHyperbolic (leechData)
open LatticeHalfFockChargedTensorCoefficients (ActualGround)
open LatticeHalfFockGradedTrace (actualGrade)
open Orbifold.NativeOddTwistedIntertwiner (Twisted TwistedEven TwistedOdd leechUnit)
open OriginalFourMActualChart (Puncture)
open OriginalFourMVariableSupport (wordAt)
open OriginalGaussianSewnAnalytic (coefficient)
open NativeMixedWickChartTransport (MixedParity doubledOccupation sigma)
open NativeFixedPairAIterate
  (fixedAExponent fixedAIterateCoeff fixedASlitSewn fixedAIterate_hasSum
    fixedAIterate_negative_square_germ)
open NativeMixedUpperProductCusp (bJointTerm bProductCoeff bProductCoeff_eq_taylor bSewnNumerator)
open NativeMixedUpperDLip (dProductCoeff dSlitProduct)
open NativeHHBBBSlitExtension (hhbb_marked_b_slit_extension)
open NativeHHBBUpperHalfPlaneBD
  (hhbb_marked_rawD_eq_neg_rawB_upper_half_plane hhbb_marked_rawD_hasSum_upper_exterior)
open NativeFixedCrossedProductToIterate (hhbb_upper_fixed_d_joint_hasSum)
open NativeHBHBUpperAD (hbhb_marked_d_hasSum_upper_right)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod
  (slitDomain ball_subset_slitDomain isOpen_slitDomain)

open private sqrt_square square_root_disk zpow_double a_joint_from_diagonal from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedComplexSewing
open private marked_grade right_ratio from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHBHBUpperAD
open private norm_one_sub_lt_iff ratio_analytic from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHRealSewing
open private fixedASlitSewn_neg_differentiableOn from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedPairAIterate
open private bSewnNumerator_differentiableOn bDetector_coefficient
  punctureExcitation_cast from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedUpperProductCusp
open private occupationGrade_eq from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedPhysicalOverlap

local notation "ℒ" => leechData

private theorem scalar_taylor_hasSum {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G (ball (0 : ℂ) 1)) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    HasSum (fun E : ℕ => coefficient E G * z ^ E) (G z) := by
  refine (Complex.hasSum_taylorSeries_on_ball hG hz).congr_fun ?_
  intro E
  simp only [coefficient, sub_zero, smul_eq_mul, div_eq_mul_inv]
  ring

private theorem shifted_energy_power {root : ℂ} (hroot : root ≠ 0) (A : ℤ) (E : ℕ) :
    root ^ (2 * (E : ℤ) - A) = root ^ (-A) * (root ^ (2 : ℕ)) ^ E := by
  rw [show 2 * (E : ℤ) - A = -A + 2 * (E : ℤ) by ring,
    zpow_add₀ hroot, zpow_mul, zpow_ofNat, zpow_natCast]

set_option maxHeartbeats 4000000 in
/-- The marked HHBB upper amplitude is the negative of raw B and is
holomorphic on the open upper half-plane. With the principal roots
`Z = sqrt y` and `D = sqrt (1-y)`, its three renormalized values agree
with holomorphic functions through the corresponding cusps. The three
unit-disk energy sums use the actual B, A and D mode coefficients.
At the cusp one the energy variable is `(1-y)/y`. The holomorphic
prefactor in the physical coordinate is `Z ^ (N-L)`. -/
theorem hhbb_marked_upper_cusp_germs {X : Type*} [Finite X]
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
    let Z := Complex.sqrt
    let D (y : ℂ) := Complex.sqrt (1 - y)
    let t (y : ℂ) := (1 - y) / y
    let G₀ (y : ℂ) := -(I ^ ((L : ℤ) + N - M - 2 * (K : ℤ) - 3) *
      bSewnNumerator K L N (V .P) (V .Q) (V .R) (V .S) p q r d y)
    let A (z : ℂ) := fixedASlitSewn M K (V .P) (V .Q) (V .R) (V .S) p q r d (-z)
    let G₁ (y : ℂ) := Z y ^ ((N : ℤ) - L) * A (t y)
    let Ginf (z : ℂ) := I ^ ((L : ℤ) + N - K - 2 * (M : ℤ) - 3) *
      bSewnNumerator M L N (V .Q) (V .P) (V .R) (V .S) q p r d z
    let F (y : ℂ) := -(Z y ^ (-(6 + (K : ℤ) + L)) *
      I ^ ((L : ℤ) + N - M - 2 * (K : ℤ) - 3) *
      bSewnNumerator K L N (V .P) (V .Q) (V .R) (V .S) p q r d y)
    AnalyticOnNhd ℂ F {y : ℂ | 0 < y.im} ∧
    (AnalyticOnNhd ℂ G₀ (ball (0 : ℂ) 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, HasSum
        (fun E : ℕ => -(bProductCoeff false false M K L N v w u b E) * z ^ E) (G₀ z)) ∧
      (∀ y ∈ ball (0 : ℂ) 1, 0 < y.im →
        HasSum (bJointTerm false false v w u b 1 (Z y)) (-(F y)) ∧
        Z y ^ (6 + (K : ℤ) + L) * F y = G₀ y)) ∧
    (AnalyticOnNhd ℂ G₁ {y : ℂ | (1 / 2 : ℝ) < y.re} ∧
      AnalyticOnNhd ℂ A (ball (0 : ℂ) 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, HasSum
        (fun E : ℕ => fixedAIterateCoeff false M K L N (fixedAExponent M K E)
          u v w.val b.val * z ^ E) (A z)) ∧
      (∀ y : ℂ, 0 < y.im → (1 / 2 : ℝ) < y.re →
        HasSum (NativeMixedComplexSewing.aJointTerm u v w b (D y) (Z y)) (F y) ∧
        D y ^ ((M : ℤ) + K + 6) * F y = G₁ y)) ∧
    (AnalyticOnNhd ℂ Ginf (ball (0 : ℂ) 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, HasSum
        (fun E : ℕ => dProductCoeff false false M K L N u w v b E * z ^ E) (Ginf z)) ∧
      (∀ y : ℂ, 0 < y.im → 1 < ‖y‖ →
        HasSum (bJointTerm false false u w v b (Z y) 1) (F y) ∧
        Z y ^ ((K : ℤ) - N) * F y = Ginf y⁻¹)) := by
  let H (i : Puncture) := (doubledOccupation slot n l i).toNat
  let V := wordAt ℒ slot colour n l
  let M := H .P
  let K := H .Q
  let L := H .R
  let N := H .S
  let Z := Complex.sqrt
  let D (y : ℂ) := Complex.sqrt (1 - y)
  let t (y : ℂ) := (1 - y) / y
  let a : ℤ := (M : ℤ) + K + 6
  let c : ℤ := 6 + (K : ℤ) + L
  let e : ℤ := 6 + (M : ℤ) + L
  let s := sigma (M : ℤ) K L N
  let phase₀ := I ^ ((L : ℤ) + N - M - 2 * (K : ℤ) - 3)
  let phaseInf := I ^ ((L : ℤ) + N - K - 2 * (M : ℤ) - 3)
  let num₀ := bSewnNumerator K L N (V .P) (V .Q) (V .R) (V .S) p q r d
  let numInf := bSewnNumerator M L N (V .Q) (V .P) (V .R) (V .S) q p r d
  let G₀ (y : ℂ) := -(phase₀ * num₀ y)
  let A (z : ℂ) := fixedASlitSewn M K (V .P) (V .Q) (V .R) (V .S) p q r d (-z)
  let G₁ (y : ℂ) := Z y ^ ((N : ℤ) - L) * A (t y)
  let Ginf (z : ℂ) := phaseInf * numInf z
  let F (y : ℂ) := -(Z y ^ (-c) * phase₀ * num₀ y)
  let Bcoeff := bProductCoeff false false M K L N v w u b
  let Acoeff (E : ℕ) := fixedAIterateCoeff false M K L N (fixedAExponent M K E)
    u v w.val b.val
  let Dcoeff := dProductCoeff false false M K L N u w v b
  change AnalyticOnNhd ℂ F {y : ℂ | 0 < y.im} ∧
    (AnalyticOnNhd ℂ G₀ (ball (0 : ℂ) 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, HasSum (fun E : ℕ => -(Bcoeff E) * z ^ E) (G₀ z)) ∧
      (∀ y ∈ ball (0 : ℂ) 1, 0 < y.im →
        HasSum (bJointTerm false false v w u b 1 (Z y)) (-(F y)) ∧
        Z y ^ c * F y = G₀ y)) ∧
    (AnalyticOnNhd ℂ G₁ {y : ℂ | (1 / 2 : ℝ) < y.re} ∧
      AnalyticOnNhd ℂ A (ball (0 : ℂ) 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, HasSum (fun E : ℕ => Acoeff E * z ^ E) (A z)) ∧
      (∀ y : ℂ, 0 < y.im → (1 / 2 : ℝ) < y.re →
        HasSum (NativeMixedComplexSewing.aJointTerm u v w b (D y) (Z y)) (F y) ∧
        D y ^ a * F y = G₁ y)) ∧
    (AnalyticOnNhd ℂ Ginf (ball (0 : ℂ) 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, HasSum (fun E : ℕ => Dcoeff E * z ^ E) (Ginf z)) ∧
      (∀ y : ℂ, 0 < y.im → 1 < ‖y‖ →
        HasSum (bJointTerm false false u w v b (Z y) 1) (F y) ∧
        Z y ^ ((K : ℤ) - N) * F y = Ginf y⁻¹))
  have hG (i : Puncture) : (H i : ℤ) = doubledOccupation slot n l i := by
    change (((doubledOccupation slot n l i).toNat : ℕ) : ℤ) = _
    rw [occupationGrade_eq slot colour n l i, punctureExcitation_cast]
  have hM₀ : (M : ℤ) % 2 = 0 := by simpa only [M, hG] using hpar.1
  have hK₀ : (K : ℤ) % 2 = 0 := by simpa only [K, hG] using hpar.2.1
  have hL₁ : (L : ℤ) % 2 = 1 := by simpa only [L, hG] using hpar.2.2.1
  have hN₁ : (N : ℤ) % 2 = 1 := by simpa only [N, hG] using hpar.2.2.2
  have hM : Even M := (Int.even_coe_nat M).mp (Int.even_iff.mpr hM₀)
  have hK : Even K := (Int.even_coe_nat K).mp (Int.even_iff.mpr hK₀)
  have hMK : Even ((M : ℤ) + K) := Int.even_iff.mpr (by omega)
  have huG : u.val ∈ actualGrade ℒ leechUnit M := hu.symm ▸ marked_grade slot colour n l .P p
  have hvG : v.val ∈ actualGrade ℒ leechUnit K := hv.symm ▸ marked_grade slot colour n l .Q q
  have hRG := marked_grade slot colour n l .R r
  have hSG := marked_grade slot colour n l .S d
  have hwG : w.val ∈ actualGrade ℒ leechUnit L := hw.symm ▸ hRG
  have hbG : b.val ∈ actualGrade ℒ leechUnit N := hb.symm ▸ hSG
  have hA_diff : DifferentiableOn ℂ A (ball (0 : ℂ) 1) :=
    fixedASlitSewn_neg_differentiableOn M K (V .P) (V .Q) (V .R) (V .S) p q r d
  have hA_analytic : AnalyticOnNhd ℂ A (ball (0 : ℂ) 1) :=
    hA_diff.analyticOnNhd isOpen_ball
  have hCross := hhbb_marked_rawD_eq_neg_rawB_upper_half_plane slot colour n l hl hpar
    u v w b p q r d hu hv hw hb
  have hNum₀ : DifferentiableOn ℂ num₀ slitDomain :=
    bSewnNumerator_differentiableOn K L N (V .P) (V .Q) (V .R) (V .S) p q r d
  have hNumInf : DifferentiableOn ℂ numInf slitDomain :=
    bSewnNumerator_differentiableOn M L N (V .Q) (V .P) (V .R) (V .S) q p r d
  have hDEnergy (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) :
      HasSum (fun E : ℕ => Dcoeff E * z ^ E) (Ginf z) := by
    have hML : Odd ((M : ℤ) + L) := Int.odd_iff.mpr (by omega)
    have hNK : Odd ((N : ℤ) - K) := Int.odd_iff.mpr (by omega)
    have hdiff := hNumInf.mono ball_subset_slitDomain
    refine ((scalar_taylor_hasSum hdiff hz).mul_left phaseInf).congr_fun ?_
    intro E
    symm
    change phaseInf * (coefficient E numInf * z ^ E) = Dcoeff E * z ^ E
    have hCoeff : Dcoeff E = phaseInf * coefficient E numInf := by
      dsimp only [Dcoeff, dProductCoeff]
      rw [bProductCoeff_eq_taylor false false K M L N u w v b (V .Q) (V .P) (V .R) (V .S)
        q p r d huG hwG hvG hbG hu hw hv hb hML hNK E, bDetector_coefficient,
        ← mul_assoc, ← zpow_add₀ Complex.I_ne_zero]
      have hphase : (N : ℤ) - K + ((L : ℤ) - 2 * (M : ℤ) - 3) =
          (L : ℤ) + N - K - 2 * (M : ℤ) - 3 := by ring
      rw [hphase]
    rw [hCoeff, mul_assoc]
  refine ⟨hCross.1.neg, ⟨?_, ?_, ?_⟩, ⟨?_, hA_analytic, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · intro y hy
    exact ((analyticAt_const (v := phase₀)).mul
      (hNum₀.analyticOnNhd isOpen_slitDomain y (ball_subset_slitDomain hy))).neg
  · intro z hz
    have hKL : Odd ((K : ℤ) + L) := Int.odd_iff.mpr (by omega)
    have hNM : Odd ((N : ℤ) - M) := Int.odd_iff.mpr (by omega)
    have hdiff := hNum₀.mono ball_subset_slitDomain
    refine ((scalar_taylor_hasSum hdiff hz).mul_left phase₀).neg.congr_fun ?_
    intro E
    symm
    change -(phase₀ * (coefficient E num₀ * z ^ E)) = -(Bcoeff E) * z ^ E
    have hCoeff : Bcoeff E = phase₀ * coefficient E num₀ := by
      dsimp only [Bcoeff]
      rw [bProductCoeff_eq_taylor false false M K L N v w u b (V .P) (V .Q) (V .R) (V .S)
        p q r d hvG hwG huG hbG hv hw hu hb hKL hNM E, bDetector_coefficient,
        ← mul_assoc, ← zpow_add₀ Complex.I_ne_zero]
      have hphase : (N : ℤ) - M + ((L : ℤ) - 2 * (K : ℤ) - 3) =
          (L : ℤ) + N - M - 2 * (K : ℤ) - 3 := by ring
      rw [hphase]
    rw [hCoeff, neg_mul, mul_assoc]
  · intro y hy him
    have hy₀ : y ≠ 0 := by
      rintro rfl
      simp at him
    have hz₀ : Z y ≠ 0 := fun h => hy₀ (by simpa [Z, h] using (sqrt_square y).symm)
    have hSum := (hhbb_marked_b_slit_extension slot colour n l hpar
      u v w b p q r d hu hv hw hb).2 (mem_ball_zero_iff.mp hy)
    refine ⟨by simpa only [F, neg_neg] using hSum, ?_⟩
    change Z y ^ c * -(Z y ^ (-c) * phase₀ * num₀ y) = -(phase₀ * num₀ y)
    rw [← mul_neg, ← mul_assoc, ← mul_assoc, ← zpow_add₀ hz₀, add_neg_cancel, zpow_zero, one_mul, mul_neg]
  · intro y hre
    change (1 / 2 : ℝ) < y.re at hre
    have hy₀ : y ≠ 0 := by
      rintro rfl
      norm_num at hre
    have hz₀ : Z y ≠ 0 := fun h => hy₀ (by simpa [Z, h] using (sqrt_square y).symm)
    have hZ : AnalyticAt ℂ Z y :=
      Complex.differentiableOn_sqrt.analyticOnNhd Complex.isOpen_slitPlane y
        (Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith)))
    have ht : AnalyticAt ℂ t y := ratio_analytic hy₀
    have ht_ball : t y ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff]
      change ‖(1 - y) / y‖ < 1
      rw [norm_div, div_lt_one (norm_pos_iff.mpr hy₀)]
      exact (norm_one_sub_lt_iff y).mpr hre
    exact (hZ.zpow (n := (N : ℤ) - L) hz₀).mul ((hA_analytic _ ht_ball).comp ht)
  · intro z hz
    have hSeries : HasFPowerSeriesAt A (FormalMultilinearSeries.ofScalars ℂ Acoeff) 0 := by
      simpa only [A, Acoeff, hw, hb] using
        fixedAIterate_negative_square_germ false M K L N u v
          (V .P) (V .Q) (V .R) (V .S) p q r d huG hvG hu hv hRG hSG hMK
    have hEq := hSeries.analyticAt.hasFPowerSeriesAt.eq_formalMultilinearSeries hSeries
    refine (scalar_taylor_hasSum hA_diff hz).congr_fun fun E => ?_
    have hCoeff : coefficient E A = Acoeff E := by
      simpa only [FormalMultilinearSeries.coeff_ofScalars, coefficient] using
        congrArg (fun series => FormalMultilinearSeries.coeff series E) hEq
    rw [hCoeff]
  · intro y him hre
    obtain ⟨hy₀, hy₁, ht₁⟩ := right_ratio him hre
    let ξ := D y / Z y
    have hz₀ : Z y ≠ 0 := fun h => hy₀ (by simpa [Z, h] using (sqrt_square y).symm)
    have hξsq : ξ ^ (2 : ℕ) = t y := by
      dsimp only [ξ, D, Z, t]
      rw [div_pow, sqrt_square, sqrt_square]
    obtain ⟨hξ₀, hξ₁⟩ := square_root_disk hξsq (div_ne_zero hy₁ hy₀) ht₁
    have hLift : Z y * ξ = D y := mul_div_cancel₀ (D y) hz₀
    have hIter := fixedAIterate_hasSum false M K L N u v (V .P) (V .Q) (V .R) (V .S) p q r d
      huG hvG hu hv hRG hSG hMK hξ₀ hξ₁
    rw [hξsq] at hIter
    have hIter' : HasSum (fun j : ℤ => fixedAIterateCoeff false M K L N j u v w.val b.val * ξ ^ j)
        (ξ ^ (-a) * A (t y)) := by
      simpa only [a, A, hw, hb] using hIter
    have hJoint := a_joint_from_diagonal M K L N u v w b huG hvG hwG hbG hM hK hz₀ hIter'
    rw [hLift] at hJoint
    have hFixed := hhbb_upper_fixed_d_joint_hasSum M K L N u v w b huG hvG hwG hbG
      (Ne.symm (sub_ne_zero.mp hy₁)) hre
    have hFixedValue := hbhb_marked_d_hasSum_upper_right slot colour n l hl hpar
      u v w b p q r d hu hv hw hb him hre
    have hCommon : (∑' i, NativeMixedComplexSewing.aJointTerm u v w b (D y) (Z y) i) = F y :=
      hFixed.unique hFixedValue
    have hValue : Z y ^ ((N : ℤ) - L - a) * (ξ ^ (-a) * A (t y)) = F y :=
      hJoint.tsum_eq.symm.trans hCommon
    refine ⟨hValue ▸ hJoint, ?_⟩
    rw [← hValue, ← hLift, mul_zpow]
    calc
      _ = (Z y ^ a * Z y ^ ((N : ℤ) - L - a)) * (ξ ^ a * ξ ^ (-a)) * A (t y) := by ring
      _ = G₁ y := by
        change _ = Z y ^ ((N : ℤ) - L) * A (t y)
        rw [← zpow_add₀ hz₀, ← zpow_add₀ hξ₀, add_neg_cancel, zpow_zero, mul_one,
          show a + ((N : ℤ) - L - a) = (N : ℤ) - L by ring]
  · intro y hy
    exact (analyticAt_const (v := phaseInf)).mul
      (hNumInf.analyticOnNhd isOpen_slitDomain y (ball_subset_slitDomain hy))
  · exact hDEnergy
  · intro y him hy
    have hy₀ : y ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans hy)
    have hz₀ : Z y ≠ 0 := fun h => hy₀ (by simpa [Z, h] using (sqrt_square y).symm)
    have hyInv : y⁻¹ ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, norm_inv]
      exact inv_lt_one_of_one_lt₀ hy
    have hRaw := hhbb_marked_rawD_hasSum_upper_exterior slot colour n l hpar
      u v w b p q r d hu hv hw hb him hy
    let slitD := dSlitProduct M K L N (V .P) (V .Q) (V .R) (V .S) p q r d y⁻¹
    have hCommon : y ^ (-s) * slitD = F y := hCross.2.2 him
    have hArg : y.arg ≠ Real.pi := fun h => him.ne' (Complex.arg_eq_pi_iff.mp h).2
    have hρ : (y⁻¹) ^ (1 / 2 : ℂ) = (Z y)⁻¹ := by
      simpa only [Z, Complex.sqrt, one_div] using Complex.inv_cpow y (1 / 2 : ℂ) hArg
    have hzSq : Z y ^ (2 : ℕ) = y := sqrt_square y
    have hρsq : ((Z y)⁻¹) ^ (2 : ℕ) = y⁻¹ := by rw [inv_pow, hzSq]
    have hEnergy := hRaw.2
    change HasSum (fun E : ℕ => Dcoeff E * ((y⁻¹) ^ (1 / 2 : ℂ)) ^
      (2 * (E : ℤ) - e)) slitD at hEnergy
    rw [hρ] at hEnergy
    have hScale : Z y ^ ((K : ℤ) - N) * y ^ (-s) * ((Z y)⁻¹) ^ (-e) = 1 := by
      have hExp : ((K : ℤ) - N) + 2 * (-s) + e = 0 := by
        dsimp only [s, sigma, e]
        omega
      have hOuter : Z y ^ (2 * (-s)) = y ^ (-s) := by rw [zpow_double, hzSq]
      rw [← hOuter, inv_zpow', neg_neg,
        ← zpow_add₀ hz₀, ← zpow_add₀ hz₀, hExp, zpow_zero]
    have hNorm : HasSum (fun E : ℕ => Dcoeff E * y⁻¹ ^ E)
        (Z y ^ ((K : ℤ) - N) * F y) := by
      rw [← hCommon, ← mul_assoc]
      refine (hEnergy.mul_left (Z y ^ ((K : ℤ) - N) * y ^ (-s))).congr_fun ?_
      intro E
      symm
      rw [shifted_energy_power (inv_ne_zero hz₀), hρsq]
      calc
        _ = (Z y ^ ((K : ℤ) - N) * y ^ (-s) * ((Z y)⁻¹) ^ (-e)) *
            (Dcoeff E * y⁻¹ ^ E) := by ring
        _ = _ := by rw [hScale, one_mul]
    refine ⟨hCommon ▸ hRaw.1, ?_⟩
    exact hNorm.unique (hDEnergy _ hyInv)

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBUpperCuspGerms
