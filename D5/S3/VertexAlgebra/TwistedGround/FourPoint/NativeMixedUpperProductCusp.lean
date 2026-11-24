/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedUpperProductCusp
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedUpperProductCusp
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual mixed Leech upper right-skew product sums to the B sewn cusp germ. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedWickCuspGerm
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedWickChartTransport
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMVariableSupport
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.TaylorSeries

/-! The upper-branch B product, with native order (Q, R, P, S). -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators Topology TensorProduct VertexOperator
open Filter Metric

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedUpperProductCusp

open Complex (I)
open LatticeGeneratingFieldLocality LatticeHalfFock LatticePositiveEnergy
open ActualEnergyRestrictedDual (maxOddWeight)
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockGradedTrace
open LatticeTwistedGroundRealization LatticeTwistedGroundRealization.SignQuotient
open ActualLeechHyperbolic (leechData leech_spec)
open ActualChargedAdjoint (actualForm)
open ActualOddGradeOrthogonality (actualForm_oddGrade_orthogonal)
open Orbifold.NativeOddTwistedIntertwiner (Twisted OddCarrier leechUnit)
open Orbifold.NativeOddUpperRightSkew (rightField rightField_coeff rightField_even_zero R_pairing_finite)
open Orbifold.NativeMixedPairField (mu mu_coeff_of_grade mu_coeff_even_zero mu_lower_truncation)
open Orbifold.NativeMixedPairState (mixedPairWeight mixedPairState_grade)
open OriginalFourMVariableSupport (occupationReadout inverseFlow nativeSector
  nativePuncture wordAt loweredOscillator)
open OriginalFourMChargeCoset (oscillatorLower)
open OriginalFourMChargeGerm (chargeSectorSewn)
open OriginalFourMSectorContinuation (slitChargeTerm slitChargeTerm_eq_native
  slitChargeSector slitChargeSector_differentiableOn)
open OriginalGaussianSewnAnalytic (coefficient)
open OriginalFourMActualChart (Chart Puncture loweringParameter)
open NativeMixedWickCuspGerm (mixedOccupationSewn mixedSewn mixedSewn_analyticAt
  mixedR_pairing_eq_sewn_coefficient)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod
  (slitDomain isOpen_slitDomain ball_subset_slitDomain)

open private J_energy from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
open private actualGrade_eigen from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
open private T lowering_eigen from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private mixedGroundWeight maxOddWeight_le_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedWickCuspGerm
open private analytic_neg_square_even_part coefficient_fun_sum coefficient_const_mul from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMChargeGerm
open private occupationLast_apply punctureLowering_eq_word from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeLaurent

/-- The original coefficient of the B product. The first field has doubled
exponent `2E-(6+K+L)` and the right-skew field has doubled exponent `N-M-2E`. -/
def bProductCoeff (s t : Bool) (M K L N : ℕ)
    (v : Twisted leechData leechUnit s) (w : Twisted leechData leechUnit (!s))
    (u : Twisted leechData leechUnit t) (b : Twisted leechData leechUnit (!t))
    (E : ℕ) : ℂ :=
  actualForm leechData leechUnit b.val
    ((rightField leechData leechUnit t u).coeff ((N : ℤ) - M - 2 * (E : ℤ))
      ((mu s v).coeff (2 * (E : ℤ) - (6 + (K : ℤ) + L)) w)).val

/-- The inner field vanishes outside the doubled B energy lattice. -/
theorem b_inner_coeff_off_grid (s : Bool) (K L : ℕ)
    (v : Twisted leechData leechUnit s) (w : Twisted leechData leechUnit (!s))
    (hv : v.val ∈ actualGrade leechData leechUnit K)
    (hw : w.val ∈ actualGrade leechData leechUnit L)
    (hKL : Odd ((K : ℤ) + L)) (j : ℤ)
    (hj : ∀ E : ℕ, j ≠ 2 * (E : ℤ) - (6 + (K : ℤ) + L)) :
    (mu s v).coeff j w = 0 := by
  by_cases he : Even j
  · exact mu_coeff_even_zero s j v w he
  · have hbelow : j < -(6 + (K : ℤ) + L) := by
      by_contra! h
      apply hj ((j + (6 + (K : ℤ) + L)) / 2).toNat
      obtain ⟨k, hk⟩ := hKL
      obtain ⟨m, hm⟩ := Int.not_even_iff_odd.mp he
      omega
    have hK : (maxOddWeight leechData leechUnit v.val : ℤ) ≤ (K : ℤ) := by
      exact_mod_cast maxOddWeight_le_grade hv
    have hL : (maxOddWeight leechData leechUnit w.val : ℤ) ≤ (L : ℤ) := by
      exact_mod_cast maxOddWeight_le_grade hw
    exact mu_lower_truncation s v w j (by omega)

/-- The B slit occupation on the original ordered slots, including the
detector inverse flow and both inverse flows at the mixed insertion. -/
def bSlitOccupation (K L N : ℕ) (P Q U S : Oscillator leechData)
    (a : ModTwoCharge leechData) (z : ℂ) : ℂ :=
  occupationReadout leechData (inverseFlow leechData (K / 2 + 1) Q)
    (inverseFlow leechData (L / 2 + 1) U) P (inverseFlow leechData (N / 2 + 1) S)
    (fun β γ δ η => slitChargeSector leechData a β γ δ η z)

/-- The holomorphic numerator before the common B chart phase. -/
def bSewnNumerator (K L N : ℕ) (P Q U S : Oscillator leechData)
    (p q r d : ActualGround leechData leechUnit) (z : ℂ) : ℂ :=
  ∑ a : ModTwoCharge leechData, mixedGroundWeight q r p d a *
    bSlitOccupation K L N P Q U S a z

private theorem bSewnNumerator_differentiableOn (K L N : ℕ) (P Q U S : Oscillator leechData)
    (p q r d : ActualGround leechData leechUnit) :
    DifferentiableOn ℂ (bSewnNumerator K L N P Q U S p q r d) slitDomain := by
  classical
  have hsector (a : ModTwoCharge leechData) (β γ δ η : Exponent leechData) :
      DifferentiableOn ℂ (slitChargeSector leechData a β γ δ η) slitDomain :=
    slitChargeSector_differentiableOn leechData leech_spec.2.2.1 a β γ δ η
  unfold bSewnNumerator bSlitOccupation occupationReadout
  fun_prop

theorem bSewnNumerator_analyticAt (K L N : ℕ) (P Q U S : Oscillator leechData)
    (p q r d : ActualGround leechData leechUnit) :
    AnalyticAt ℂ (bSewnNumerator K L N P Q U S p q r d) 0 :=
  DifferentiableOn.analyticOnNhd (bSewnNumerator_differentiableOn K L N P Q U S p q r d)
    isOpen_slitDomain 0 (ball_subset_slitDomain (Metric.mem_ball_self zero_lt_one))

private def detectorSewn (K L N : ℕ) (P Q U S : Oscillator leechData)
    (p q r d : ActualGround leechData leechUnit) (ρ : ℂ) : ℂ :=
  ∑ ell ∈ Finset.range (N / 2 + 1), ((-1 : ℂ) ^ ell * (ell.factorial : ℂ)⁻¹) *
    mixedSewn K L Q U P ((oscillatorLower leechData ^ ell) S) q r p d ρ

private theorem detectorSewn_analyticAt (K L N : ℕ) (P Q U S : Oscillator leechData)
    (p q r d : ActualGround leechData leechUnit) :
    AnalyticAt ℂ (detectorSewn K L N P Q U S p q r d) 0 := by
  have hsector (ell : ℕ) :
      AnalyticAt ℂ (mixedSewn K L Q U P ((oscillatorLower leechData ^ ell) S) q r p d) 0 :=
    mixedSewn_analyticAt K L Q U P _ q r p d
  unfold detectorSewn
  fun_prop

private theorem slitSector_square (a : ModTwoCharge leechData) (β γ δ η : Exponent leechData)
    {ρ : ℂ} (hρ : ‖ρ‖ < 1) :
    slitChargeSector leechData a β γ δ η (ρ ^ 2) =
      chargeSectorSewn leechData a β γ δ η ρ := by
  classical
  unfold slitChargeSector chargeSectorSewn
  apply tsum_congr
  intro c
  by_cases hc : reduceCharge leechData c = a
  · simp only [hc, ite_true]
    exact slitChargeTerm_eq_native leechData leech_spec.1 β γ δ η c
      (chargeEnergy_nonneg leechData leech_spec.2.2.1 c) hρ
  · simp only [hc, ite_false]

private theorem detectorSewn_eq (K L N : ℕ) (P Q U S : Oscillator leechData)
    (p q r d : ActualGround leechData leechUnit) {ρ : ℂ} (hρ : ‖ρ‖ < 1) :
    detectorSewn K L N P Q U S p q r d ρ =
      I ^ ((L : ℤ) - 2 * (K : ℤ) - 3) * bSewnNumerator K L N P Q U S p q r d (ρ ^ 2) := by
  classical
  let W (a : ModTwoCharge leechData) (V : Oscillator leechData) :=
    occupationReadout leechData (inverseFlow leechData (K / 2 + 1) Q)
      (inverseFlow leechData (L / 2 + 1) U) P V
      (fun β γ δ η => slitChargeSector leechData a β γ δ η (ρ ^ 2))
  have hsector (a : ModTwoCharge leechData) (V : Oscillator leechData) :
      mixedOccupationSewn K L Q U P V a ρ = W a V := by
    have h (β γ δ η : Exponent leechData) := slitSector_square a β γ δ η hρ
    simp only [mixedOccupationSewn, W, h]
  have hlast (a : ModTwoCharge leechData) :
      W a (inverseFlow leechData (N / 2 + 1) S) =
        ∑ ell ∈ Finset.range (N / 2 + 1), ((-1 : ℂ) ^ ell * (ell.factorial : ℂ)⁻¹) *
          W a ((oscillatorLower leechData ^ ell) S) := by
    dsimp only [W]
    simp only [← occupationLast_apply, inverseFlow, map_sum, map_smul, smul_eq_mul, div_eq_mul_inv]
  unfold detectorSewn mixedSewn bSewnNumerator
  simp only [hsector]
  change _ = I ^ ((L : ℤ) - 2 * (K : ℤ) - 3) *
    ∑ a, mixedGroundWeight q r p d a * W a (inverseFlow leechData (N / 2 + 1) S)
  simp only [hlast, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun ell _ => ?_
  ring

theorem bProductCoeff_eq_taylor (s t : Bool) (M K L N : ℕ)
    (v : Twisted leechData leechUnit s) (w : Twisted leechData leechUnit (!s))
    (u : Twisted leechData leechUnit t) (b : Twisted leechData leechUnit (!t))
    (P Q U S : Oscillator leechData) (p q r d : ActualGround leechData leechUnit)
    (hv : v.val ∈ actualGrade leechData leechUnit K)
    (hw : w.val ∈ actualGrade leechData leechUnit L)
    (hu : u.val ∈ actualGrade leechData leechUnit M)
    (hb : b.val ∈ actualGrade leechData leechUnit N)
    (hvQ : v.val = Q ⊗ₜ[ℂ] q) (hwU : w.val = U ⊗ₜ[ℂ] r)
    (huP : u.val = P ⊗ₜ[ℂ] p) (hbS : b.val = S ⊗ₜ[ℂ] d)
    (hKL : Odd ((K : ℤ) + L)) (hNM : Odd ((N : ℤ) - M)) (E : ℕ) :
    bProductCoeff s t M K L N v w u b E =
      I ^ ((N : ℤ) - M) * coefficient (2 * E)
        (detectorSewn K L N P Q U S p q r d) := by
  let n₀ : ℤ := ((M : ℤ) - (N : ℤ) - 3) / 2
  let m : ℤ := ((K : ℤ) + (L : ℤ) + 3) / 2 - (E : ℤ)
  have hn₀ : -2 * n₀ - 3 = (N : ℤ) - M := by
    obtain ⟨k, hk⟩ := hNM
    dsimp only [n₀]
    omega
  have hright : -2 * (n₀ + (E : ℤ)) - 3 = (N : ℤ) - M - 2 * (E : ℤ) := by omega
  have hleft : -2 * m - 3 = 2 * (E : ℤ) - (6 + (K : ℤ) + L) := by
    obtain ⟨k, hk⟩ := hKL
    dsimp only [m]
    omega
  unfold bProductCoeff detectorSewn
  rw [← hright, rightField_coeff, ← hleft, coefficient_fun_sum]
  · simp only [coefficient_const_mul]
    exact mixedR_pairing_eq_sewn_coefficient s t K L M N E n₀ v w u b Q U P S q r p d
      hv hw hu hb hvQ hwU huP hbS hKL hn₀
  · intro ell _
    have h := mixedSewn_analyticAt K L Q U P ((oscillatorLower leechData ^ ell) S) q r p d
    fun_prop

/-- The even detector Taylor coefficient is the corresponding coefficient
of the slit numerator with the detector phase. -/
private theorem bDetector_coefficient (K L N : ℕ)
    (P Q U S : Oscillator leechData) (p q r d : ActualGround leechData leechUnit) (E : ℕ) :
    coefficient (2 * E) (detectorSewn K L N P Q U S p q r d) =
      I ^ ((L : ℤ) - 2 * (K : ℤ) - 3) * coefficient E (bSewnNumerator K L N P Q U S p q r d) := by
  let F := detectorSewn K L N P Q U S p q r d
  let B := bSewnNumerator K L N P Q U S p q r d
  let phase := I ^ ((L : ℤ) - 2 * (K : ℤ) - 3)
  obtain ⟨G, hG, hpull⟩ :=
    analytic_neg_square_even_part (detectorSewn_analyticAt K L N P Q U S p q r d)
  have hSquare : ∀ᶠ ρ : ℂ in 𝓝 0, G (-(ρ ^ 2)) = phase * B (ρ ^ 2) := by
    filter_upwards [hpull, ball_mem_nhds (0 : ℂ) zero_lt_one] with ρ hρ hball
    have hn : ‖ρ‖ < 1 := mem_ball_zero_iff.mp hball
    rw [hρ, detectorSewn_eq K L N P Q U S p q r d hn,
      detectorSewn_eq K L N P Q U S p q r d (ρ := -ρ) (by simpa only [norm_neg] using hn),
      neg_sq]
    change (phase * B (ρ ^ 2) + phase * B (ρ ^ 2)) / 2 = phase * B (ρ ^ 2)
    ring
  have hlocal : G =ᶠ[𝓝 0] fun z => phase * B (-z) := by
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hSquare
    refine Metric.eventually_nhds_iff_ball.mpr ⟨δ ^ 2, sq_pos_of_pos hδ, ?_⟩
    intro z hz
    obtain ⟨ρ, hρ⟩ := IsAlgClosed.exists_pow_nat_eq (-z) (n := 2) zero_lt_two
    have hsmall : ‖ρ‖ < δ := by
      apply (sq_lt_sq₀ (norm_nonneg ρ) hδ.le).mp
      rw [← norm_pow, hρ, norm_neg]
      exact mem_ball_zero_iff.mp hz
    simpa only [hρ, neg_neg] using hball ρ (mem_ball_zero_iff.mpr hsmall)
  have hseries := hG.congr hlocal
  have hcoef : coefficient E (fun z => phase * B (-z)) = (-1 : ℂ) ^ E * coefficient (2 * E) F := by
    have heq := hseries.analyticAt.hasFPowerSeriesAt.eq_formalMultilinearSeries hseries
    simpa only [FormalMultilinearSeries.coeff_ofScalars, coefficient] using
      congrArg (fun series => FormalMultilinearSeries.coeff series E) heq
  have hneg : coefficient E (fun z => B (-z)) = (-1 : ℂ) ^ E * coefficient E B := by
    unfold coefficient
    rw [iteratedDeriv_comp_neg, neg_zero, smul_eq_mul, mul_div_assoc]
  rw [coefficient_const_mul, hneg] at hcoef
  change coefficient (2 * E) F = phase * coefficient E B
  apply mul_left_cancel₀ (pow_ne_zero E (by norm_num : (-1 : ℂ) ≠ 0))
  calc
    (-1 : ℂ) ^ E * coefficient (2 * E) F = phase * ((-1 : ℂ) ^ E * coefficient E B) :=
      hcoef.symm
    _ = _ := by ring

/-- The original B energy diagonal sums on the punctured unit disk of the
physical doubled coordinate. The sewn numerator is evaluated at its square. -/
theorem b_product_hasSum_complex (s t : Bool) (M K L N : ℕ)
    (v : Twisted leechData leechUnit s) (w : Twisted leechData leechUnit (!s))
    (u : Twisted leechData leechUnit t) (b : Twisted leechData leechUnit (!t))
    (P Q U S : Oscillator leechData) (p q r d : ActualGround leechData leechUnit)
    (hv : v.val ∈ actualGrade leechData leechUnit K)
    (hw : w.val ∈ actualGrade leechData leechUnit L)
    (hu : u.val ∈ actualGrade leechData leechUnit M)
    (hb : b.val ∈ actualGrade leechData leechUnit N)
    (hvQ : v.val = Q ⊗ₜ[ℂ] q) (hwU : w.val = U ⊗ₜ[ℂ] r)
    (huP : u.val = P ⊗ₜ[ℂ] p) (hbS : b.val = S ⊗ₜ[ℂ] d)
    (hKL : Odd ((K : ℤ) + L)) (hNM : Odd ((N : ℤ) - M))
    {ρ : ℂ} (hρ₀ : 0 < ‖ρ‖) (hρ₁ : ‖ρ‖ < 1) :
    HasSum (fun E : ℕ => bProductCoeff s t M K L N v w u b E *
      ρ ^ (2 * (E : ℤ) - (6 + (K : ℤ) + L)))
      (ρ ^ (-(6 + (K : ℤ) + L)) *
        I ^ ((L : ℤ) + N - M - 2 * (K : ℤ) - 3) *
        bSewnNumerator K L N P Q U S p q r d (ρ ^ 2)) := by
  let B := bSewnNumerator K L N P Q U S p q r d
  let A : ℤ := 6 + (K : ℤ) + L
  let phase : ℤ := (L : ℤ) + N - M - 2 * (K : ℤ) - 3
  have hρ : ρ ≠ 0 := norm_pos_iff.mp hρ₀
  have hdiff : DifferentiableOn ℂ B (ball (0 : ℂ) 1) :=
    (bSewnNumerator_differentiableOn K L N P Q U S p q r d).mono ball_subset_slitDomain
  have hball : ρ ^ 2 ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_pow]
    exact pow_lt_one₀ (norm_nonneg ρ) hρ₁ (by decide)
  have htaylor : HasSum (fun E : ℕ => coefficient E B * (ρ ^ (2 : ℕ)) ^ E) (B (ρ ^ 2)) := by
    refine (Complex.hasSum_taylorSeries_on_ball hdiff hball).congr_fun ?_
    intro E
    simp only [coefficient, sub_zero, smul_eq_mul, div_eq_mul_inv]
    ring
  refine (htaylor.mul_left (ρ ^ (-A) * I ^ phase)).congr_fun fun E => ?_
  have hpow : ρ ^ (2 * (E : ℤ) - A) = ρ ^ (-A) * (ρ ^ (2 : ℕ)) ^ E := by
    rw [show 2 * (E : ℤ) - A = -A + 2 * (E : ℤ) by ring,
      zpow_add₀ hρ, zpow_mul, zpow_natCast _ E]
    rfl
  rw [bProductCoeff_eq_taylor s t M K L N v w u b P Q U S p q r d
    hv hw hu hb hvQ hwU huP hbS hKL hNM E, bDetector_coefficient, ← mul_assoc,
    ← zpow_add₀ Complex.I_ne_zero, hpow]
  have hphase : (N : ℤ) - M + ((L : ℤ) - 2 * (K : ℤ) - 3) = phase := by
    dsimp only [phase]
    ring
  rw [hphase]
  change I ^ phase * coefficient E B * (ρ ^ (-A) * (ρ ^ (2 : ℕ)) ^ E) = _
  ring

/-- On the positive interval the physical root is `sqrt y` and the upper
chart root is `I * sqrt y`. -/
theorem b_upper_product_hasSum_unitInterval (s t : Bool) (M K L N : ℕ)
    (v : Twisted leechData leechUnit s) (w : Twisted leechData leechUnit (!s))
    (u : Twisted leechData leechUnit t) (b : Twisted leechData leechUnit (!t))
    (P Q U S : Oscillator leechData) (p q r d : ActualGround leechData leechUnit)
    (hv : v.val ∈ actualGrade leechData leechUnit K)
    (hw : w.val ∈ actualGrade leechData leechUnit L)
    (hu : u.val ∈ actualGrade leechData leechUnit M)
    (hb : b.val ∈ actualGrade leechData leechUnit N)
    (hvQ : v.val = Q ⊗ₜ[ℂ] q) (hwU : w.val = U ⊗ₜ[ℂ] r)
    (huP : u.val = P ⊗ₜ[ℂ] p) (hbS : b.val = S ⊗ₜ[ℂ] d)
    (hKL : Odd ((K : ℤ) + L)) (hNM : Odd ((N : ℤ) - M))
    {y : ℝ} (hy : 0 < y) (hy₁ : y < 1) :
    HasSum (fun E : ℕ => bProductCoeff s t M K L N v w u b E *
      (Real.sqrt y : ℂ) ^ (2 * (E : ℤ) - (6 + (K : ℤ) + L)))
      ((I * (Real.sqrt y : ℂ)) ^ (-(6 + (K : ℤ) + L)) *
        I ^ (3 + 2 * (L : ℤ) + N - M - K) * bSewnNumerator K L N P Q U S p q r d y) := by
  let x : ℂ := Real.sqrt y
  let A : ℤ := 6 + (K : ℤ) + L
  have hx₀ : 0 < ‖x‖ := norm_pos_iff.mpr (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hy).ne')
  have hx₁ : ‖x‖ < 1 := by
    change ‖(Real.sqrt y : ℂ)‖ < 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg y)]
    exact (Real.sqrt_lt' zero_lt_one).2 (by simpa using hy₁)
  have hsq : x ^ 2 = (y : ℂ) := by
    change ((Real.sqrt y : ℝ) : ℂ) ^ (2 : ℕ) = (y : ℂ)
    rw [← Complex.ofReal_pow, Real.sq_sqrt hy.le]
  have hphase :
      (I * x) ^ (-A) * I ^ (3 + 2 * (L : ℤ) + N - M - K) =
        x ^ (-A) * I ^ ((L : ℤ) + N - M - 2 * (K : ℤ) - 3) := by
    rw [mul_zpow]
    calc
      _ = x ^ (-A) * (I ^ (-A) * I ^ (3 + 2 * (L : ℤ) + N - M - K)) := by ring
      _ = _ := by
        rw [← zpow_add₀ Complex.I_ne_zero]
        rw [show -A + (3 + 2 * (L : ℤ) + N - M - K) =
          (L : ℤ) + N - M - 2 * (K : ℤ) - 3 by dsimp only [A]; ring]
  change HasSum _ ((I * x) ^ (-A) * I ^ (3 + 2 * (L : ℤ) + N - M - K) * _)
  rw [hphase, ← hsq]
  exact b_product_hasSum_complex s t M K L N v w u b P Q U S p q r d
    hv hw hu hb hvQ hwU huP hbS hKL hNM hx₀ hx₁

/-- The original B energy diagonal converges near the positive cusp. Its
positive physical coordinate has root `sqrt y`. In the upper root of minus
that coordinate, the Laurent factor is `(I * sqrt y)^(-(6+K+L))`. -/
theorem b_upper_product_hasSum (s t : Bool) (M K L N : ℕ)
    (v : Twisted leechData leechUnit s) (w : Twisted leechData leechUnit (!s))
    (u : Twisted leechData leechUnit t) (b : Twisted leechData leechUnit (!t))
    (P Q U S : Oscillator leechData) (p q r d : ActualGround leechData leechUnit)
    (hv : v.val ∈ actualGrade leechData leechUnit K)
    (hw : w.val ∈ actualGrade leechData leechUnit L)
    (hu : u.val ∈ actualGrade leechData leechUnit M)
    (hb : b.val ∈ actualGrade leechData leechUnit N)
    (hvQ : v.val = Q ⊗ₜ[ℂ] q) (hwU : w.val = U ⊗ₜ[ℂ] r)
    (huP : u.val = P ⊗ₜ[ℂ] p) (hbS : b.val = S ⊗ₜ[ℂ] d)
    (hKL : Odd ((K : ℤ) + L)) (hNM : Odd ((N : ℤ) - M)) :
    ∀ᶠ y in 𝓝 (0 : ℝ), 0 < y →
      HasSum (fun E : ℕ => bProductCoeff s t M K L N v w u b E *
        (Real.sqrt y : ℂ) ^ (2 * (E : ℤ) - (6 + (K : ℤ) + L)))
        ((I * (Real.sqrt y : ℂ)) ^ (-(6 + (K : ℤ) + L)) *
          I ^ (3 + 2 * (L : ℤ) + N - M - K) * bSewnNumerator K L N P Q U S p q r d y) := by
  filter_upwards [gt_mem_nhds (show (0 : ℝ) < 1 from zero_lt_one)] with y hy₁ hy
  exact b_upper_product_hasSum_unitInterval s t M K L N v w u b P Q U S p q r d
    hv hw hu hb hvQ hwU huP hbS hKL hNM hy hy₁

/-- A term of the actual B product at independent doubled modes, with
`xRoot ^ 2 = x` and `zRoot ^ 2 = z`. -/
def bJointTerm (s t : Bool)
    (v : Twisted leechData leechUnit s) (w : Twisted leechData leechUnit (!s))
    (u : Twisted leechData leechUnit t) (b : Twisted leechData leechUnit (!t))
    (xRoot zRoot : ℂ) (i : ℤ × ℤ) : ℂ :=
  actualForm leechData leechUnit b.val
    ((rightField leechData leechUnit t u).coeff i.2 ((mu s v).coeff i.1 w)).val *
      (zRoot ^ i.1 * xRoot ^ i.2)

private theorem b_inner_energy (s : Bool) (K L E : ℕ)
    (v : Twisted leechData leechUnit s) (w : Twisted leechData leechUnit (!s))
    (hv : v.val ∈ actualGrade leechData leechUnit K)
    (hw : w.val ∈ actualGrade leechData leechUnit L)
    (hKL : Odd ((K : ℤ) + L)) :
    ((mu s v).coeff (2 * (E : ℤ) - (6 + (K : ℤ) + L)) w).val ∈
      grade leechData (E : ℤ) := by
  let m : ℤ := ((K : ℤ) + L + 3) / 2 - (E : ℤ)
  have hj : 2 * (E : ℤ) - (6 + (K : ℤ) + L) = -2 * m - 3 := by
    obtain ⟨k, hk⟩ := hKL
    dsimp only [m]
    omega
  have hgrade : mixedPairWeight K L m = (E : ℤ) := by
    obtain ⟨k, hk⟩ := hKL
    unfold mixedPairWeight m
    omega
  rw [hj, mu_coeff_of_grade s K L m v w hv hw, ← hgrade]
  exact mixedPairState_grade s K L m v w

private theorem b_outer_pairing_off_grid (t : Bool) (M N E : ℕ)
    (u : Twisted leechData leechUnit t) (b : Twisted leechData leechUnit (!t))
    (hu : u.val ∈ actualGrade leechData leechUnit M)
    (hb : b.val ∈ actualGrade leechData leechUnit N)
    (a : OddCarrier leechData) (ha : a.val ∈ grade leechData (E : ℤ))
    (e : ℤ) (he : e ≠ (N : ℤ) - M - 2 * (E : ℤ)) :
    actualForm leechData leechUnit b.val
      ((rightField leechData leechUnit t u).coeff e a).val = 0 := by
  by_cases hEven : Even e
  · rw [rightField_even_zero leechData leechUnit t e hEven, Submodule.coe_zero, map_zero]
  · obtain ⟨k, hk⟩ := Int.not_even_iff_odd.mp hEven
    let n : ℤ := -k - 2
    have hn : e = -2 * n - 3 := by dsimp only [n]; omega
    rw [hn, rightField_coeff, R_pairing_finite leechData leechUnit t n N u a b hb]
    apply Finset.sum_eq_zero
    intro ell _
    have hbEigen := (actualGrade_eigen leechData leechUnit N b.val).mp hb
    have hlow := lowering_eigen leechData leechUnit (N : ℤ) b.val
      (by simpa only [Int.cast_natCast] using hbEigen) ell
    have hout := J_energy leechData leechUnit t (n + (ell : ℤ)) (E : ℤ) M a u ha hu
    rw [actualForm_oddGrade_orthogonal leechData leechUnit _ _ ((T leechData leechUnit ^ ell) b.val)
      _ hlow hout (by omega), mul_zero]

/-- The B product on the root double cover sums over both doubled modes.
Homogeneity factors out the degree in `xRoot`, leaving the disk series
at the ratio of the two roots. -/
theorem b_joint_product_hasSum (s t : Bool) (M K L N : ℕ)
    (v : Twisted leechData leechUnit s) (w : Twisted leechData leechUnit (!s))
    (u : Twisted leechData leechUnit t) (b : Twisted leechData leechUnit (!t))
    (P Q U S : Oscillator leechData) (p q r d : ActualGround leechData leechUnit)
    (hv : v.val ∈ actualGrade leechData leechUnit K)
    (hw : w.val ∈ actualGrade leechData leechUnit L)
    (hu : u.val ∈ actualGrade leechData leechUnit M)
    (hb : b.val ∈ actualGrade leechData leechUnit N)
    (hvQ : v.val = Q ⊗ₜ[ℂ] q) (hwU : w.val = U ⊗ₜ[ℂ] r)
    (huP : u.val = P ⊗ₜ[ℂ] p) (hbS : b.val = S ⊗ₜ[ℂ] d)
    (hKL : Odd ((K : ℤ) + L)) (hNM : Odd ((N : ℤ) - M))
    {xRoot zRoot : ℂ} (hx : xRoot ≠ 0)
    (hρ₀ : 0 < ‖zRoot / xRoot‖) (hρ₁ : ‖zRoot / xRoot‖ < 1) :
    HasSum (bJointTerm s t v w u b xRoot zRoot)
      (xRoot ^ ((N : ℤ) - M - (6 + (K : ℤ) + L)) *
        ((zRoot / xRoot) ^ (-(6 + (K : ℤ) + L)) *
          I ^ ((L : ℤ) + N - M - 2 * (K : ℤ) - 3) *
          bSewnNumerator K L N P Q U S p q r d ((zRoot / xRoot) ^ 2))) := by
  let A : ℤ := 6 + (K : ℤ) + L
  let j (E : ℕ) : ℤ := 2 * (E : ℤ) - A
  let e (E : ℕ) : ℤ := (N : ℤ) - M - 2 * (E : ℤ)
  let mode (E : ℕ) : ℤ × ℤ := (j E, e E)
  have hinj : Function.Injective mode := by
    intro E F h
    have hmode : j E = j F := congrArg Prod.fst h
    dsimp only [j] at hmode
    omega
  have hzero (i : ℤ × ℤ) (hi : i ∉ Set.range mode) :
      bJointTerm s t v w u b xRoot zRoot i = 0 := by
    rcases i with ⟨a, c⟩
    by_cases ha : ∃ E : ℕ, a = j E
    · obtain ⟨E, rfl⟩ := ha
      have hc : c ≠ e E := fun h => hi ⟨E, Prod.ext rfl h.symm⟩
      have hgrade := b_inner_energy s K L E v w hv hw hKL
      have hout := b_outer_pairing_off_grid t M N E u b hu hb ((mu s v).coeff (j E) w) hgrade c hc
      change _ * (zRoot ^ j E * xRoot ^ c) = 0
      rw [hout, zero_mul]
    · have hinner := b_inner_coeff_off_grid s K L v w hv hw hKL a (fun E h => ha ⟨E, h⟩)
      simp [bJointTerm, hinner]
  apply (hinj.hasSum_iff hzero).mp
  have hsum := b_product_hasSum_complex s t M K L N v w u b P Q U S p q r d
    hv hw hu hb hvQ hwU huP hbS hKL hNM hρ₀ hρ₁
  refine (hsum.mul_left (xRoot ^ ((N : ℤ) - M - A))).congr_fun fun E => ?_
  change bProductCoeff s t M K L N v w u b E * (zRoot ^ j E * xRoot ^ e E) =
    xRoot ^ ((N : ℤ) - M - A) * (bProductCoeff s t M K L N v w u b E * (zRoot / xRoot) ^ j E)
  have hpow : zRoot ^ j E * xRoot ^ e E =
      xRoot ^ ((N : ℤ) - M - A) * (zRoot / xRoot) ^ j E := by
    rw [div_zpow, div_eq_mul_inv, ← zpow_neg]
    calc
      _ = xRoot ^ e E * zRoot ^ j E := mul_comm _ _
      _ = (xRoot ^ ((N : ℤ) - M - A) * xRoot ^ (-j E)) * zRoot ^ j E := by
        rw [← zpow_add₀ hx, show (N : ℤ) - M - A + (-j E) = e E by dsimp only [j, e]; ring]
      _ = _ := by ring
  rw [hpow]
  ring

/-- Reversing the physical `z` root changes the sign of the B product.
The mixed inner field has only odd doubled modes. -/
theorem b_joint_product_neg_root (s t : Bool)
    (v : Twisted leechData leechUnit s) (w : Twisted leechData leechUnit (!s))
    (u : Twisted leechData leechUnit t) (b : Twisted leechData leechUnit (!t))
    (xRoot zRoot : ℂ) :
    (∑' i, bJointTerm s t v w u b xRoot (-zRoot) i) =
      -(∑' i, bJointTerm s t v w u b xRoot zRoot i) := by
  rw [← tsum_neg]
  apply tsum_congr
  intro i
  by_cases hEven : Even i.1
  · simp [bJointTerm, mu_coeff_even_zero s i.1 v w hEven]
  · have hOdd := Int.not_even_iff_odd.mp hEven
    simp only [bJointTerm, hOdd.neg_zpow, neg_mul, mul_neg]

open NativeMixedWickChartTransport (doubledOccupation gaussianOccupation normalizedOccupation
  bpzPhase laurentRoot laurentPower)
open NativeDoubledOccupationReadout (lowering_eq_zero_of_cutoff)
open OriginalFourMCompactLowering (punctureLowering)
open HalfFock.OriginalHalfCurrentWickPolynomial (word eval_word_eq_lowering)
open NativeAffineExternalCoefficient (jetOccupation)

open private oscillatorWord from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeLaurent
open private word_monomial word_weight from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMVariableSupport
open private punctureLowering_eq from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCompactLowering
open private doubledWeight_cast from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient

open Classical in
private def punctureModes {X : Type*} (slot : X → Puncture)
    (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X) (i : Puncture) :
    List (Index leechData) :=
  (l.filter fun a => decide (slot a = i)).map fun a => (colour a, n a)

private def punctureExcitation {X : Type*} (slot : X → Puncture)
    (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X) (i : Puncture) : ℕ :=
  ((punctureModes slot colour n l i).map fun a => 2 * a.2 + 1).sum

private theorem punctureExcitation_cast {X : Type*} (slot : X → Puncture)
    (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X) (i : Puncture) :
    (punctureExcitation slot colour n l i : ℤ) = doubledOccupation slot n l i := by
  classical
  unfold punctureExcitation punctureModes doubledOccupation
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : slot a = i <;> simp [h, Nat.cast_add, Nat.cast_mul] at ih ⊢
    all_goals exact ih

private theorem wordAt_grade {X : Type*} (slot : X → Puncture)
    (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X) (i : Puncture)
    (g : ActualGround leechData leechUnit) :
    wordAt leechData slot colour n l i ⊗ₜ[ℂ] g ∈
      actualGrade leechData leechUnit (punctureExcitation slot colour n l i) := by
  classical
  let V := wordAt leechData slot colour n l i
  let l₀ := punctureModes slot colour n l i
  apply (actual_grade_mem_iff_repr_support leechData leechUnit _ _).mpr
  rintro ⟨β, a⟩ ha
  have hc := Finsupp.mem_support_iff.mp ha
  change (actualAmbientBasis leechData leechUnit).repr (V ⊗ₜ[ℂ] g) (β, a) ≠ 0 at hc
  have hrepr : (actualAmbientBasis leechData leechUnit).repr (V ⊗ₜ[ℂ] g) (β, a) =
      g a * V.coeff β := by
    unfold actualAmbientBasis
    rw [Module.Basis.tensorProduct_repr_tmul_apply]
    rfl
  rw [hrepr] at hc
  have hmem : β ∈ V.support :=
    MvPolynomial.mem_support_iff.mpr (fun h => hc (by rw [h, mul_zero]))
  change β ∈ (oscillatorWord leechData l₀).support at hmem
  rw [word_monomial] at hmem
  have hβ : β = jetOccupation l₀ := by simpa [MvPolynomial.support_monomial] using hmem
  rw [hβ]
  have hweight := word_weight leechData l₀
  rw [doubledWeight_cast] at hweight
  change oddWeight leechData (jetOccupation l₀) = ((l₀.map fun i => 2 * i.2 + 1).sum)
  exact_mod_cast hweight

private theorem b_loweredOscillator_eq_inverseFlow {X : Type*} (slot : X → Puncture)
    (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X) (i : Puncture)
    (hi : loweringParameter .B i = 1) :
    loweredOscillator leechData slot colour .B n l i =
      inverseFlow leechData (punctureExcitation slot colour n l i / 2 + 1)
        (wordAt leechData slot colour n l i) := by
  let modes := punctureModes slot colour n l i
  let H := punctureExcitation slot colour n l i
  let V := wordAt leechData slot colour n l i
  let g : ActualGround leechData leechUnit := fun _ => 1
  have hg : g ≠ 0 := by
    intro h
    have hc := congrFun h (0 : Half (groundRank leechData leechUnit))
    change (1 : ℂ) = 0 at hc
    exact one_ne_zero hc
  let J := max ((word leechData modes).natDegree + 1) (H / 2 + 1)
  have hJ : (word leechData modes).natDegree < J :=
    (Nat.lt_succ_self _).trans_le (le_max_left _ _)
  change punctureLowering leechData .B i modes = inverseFlow leechData (H / 2 + 1) V
  rw [punctureLowering_eq leechData leechUnit, hi,
    eval_word_eq_lowering leechData leechUnit modes _ J hJ]
  unfold inverseFlow
  symm
  apply Finset.sum_subset (Finset.range_mono (le_max_right _ _))
  intro j _ hj
  have hzero := lowering_eq_zero_of_cutoff leechData leechUnit H j V g hg
    (wordAt_grade slot colour n l i g)
    (Nat.le_of_not_gt fun h => hj (Finset.mem_range.mpr h))
  change ((-1 : ℂ) ^ j / (j.factorial : ℂ)) • (oscillatorLower leechData ^ j) V = 0
  rw [hzero, smul_zero]

/-- For the marked oscillator words, the normalized Gaussian B occupation
is the same slit occupation appearing in the concrete product, with exactly
its upper-root Laurent factor and BPZ phase. -/
theorem b_normalizedOccupation_eq {X : Type*} (slot : X → Puncture)
    (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X)
    (y : ℝ) (a : ModTwoCharge leechData) :
    let H := punctureExcitation slot colour n l
    let V := wordAt leechData slot colour n l
    let M := H .P
    let K := H .Q
    let L := H .R
    let N := H .S
    normalizedOccupation leechData slot colour n l .B y a =
      (I * (Real.sqrt y : ℂ)) ^ (-(6 + (K : ℤ) + L)) *
        I ^ (3 + 2 * (L : ℤ) + N - M - K) *
        bSlitOccupation K L N (V .P) (V .Q) (V .R) (V .S) a y := by
  dsimp only
  unfold normalizedOccupation
  simp only [← punctureExcitation_cast slot colour n l, bpzPhase, laurentPower]
  have hroot : laurentRoot .B y = I * (Real.sqrt y : ℂ) := rfl
  rw [hroot]
  have hP : loweredOscillator leechData slot colour .B n l .P =
      wordAt leechData slot colour n l .P :=
    punctureLowering_eq_word leechData .B .P rfl (punctureModes slot colour n l .P)
  have hQ := b_loweredOscillator_eq_inverseFlow slot colour n l .Q rfl
  have hR := b_loweredOscillator_eq_inverseFlow slot colour n l .R rfl
  have hS := b_loweredOscillator_eq_inverseFlow slot colour n l .S rfl
  have hoccupation : gaussianOccupation leechData slot colour n l .B y a =
      bSlitOccupation (punctureExcitation slot colour n l .Q)
        (punctureExcitation slot colour n l .R) (punctureExcitation slot colour n l .S)
        (wordAt leechData slot colour n l .P) (wordAt leechData slot colour n l .Q)
        (wordAt leechData slot colour n l .R) (wordAt leechData slot colour n l .S) a y := by
    change occupationReadout leechData
      (loweredOscillator leechData slot colour .B n l .Q)
      (loweredOscillator leechData slot colour .B n l .R)
      (loweredOscillator leechData slot colour .B n l .P)
      (loweredOscillator leechData slot colour .B n l .S)
      (nativeSector leechData .B y a) = _
    rw [hP, hQ, hR, hS]
    rfl
  rw [hoccupation]
  ring

/-- The ground-form weighted normalized occupation sum is the Laurent value
of the holomorphic numerator used in `b_upper_product_hasSum`. -/
theorem b_weighted_normalizedOccupation_eq {X : Type*} (slot : X → Puncture)
    (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X)
    (p q r d : ActualGround leechData leechUnit) (y : ℝ) :
    let H := punctureExcitation slot colour n l
    let V := wordAt leechData slot colour n l
    let M := H .P
    let K := H .Q
    let L := H .R
    let N := H .S
    (∑ a : ModTwoCharge leechData, mixedGroundWeight q r p d a *
      normalizedOccupation leechData slot colour n l .B y a) =
      (I * (Real.sqrt y : ℂ)) ^ (-(6 + (K : ℤ) + L)) *
        I ^ (3 + 2 * (L : ℤ) + N - M - K) *
        bSewnNumerator K L N (V .P) (V .Q) (V .R) (V .S) p q r d y := by
  classical
  dsimp only
  simp only [b_normalizedOccupation_eq, bSewnNumerator, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedUpperProductCusp
