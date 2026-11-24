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
import Mathlib.Analysis.Complex.CauchyIntegral

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
open Orbifold.NativeOddTwistedIntertwiner (Twisted leechUnit)
open Orbifold.NativeOddUpperRightSkew (rightField rightField_coeff)
open Orbifold.NativeMixedPairField (mu mu_coeff_even_zero mu_lower_truncation)
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

theorem bSewnNumerator_analyticAt (K L N : ℕ) (P Q U S : Oscillator leechData)
    (p q r d : ActualGround leechData leechUnit) :
    AnalyticAt ℂ (bSewnNumerator K L N P Q U S p q r d) 0 := by
  classical
  have hsector (a : ModTwoCharge leechData) (β γ δ η : Exponent leechData) :
      AnalyticAt ℂ (slitChargeSector leechData a β γ δ η) 0 :=
    DifferentiableOn.analyticOnNhd
      (slitChargeSector_differentiableOn leechData leech_spec.2.2.1 a β γ δ η)
      isOpen_slitDomain 0
      (ball_subset_slitDomain (Metric.mem_ball_self zero_lt_one))
  unfold bSewnNumerator bSlitOccupation occupationReadout
  fun_prop

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
  let F := detectorSewn K L N P Q U S p q r d
  let A : ℤ := 6 + (K : ℤ) + L
  obtain ⟨G, hG, hpull⟩ := analytic_neg_square_even_part
    (detectorSewn_analyticAt K L N P Q U S p q r d)
  have hsqrt : Tendsto (fun y : ℝ => (Real.sqrt y : ℂ)) (𝓝 0) (𝓝 0) := by
    simpa only [Real.sqrt_zero, Complex.ofReal_zero, Function.comp_def] using
      (Complex.continuous_ofReal.comp Real.continuous_sqrt).tendsto (0 : ℝ)
  have hneg : Tendsto (fun y : ℝ => -(y : ℂ)) (𝓝 0) (𝓝 0) := by
    have h : Continuous (fun y : ℝ => -(y : ℂ)) := by fun_prop
    simpa only [Complex.ofReal_zero, neg_zero] using
      h.tendsto (0 : ℝ)
  filter_upwards [hneg.eventually hG.eventually_hasSum, hsqrt.eventually hpull,
    hsqrt.eventually_mem (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)]
    with y hsum hpull hball hy
  let x : ℂ := Real.sqrt y
  have hx : x ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hy).ne'
  have hsq : x ^ 2 = (y : ℂ) := by
    change ((Real.sqrt y : ℝ) : ℂ) ^ 2 = (y : ℂ)
    rw [← Complex.ofReal_pow, Real.sq_sqrt hy.le]
  have hsmall : ‖x‖ < 1 := mem_ball_zero_iff.mp hball
  have hsmallneg : ‖-x‖ < 1 := by simpa only [norm_neg] using hsmall
  have hvalue : G (-(y : ℂ)) =
      I ^ ((L : ℤ) - 2 * (K : ℤ) - 3) * bSewnNumerator K L N P Q U S p q r d y := by
    rw [← hsq]
    change G (-(x ^ 2)) = _
    rw [hpull, detectorSewn_eq K L N P Q U S p q r d hsmall,
      detectorSewn_eq K L N P Q U S p q r d hsmallneg, neg_sq]
    ring
  have hnegative : HasSum (fun E : ℕ => ((-1 : ℂ) ^ E * coefficient (2 * E) F) *
      (-(y : ℂ)) ^ E) (G (-(y : ℂ))) := by
    simpa only [zero_add, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using hsum
  have hpositive : HasSum (fun E : ℕ => coefficient (2 * E) F * (y : ℂ) ^ E)
      (G (-(y : ℂ))) := by
    refine hnegative.congr_fun fun E => ?_
    have hsign : (-1 : ℂ) ^ E * (-1 : ℂ) ^ E = 1 := by
      rw [← mul_pow]
      norm_num
    rw [neg_pow]
    calc
      _ = (coefficient (2 * E) F * (y : ℂ) ^ E) * 1 := by ring
      _ = (coefficient (2 * E) F * (y : ℂ) ^ E) * ((-1 : ℂ) ^ E * (-1 : ℂ) ^ E) := by
        rw [hsign]
      _ = _ := by ring
  have hpow (E : ℕ) : x ^ (2 * (E : ℤ) - A) = x ^ (-A) * (y : ℂ) ^ E := by
    rw [show 2 * (E : ℤ) - A = -A + 2 * (E : ℤ) by ring,
      zpow_add₀ hx, zpow_mul, zpow_natCast _ E]
    change x ^ (-A) * (x ^ (2 : ℕ)) ^ E = _
    rw [hsq]
  have hphase :
      (I * x) ^ (-A) * I ^ (3 + 2 * (L : ℤ) + N - M - K) =
        x ^ (-A) * I ^ ((N : ℤ) - M) * I ^ ((L : ℤ) - 2 * (K : ℤ) - 3) := by
    rw [mul_zpow]
    calc
      _ = x ^ (-A) * (I ^ (-A) * I ^ (3 + 2 * (L : ℤ) + N - M - K)) := by ring
      _ = _ := by
        rw [← zpow_add₀ Complex.I_ne_zero, mul_assoc, ← zpow_add₀ Complex.I_ne_zero]
        rw [show -A + (3 + 2 * (L : ℤ) + N - M - K) =
          ((N : ℤ) - M) + ((L : ℤ) - 2 * (K : ℤ) - 3) by
          dsimp only [A]
          ring]
  change HasSum (fun E : ℕ => bProductCoeff s t M K L N v w u b E * x ^ (2 * (E : ℤ) - A))
    ((I * x) ^ (-A) * I ^ (3 + 2 * (L : ℤ) + N - M - K) *
      bSewnNumerator K L N P Q U S p q r d y)
  rw [hphase, mul_assoc (x ^ (-A) * I ^ ((N : ℤ) - M)), ← hvalue]
  refine (hpositive.mul_left (x ^ (-A) * I ^ ((N : ℤ) - M))).congr_fun fun E => ?_
  rw [bProductCoeff_eq_taylor s t M K L N v w u b P Q U S p q r d
    hv hw hu hb hvQ hwU huP hbS hKL hNM, hpow]
  change (I ^ ((N : ℤ) - M) * coefficient (2 * E) F) * (x ^ (-A) * (y : ℂ) ^ E) = _
  ring

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
