/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeFourHUpperProduct
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/NativeFourHUpperProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The native even-intermediate four-H product sums to the continued B Gaussian sector. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedPairAIterate
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHWickChartTransport
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedUpperProductCusp
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeFixedUpperRightSkew
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! The even-intermediate product in the native B order `(Q, R, P, S)`. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators Topology TensorProduct VertexOperator
open Filter Metric

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHUpperProduct

open Complex (I)
open LatticeGeneratingFieldLocality LatticeHalfFock LatticePositiveEnergy
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockGradedTrace LatticeTwistedGroundRealization
open LatticeTwistedGroundRealization.SignQuotient
open ActualLeechHyperbolic (leechData leech_spec)
open ActualChargedAdjoint (actualForm)
open ActualEnergyRestrictedDual (maxOddWeight)
open Orbifold.NativeOddTwistedIntertwiner (Twisted TwistedEven leechUnit)
open Orbifold.NativeFixedPairField (nu nu_coeff_odd_zero nu_lower_truncation)
open Orbifold.NativeFixedUpperRightSkew (rightField rightField_coeff R_pairing_energy_diagonal)
open NativeFixedPairAIterate (fixedAExponent fixedAIterateCoeff fixedAIterateCoeff_eq_sewn_coefficient
  fixedAIterate_hasSum_on_overlap fixedASlitSewn)
open NativeMixedWickCuspGerm (mixedSewn mixedSewn_analyticAt)
open NativeMixedUpperProductCusp (bSewnNumerator bSlitOccupation b_weighted_normalizedOccupation_eq)
open NativeMixedWickChartTransport
  (bpzPhase doubledOccupation gaussianOccupation laurentPower laurentRoot normalizedOccupation sigma)
open NativeFourHWickChartTransport (FourHParity normalized_occupation_fourier_overlap)
open OriginalFourMChargeCoset (oscillatorLower fourierSign quadraticSign ground_exchange_first)
open OriginalFourMVariableSupport (inverseFlow loweredOscillator nativeSector occupationReadout wordAt)
open OriginalFourMSectorContinuation (slitChargeSector slitChargeSector_differentiableOn)
open OriginalFourMActualChart (Chart Puncture loweringParameter parameter)
open OriginalGaussianSewnAnalytic (coefficient)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod (slitDomain ball_subset_slitDomain)

open private actualGrade_eigen from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
open private T lowering_eigen from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private lower_power_tmul from D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset
open private original_ground_dimension from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset
open private maxOddWeight_le_grade mixedGroundWeight from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedWickCuspGerm
open private analytic_neg_square_even_part coefficient_fun_sum coefficient_const_mul from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMChargeGerm
open private detectorSewn detectorSewn_analyticAt detectorSewn_eq punctureExcitation
  punctureExcitation_cast punctureModes wordAt_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedUpperProductCusp

local notation "ℒ" => leechData

/-- Actual composition on the energy diagonal. The inner mode has doubled
exponent `2E - (6+K+L)` and the outer mode has doubled exponent `N-M-2E`. -/
def fixedBProductCoeff (s t : Bool) (M K L N : ℕ)
    (v w : Twisted ℒ leechUnit s) (u b : Twisted ℒ leechUnit t) (E : ℕ) : ℂ :=
  actualForm ℒ leechUnit b.val
    ((rightField ℒ leechUnit t u).coeff ((N : ℤ) - M - 2 * (E : ℤ))
      ((nu s v).coeff (2 * (E : ℤ) - (6 + (K : ℤ) + L)) w)).val

/-- The actual fixed pair vanishes off the doubled B energy grid. -/
theorem fixedB_inner_coeff_off_grid (s : Bool) (K L : ℕ)
    (v w : Twisted ℒ leechUnit s)
    (hv : v.val ∈ actualGrade ℒ leechUnit K) (hw : w.val ∈ actualGrade ℒ leechUnit L)
    (hKL : Even ((K : ℤ) + L)) (j : ℤ)
    (hj : ∀ E : ℕ, j ≠ 2 * (E : ℤ) - (6 + (K : ℤ) + L)) :
    (nu s v).coeff j w = 0 := by
  by_cases he : Even j
  · have hbelow : j < -(6 + (K : ℤ) + L) := by
      by_contra! h
      apply hj ((j + (6 + (K : ℤ) + L)) / 2).toNat
      obtain ⟨i, hi⟩ := he
      obtain ⟨k, hk⟩ := hKL
      omega
    have hK : (maxOddWeight ℒ leechUnit v.val : ℤ) ≤ (K : ℤ) := by
      exact_mod_cast maxOddWeight_le_grade hv
    have hL : (maxOddWeight ℒ leechUnit w.val : ℤ) ≤ (L : ℤ) := by
      exact_mod_cast maxOddWeight_le_grade hw
    exact nu_lower_truncation s v w j (by omega)
  · exact nu_coeff_odd_zero s j v w (Int.not_even_iff_odd.mp he)

/-- On each lowered detector grade, the fixed A coefficient supplies the
pair contraction and its energy sign. That sign cancels the energy part of
the upper right-skew phase. -/
private theorem fixedBProductCoeff_eq_detector (s t : Bool) (M K L N : ℕ)
    (v w : Twisted ℒ leechUnit s) (u b : Twisted ℒ leechUnit t)
    (P Q R S : Oscillator ℒ) (p q r d : ActualGround ℒ leechUnit)
    (hv : v.val ∈ actualGrade ℒ leechUnit K) (hw : w.val ∈ actualGrade ℒ leechUnit L)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    (hvQ : v.val = Q ⊗ₜ[ℂ] q) (hwR : w.val = R ⊗ₜ[ℂ] r)
    (huP : u.val = P ⊗ₜ[ℂ] p) (hbS : b.val = S ⊗ₜ[ℂ] d)
    (hKL : Even ((K : ℤ) + L)) (hNM : Even ((N : ℤ) - M)) (E : ℕ) :
    fixedBProductCoeff s t M K L N v w u b E =
      I ^ ((N : ℤ) - M) * coefficient (2 * E) (detectorSewn K L N P Q R S p q r d) := by
  let n₀ : ℤ := ((M : ℤ) - N - 2) / 2
  have hn₀ : -2 * n₀ - 2 = (N : ℤ) - M := by
    obtain ⟨k, hk⟩ := hNM
    dsimp only [n₀]
    omega
  have hright : -2 * (n₀ + (E : ℤ)) - 2 = (N : ℤ) - M - 2 * (E : ℤ) := by omega
  have hleft : fixedAExponent K L E = 2 * (E : ℤ) - (6 + (K : ℤ) + L) := by
    unfold fixedAExponent
    ring
  have hana (ell : ℕ) (_ : ell ∈ Finset.range (N / 2 + 1)) :
      AnalyticAt ℂ (fun ρ => ((-1 : ℂ) ^ ell * (ell.factorial : ℂ)⁻¹) *
        mixedSewn K L Q R P ((oscillatorLower ℒ ^ ell) S) q r p d ρ) 0 := by
    have h := mixedSewn_analyticAt K L Q R P ((oscillatorLower ℒ ^ ell) S) q r p d
    fun_prop
  unfold fixedBProductCoeff detectorSewn
  rw [← hright, rightField_coeff, ← hleft,
    R_pairing_energy_diagonal ℒ leechUnit t M N E n₀ u _ b.val hb hn₀,
    coefficient_fun_sum _ _ _ hana]
  simp only [coefficient_const_mul]
  apply congrArg (fun value : ℂ => I ^ ((N : ℤ) - M) * value)
  apply Finset.sum_congr rfl
  intro ell hell
  have hellN : 2 * ell ≤ N := by
    have h := Finset.mem_range.mp hell
    omega
  have hgrade : ((N - 2 * ell : ℕ) : ℤ) = (N : ℤ) - 2 * (ell : ℤ) := by omega
  have hbEigen := (actualGrade_eigen ℒ leechUnit N b.val).mp hb
  have hlow := lowering_eigen ℒ leechUnit (N : ℤ) b.val
    (by simpa only [Int.cast_natCast] using hbEigen) ell
  have hS : (oscillatorLower ℒ ^ ell) S ⊗ₜ[ℂ] d ∈ actualGrade ℒ leechUnit (N - 2 * ell) := by
    apply (actualGrade_eigen ℒ leechUnit _ _).mpr
    rw [← hgrade, Int.cast_natCast] at hlow
    simpa only [hbS, T, lower_power_tmul] using hlow
  have hcoeff := fixedAIterateCoeff_eq_sewn_coefficient s K L M (N - 2 * ell) E
    v w Q R P ((oscillatorLower ℒ ^ ell) S) q r p d
    hv hw hvQ hwR (huP ▸ hu) hS hKL
  have he : ((N - 2 * ell : ℕ) : ℤ) - (M : ℤ) -
        (fixedAExponent K L E + ((K : ℤ) + (L : ℤ) + 6)) =
      (N : ℤ) - M - 2 * (E : ℤ) - 2 * (ell : ℤ) := by
    rw [hgrade]
    unfold fixedAExponent
    ring
  unfold fixedAIterateCoeff at hcoeff
  rw [he] at hcoeff
  rw [hbS, T, lower_power_tmul, huP, hcoeff, pow_add]
  have hsign : (-1 : ℂ) ^ E * (-1 : ℂ) ^ E = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = ((-1 : ℂ) ^ E * (-1 : ℂ) ^ E) *
        (((-1 : ℂ) ^ ell * (ell.factorial : ℂ)⁻¹) *
          coefficient (2 * E)
            (mixedSewn K L Q R P ((oscillatorLower ℒ ^ ell) S) q r p d)) := by ring
    _ = _ := by rw [hsign, one_mul]

/-- Descend the even detector germ to the ordinary positive B coordinate. -/
private theorem bDetector_coefficient (K L N : ℕ)
    (P Q R S : Oscillator ℒ) (p q r d : ActualGround ℒ leechUnit) (E : ℕ) :
    coefficient (2 * E) (detectorSewn K L N P Q R S p q r d) =
      I ^ ((L : ℤ) - 2 * (K : ℤ) - 3) * coefficient E (bSewnNumerator K L N P Q R S p q r d) := by
  let F := detectorSewn K L N P Q R S p q r d
  let B := bSewnNumerator K L N P Q R S p q r d
  let phase := I ^ ((L : ℤ) - 2 * (K : ℤ) - 3)
  obtain ⟨G, hG, hpull⟩ :=
    analytic_neg_square_even_part (detectorSewn_analyticAt K L N P Q R S p q r d)
  have hSquare : ∀ᶠ ρ : ℂ in 𝓝 0, G (-(ρ ^ 2)) = phase * B (ρ ^ 2) := by
    filter_upwards [hpull, ball_mem_nhds (0 : ℂ) zero_lt_one] with ρ hρ hball
    have hn : ‖ρ‖ < 1 := mem_ball_zero_iff.mp hball
    rw [hρ, detectorSewn_eq K L N P Q R S p q r d hn,
      detectorSewn_eq K L N P Q R S p q r d (ρ := -ρ) (by simpa only [norm_neg] using hn),
      neg_sq]
    change (phase * B (ρ ^ 2) + phase * B (ρ ^ 2)) / 2 = phase * B (ρ ^ 2)
    ring
  have hsqrt : Tendsto (fun z : ℂ => Complex.sqrt (-z)) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt Complex.sqrt (0 : ℂ) :=
      Complex.continuousAt_sqrt (Or.inl le_rfl)
    have hn : Tendsto (fun z : ℂ => -z) (𝓝 0) (𝓝 0) := by
      simpa only [neg_zero] using continuous_neg.continuousAt (x := (0 : ℂ)).tendsto
    exact (by simpa using hc.tendsto : Tendsto Complex.sqrt (𝓝 (0 : ℂ)) (𝓝 0)).comp hn
  have hlocal : G =ᶠ[𝓝 0] fun z => phase * B (-z) := by
    filter_upwards [hsqrt.eventually hSquare] with z hz
    have hsq : Complex.sqrt (-z) ^ 2 = -z :=
      Complex.cpow_nat_inv_pow (-z) (by norm_num : (2 : ℕ) ≠ 0)
    simpa only [hsq, neg_neg] using hz
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

/-- The actual eigenhomogeneous tensor diagonal equals the Taylor coefficient
of the continued B numerator, with its BPZ phase in the positive root coordinate. -/
theorem fixedBProductCoeff_eq_slit_taylor (s t : Bool) (M K L N : ℕ)
    (v w : Twisted ℒ leechUnit s) (u b : Twisted ℒ leechUnit t)
    (P Q R S : Oscillator ℒ) (p q r d : ActualGround ℒ leechUnit)
    (hv : v.val ∈ actualGrade ℒ leechUnit K) (hw : w.val ∈ actualGrade ℒ leechUnit L)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    (hvQ : v.val = Q ⊗ₜ[ℂ] q) (hwR : w.val = R ⊗ₜ[ℂ] r)
    (huP : u.val = P ⊗ₜ[ℂ] p) (hbS : b.val = S ⊗ₜ[ℂ] d)
    (hKL : Even ((K : ℤ) + L)) (hNM : Even ((N : ℤ) - M)) (E : ℕ) :
    fixedBProductCoeff s t M K L N v w u b E =
      I ^ ((N : ℤ) - M + L - 2 * (K : ℤ) - 3) *
        coefficient E (bSewnNumerator K L N P Q R S p q r d) := by
  rw [fixedBProductCoeff_eq_detector s t M K L N v w u b P Q R S p q r d
    hv hw hu hb hvQ hwR huP hbS hKL hNM E, bDetector_coefficient, ← mul_assoc,
    ← zpow_add₀ Complex.I_ne_zero]
  rw [show (N : ℤ) - M + ((L : ℤ) - 2 * (K : ℤ) - 3) =
    (N : ℤ) - M + L - 2 * (K : ℤ) - 3 by ring]

private theorem bSewnNumerator_differentiableOn (K L N : ℕ)
    (P Q R S : Oscillator ℒ) (p q r d : ActualGround ℒ leechUnit) :
    DifferentiableOn ℂ (bSewnNumerator K L N P Q R S p q r d) slitDomain := by
  classical
  have hsector (a : ModTwoCharge ℒ) (β γ δ η : Exponent ℒ) :
      DifferentiableOn ℂ (slitChargeSector ℒ a β γ δ η) slitDomain :=
    slitChargeSector_differentiableOn ℒ leech_spec.2.2.1 a β γ δ η
  unfold bSewnNumerator bSlitOccupation occupationReadout
  fun_prop

/-- The genuine B energy diagonal sums on the full positive sewing interval.
The change from the positive root to the upper root gives the displayed
phase and leaves the same slit Gaussian numerator. -/
theorem fixedBProduct_hasSum (s t : Bool) (M K L N : ℕ)
    (v w : Twisted ℒ leechUnit s) (u b : Twisted ℒ leechUnit t)
    (P Q R S : Oscillator ℒ) (p q r d : ActualGround ℒ leechUnit)
    (hv : v.val ∈ actualGrade ℒ leechUnit K) (hw : w.val ∈ actualGrade ℒ leechUnit L)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    (hvQ : v.val = Q ⊗ₜ[ℂ] q) (hwR : w.val = R ⊗ₜ[ℂ] r)
    (huP : u.val = P ⊗ₜ[ℂ] p) (hbS : b.val = S ⊗ₜ[ℂ] d)
    (hKL : Even ((K : ℤ) + L)) (hNM : Even ((N : ℤ) - M))
    {y : ℝ} (hy : 0 < y) (hy₁ : y < 1) :
    HasSum (fun E : ℕ => fixedBProductCoeff s t M K L N v w u b E *
      (Real.sqrt y : ℂ) ^ (2 * (E : ℤ) - (6 + (K : ℤ) + L)))
      ((I * (Real.sqrt y : ℂ)) ^ (-(6 + (K : ℤ) + L)) *
        I ^ (3 + 2 * (L : ℤ) + N - M - K) * bSewnNumerator K L N P Q R S p q r d y) := by
  let B := bSewnNumerator K L N P Q R S p q r d
  let x : ℂ := Real.sqrt y
  let A : ℤ := 6 + (K : ℤ) + L
  let phase : ℤ := (N : ℤ) - M + L - 2 * (K : ℤ) - 3
  have hx : x ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hy).ne'
  have hsq : x ^ 2 = (y : ℂ) := by
    change ((Real.sqrt y : ℝ) : ℂ) ^ (2 : ℕ) = (y : ℂ)
    rw [← Complex.ofReal_pow, Real.sq_sqrt hy.le]
  have hdiff : DifferentiableOn ℂ B (ball (0 : ℂ) 1) :=
    (bSewnNumerator_differentiableOn K L N P Q R S p q r d).mono ball_subset_slitDomain
  have hball : (y : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
    exact hy₁
  have htaylor : HasSum (fun E : ℕ => coefficient E B * (y : ℂ) ^ E) (B y) := by
    refine (Complex.hasSum_taylorSeries_on_ball hdiff hball).congr_fun ?_
    intro E
    simp only [coefficient, sub_zero, smul_eq_mul, div_eq_mul_inv]
    ring
  have hphase :
      (I * x) ^ (-A) * I ^ (3 + 2 * (L : ℤ) + N - M - K) = x ^ (-A) * I ^ phase := by
    rw [mul_zpow]
    calc
      _ = x ^ (-A) * (I ^ (-A) * I ^ (3 + 2 * (L : ℤ) + N - M - K)) := by ring
      _ = _ := by
        rw [← zpow_add₀ Complex.I_ne_zero]
        rw [show -A + (3 + 2 * (L : ℤ) + N - M - K) = phase by
          dsimp only [A, phase]
          ring]
  change HasSum (fun E : ℕ => fixedBProductCoeff s t M K L N v w u b E * x ^ (2 * (E : ℤ) - A))
    ((I * x) ^ (-A) * I ^ (3 + 2 * (L : ℤ) + N - M - K) * B y)
  rw [hphase]
  refine (htaylor.mul_left (x ^ (-A) * I ^ phase)).congr_fun fun E => ?_
  have hpow : x ^ (2 * (E : ℤ) - A) = x ^ (-A) * (y : ℂ) ^ E := by
    rw [show 2 * (E : ℤ) - A = -A + 2 * (E : ℤ) by ring,
      zpow_add₀ hx, zpow_mul, zpow_natCast _ E]
    change x ^ (-A) * (x ^ (2 : ℕ)) ^ E = _
    rw [hsq]
  rw [fixedBProductCoeff_eq_slit_taylor s t M K L N v w u b P Q R S p q r d
    hv hw hu hb hvQ hwR huP hbS hKL hNM E, hpow]
  change I ^ phase * coefficient E B * (x ^ (-A) * (y : ℂ) ^ E) = _
  ring

private theorem occupationGrade_eq {X : Type*} (slot : X → Puncture)
    (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X) (i : Puncture) :
    (doubledOccupation slot n l i).toNat = punctureExcitation slot colour n l i := by
  rw [← punctureExcitation_cast slot colour n l i, Int.toNat_natCast]

/-- For the marked words the sum is the ground-weighted normalized Gaussian
B sector in the native chart, with no sector matching hypothesis. -/
theorem fourHProduct_hasSum_normalizedOccupation {X : Type*}
    (slot : X → Puncture) (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X)
    (u v w b : TwistedEven) (p q r d : ActualGround ℒ leechUnit)
    (hu : u.val = wordAt ℒ slot colour n l .P ⊗ₜ[ℂ] p)
    (hv : v.val = wordAt ℒ slot colour n l .Q ⊗ₜ[ℂ] q)
    (hw : w.val = wordAt ℒ slot colour n l .R ⊗ₜ[ℂ] r)
    (hb : b.val = wordAt ℒ slot colour n l .S ⊗ₜ[ℂ] d)
    (hpar : ∀ i : Puncture, Even (doubledOccupation slot n l i))
    {y : ℝ} (hy : 0 < y) (hy₁ : y < 1) :
    let H := fun i => (doubledOccupation slot n l i).toNat
    HasSum (fun E : ℕ => fixedBProductCoeff false false (H .P) (H .Q) (H .R) (H .S) v w u b E *
      (Real.sqrt y : ℂ) ^ (2 * (E : ℤ) - (6 + (H .Q : ℤ) + H .R)))
      (∑ a : ModTwoCharge ℒ, mixedGroundWeight q r p d a *
        normalizedOccupation ℒ slot colour n l .B y a) := by
  simp only [occupationGrade_eq slot colour n l]
  rw [b_weighted_normalizedOccupation_eq slot colour n l p q r d y]
  have hE (i : Puncture) : Even (punctureExcitation slot colour n l i : ℤ) := by
    rw [punctureExcitation_cast]
    exact hpar i
  exact fixedBProduct_hasSum false false _ _ _ _ v w u b _ _ _ _ p q r d
    (hv.symm ▸ wordAt_grade slot colour n l .Q q) (hw.symm ▸ wordAt_grade slot colour n l .R r)
    (hu.symm ▸ wordAt_grade slot colour n l .P p) (hb.symm ▸ wordAt_grade slot colour n l .S d)
    hv hw hu hb ((hE .Q).add (hE .R)) ((hE .S).sub (hE .P)) hy hy₁

open OriginalFourMCompactLowering (punctureLowering)
open HalfFock.OriginalHalfCurrentWickPolynomial (word eval_word_eq_lowering)
open NativeDoubledOccupationReadout (lowering_eq_zero_of_cutoff)

open private punctureLowering_eq from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCompactLowering
open private punctureLowering_eq_word from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeLaurent

private theorem a_loweredOscillator_eq_inverseFlow {X : Type*} (slot : X → Puncture)
    (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X) (i : Puncture)
    (hi : loweringParameter .A i = 1) :
    loweredOscillator ℒ slot colour .A n l i =
      inverseFlow ℒ (punctureExcitation slot colour n l i / 2 + 1)
        (wordAt ℒ slot colour n l i) := by
  let modes := punctureModes slot colour n l i
  let H := punctureExcitation slot colour n l i
  let V := wordAt ℒ slot colour n l i
  let g : ActualGround ℒ leechUnit := fun _ => 1
  have hg : g ≠ 0 := by
    intro h
    have hc := congrFun h (0 : Half (groundRank ℒ leechUnit))
    change (1 : ℂ) = 0 at hc
    exact one_ne_zero hc
  let J := max ((word ℒ modes).natDegree + 1) (H / 2 + 1)
  have hJ : (word ℒ modes).natDegree < J :=
    (Nat.lt_succ_self _).trans_le (le_max_left _ _)
  change punctureLowering ℒ .A i modes = inverseFlow ℒ (H / 2 + 1) V
  rw [punctureLowering_eq ℒ leechUnit, hi, eval_word_eq_lowering ℒ leechUnit modes _ J hJ]
  unfold inverseFlow
  symm
  apply Finset.sum_subset (Finset.range_mono (le_max_right _ _))
  intro j _ hj
  have hzero := lowering_eq_zero_of_cutoff ℒ leechUnit H j V g hg
    (wordAt_grade slot colour n l i g)
    (Nat.le_of_not_gt fun h => hj (Finset.mem_range.mpr h))
  change ((-1 : ℂ) ^ j / (j.factorial : ℂ)) • (oscillatorLower ℒ ^ j) V = 0
  rw [hzero, smul_zero]

private theorem a_weighted_normalizedOccupation_eq {X : Type*} (slot : X → Puncture)
    (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X)
    (p q r d : ActualGround ℒ leechUnit) (y : ℝ) :
    let H := punctureExcitation slot colour n l
    let V := wordAt ℒ slot colour n l
    let ξ := laurentRoot .A y
    (∑ a : ModTwoCharge ℒ, mixedGroundWeight p q r d a *
      normalizedOccupation ℒ slot colour n l .A y a) =
      ξ ^ (-((H .P : ℤ) + (H .Q : ℤ) + 6)) *
        fixedASlitSewn (H .P) (H .Q) (V .P) (V .Q) (V .R) (V .S) p q r d
          (parameter .A (y : ℂ)) := by
  classical
  let H := punctureExcitation slot colour n l
  let V := wordAt ℒ slot colour n l
  let f (a : ModTwoCharge ℒ) := occupationReadout ℒ
    (inverseFlow ℒ (H .P / 2 + 1) (V .P)) (inverseFlow ℒ (H .Q / 2 + 1) (V .Q))
    (V .R) (V .S) (fun β γ δ η => slitChargeSector ℒ a β γ δ η (parameter .A (y : ℂ)))
  have hgauss (a : ModTwoCharge ℒ) : gaussianOccupation ℒ slot colour n l .A y a = f a := by
    change occupationReadout ℒ (loweredOscillator ℒ slot colour .A n l .P)
      (loweredOscillator ℒ slot colour .A n l .Q) (loweredOscillator ℒ slot colour .A n l .R)
      (loweredOscillator ℒ slot colour .A n l .S) (nativeSector ℒ .A y a) = _
    rw [a_loweredOscillator_eq_inverseFlow slot colour n l .P rfl,
      a_loweredOscillator_eq_inverseFlow slot colour n l .Q rfl,
      show loweredOscillator ℒ slot colour .A n l .R = V .R from
        punctureLowering_eq_word ℒ .A .R rfl (punctureModes slot colour n l .R),
      show loweredOscillator ℒ slot colour .A n l .S = V .S from
        punctureLowering_eq_word ℒ .A .S rfl (punctureModes slot colour n l .S)]
    rfl
  have hnorm (a : ModTwoCharge ℒ) :
      normalizedOccupation ℒ slot colour n l .A y a =
        I ^ ((H .Q : ℤ) - 2 * (H .P : ℤ) - 3) *
          laurentRoot .A y ^ (-((H .P : ℤ) + (H .Q : ℤ) + 6)) * f a := by
    unfold normalizedOccupation
    simp only [bpzPhase, laurentPower, hgauss, ← punctureExcitation_cast slot colour n l]
    rw [show -(6 + (H .P : ℤ) + (H .Q : ℤ)) = -((H .P : ℤ) + (H .Q : ℤ) + 6) by ring]
  change _ = laurentRoot .A y ^ (-((H .P : ℤ) + (H .Q : ℤ) + 6)) *
    (I ^ ((H .Q : ℤ) - 2 * (H .P : ℤ) - 3) * ∑ a, mixedGroundWeight p q r d a * f a)
  simp only [hnorm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- Ground exchange turns the normalized four-H Fourier law into the scalar
identity, with the positive B factor `y^sigma`. -/
theorem fourH_ground_weighted_A_eq_B {X : Type*} [Fintype X] [DecidableEq X]
    (slot : X → Puncture) (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X)
    (hl : l.Nodup) (hpar : ∀ i : Puncture, Even (doubledOccupation slot n l i))
    (p q r d : ActualGround ℒ leechUnit) {y : ℝ} (hy : (1 / 2 : ℝ) < y) (hy₁ : y < 1) :
    let H := doubledOccupation slot n l
    let s := sigma (H .P) (H .Q) (H .R) (H .S)
    let F := fun (c : Chart) a => normalizedOccupation ℒ slot colour n l c y a
    (∑ a : ModTwoCharge ℒ, mixedGroundWeight p q r d a * F .A a) =
      (y : ℂ) ^ s * ∑ a : ModTwoCharge ℒ, mixedGroundWeight q r p d a * F .B a := by
  classical
  let H := doubledOccupation slot n l
  let s := sigma (H .P) (H .Q) (H .R) (H .S)
  let F := fun (c : Chart) a => normalizedOccupation ℒ slot colour n l c y a
  let W := mixedGroundWeight q r p d
  let k : ℂ := (2 : ℂ) ^ (12 : ℕ)
  have hk : k ≠ 0 := pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)
  have hmod (i : Puncture) : H i % 2 = 0 := by
    obtain ⟨j, hj⟩ := hpar i
    change H i = j + j at hj
    omega
  have hFour (a : ModTwoCharge ℒ) :
      k * (y : ℂ) ^ s * F .B a = ∑ b, fourierSign ℒ a b * quadraticSign ℒ b * F .A b :=
    (normalized_occupation_fourier_overlap ℒ leechUnit leech_spec.2.2.1 leech_spec.1
      slot colour n l hl
      (show FourHParity slot n l from ⟨hmod .P, hmod .Q, hmod .R, hmod .S⟩) hy hy₁ a).1
  have hW (a : ModTwoCharge ℒ) :
      mixedGroundWeight p q r d a =
        ∑ b, k⁻¹ * quadraticSign ℒ a * fourierSign ℒ a b * W b := by
    have h := ground_exchange_first ℒ leechUnit a p q r d
    rw [original_ground_dimension ℒ leechUnit leech_spec.1] at h
    simpa only [mixedGroundWeight, W, k, mul_assoc] using h
  have hsymm (a b : ModTwoCharge ℒ) : fourierSign ℒ a b = fourierSign ℒ b a := by
    unfold fourierSign
    rw [← mod_two_cocycle_symmetrization ℒ a b, ← mod_two_cocycle_symmetrization ℒ b a,
      add_comm (modTwoCocycle ℒ a b) (modTwoCocycle ℒ b a)]
  change (∑ a, mixedGroundWeight p q r d a * F .A a) =
    (y : ℂ) ^ s * ∑ b, W b * F .B b
  calc
    _ = ∑ a, ∑ b, (k⁻¹ * quadraticSign ℒ a * fourierSign ℒ a b * W b) * F .A a := by
      simp only [hW, Finset.sum_mul]
    _ = ∑ b, W b * (k⁻¹ * ∑ a, fourierSign ℒ b a * quadraticSign ℒ a * F .A a) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
      rw [hsymm a b]
      ring
    _ = _ := by
      conv_rhs => rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← hFour b]
      calc
        _ = (k⁻¹ * k) * ((y : ℂ) ^ s * (W b * F .B b)) := by ring
        _ = _ := by rw [inv_mul_cancel₀ hk, one_mul]

/-- On the real overlap the genuine A iterate and the genuine even B
product obey the scalar equation with the B scaling fixed by chart transport. -/
theorem fourH_actual_A_eq_B {X : Type*} [Fintype X] [DecidableEq X]
    (slot : X → Puncture) (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X)
    (hl : l.Nodup) (hpar : ∀ i : Puncture, Even (doubledOccupation slot n l i))
    (u v w b : TwistedEven) (p q r d : ActualGround ℒ leechUnit)
    (hu : u.val = wordAt ℒ slot colour n l .P ⊗ₜ[ℂ] p)
    (hv : v.val = wordAt ℒ slot colour n l .Q ⊗ₜ[ℂ] q)
    (hw : w.val = wordAt ℒ slot colour n l .R ⊗ₜ[ℂ] r)
    (hb : b.val = wordAt ℒ slot colour n l .S ⊗ₜ[ℂ] d)
    {y : ℝ} (hy : (1 / 2 : ℝ) < y) (hy₁ : y < 1) :
    let G := doubledOccupation slot n l
    let H := fun i => (G i).toNat
    let s := sigma (G .P) (G .Q) (G .R) (G .S)
    (∑' j : ℤ, fixedAIterateCoeff false (H .P) (H .Q) (H .R) (H .S) j u v w.val b.val *
      laurentRoot .A y ^ j) =
      (y : ℂ) ^ s * ∑' E : ℕ, fixedBProductCoeff false false (H .P) (H .Q) (H .R)
        (H .S) v w u b E * (Real.sqrt y : ℂ) ^ (2 * (E : ℤ) - (6 + (H .Q : ℤ) + H .R)) := by
  let H := punctureExcitation slot colour n l
  let V := wordAt ℒ slot colour n l
  have hE (i : Puncture) : Even (H i : ℤ) := by
    change Even (punctureExcitation slot colour n l i : ℤ)
    rw [punctureExcitation_cast]
    exact hpar i
  have hA := fixedAIterate_hasSum_on_overlap false (H .P) (H .Q) (H .R) (H .S) u v
    (V .P) (V .Q) (V .R) (V .S) p q r d
    (hu.symm ▸ wordAt_grade slot colour n l .P p) (hv.symm ▸ wordAt_grade slot colour n l .Q q)
    hu hv (wordAt_grade slot colour n l .R r) (wordAt_grade slot colour n l .S d)
    ((hE .P).add (hE .Q)) hy hy₁
  have hB := fourHProduct_hasSum_normalizedOccupation slot colour n l u v w b p q r d
    hu hv hw hb hpar (by linarith) hy₁
  dsimp only at hA hB ⊢
  rw [hB.tsum_eq]
  simp only [occupationGrade_eq slot colour n l]
  rw [hw, hb, hA.tsum_eq, ← a_weighted_normalizedOccupation_eq slot colour n l p q r d y]
  exact fourH_ground_weighted_A_eq_B slot colour n l hl hpar p q r d hy hy₁

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHUpperProduct
