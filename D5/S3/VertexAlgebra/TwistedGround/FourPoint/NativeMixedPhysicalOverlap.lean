/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedPhysicalOverlap
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedPhysicalOverlap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The native Leech HHBB iterate agrees with the scaled B and upper-lip D values. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedPairAIterate
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedUpperDLip
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDFourCurrent
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! The even-intermediate A iterate and the mixed upper right-skew B product. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators Topology TensorProduct
open Filter Metric

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedPhysicalOverlap

open Complex (I)
open LatticeGeneratingFieldLocality LatticeHalfFock LatticePositiveEnergy
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockGradedTrace LatticeTwistedGroundRealization
open LatticeTwistedGroundRealization.SignQuotient
open ActualLeechHyperbolic (leechData leech_spec)
open Orbifold.NativeOddTwistedIntertwiner (Twisted TwistedEven TwistedOdd leechUnit)
open NativeFixedPairAIterate (fixedAIterateCoeff fixedAIterate_hasSum_on_overlap fixedASlitSewn)
open NativeMixedUpperProductCusp (bProductCoeff bProductCoeff_eq_taylor
  bSewnNumerator bSlitOccupation b_weighted_normalizedOccupation_eq)
open NativeMixedWickChartTransport (MixedParity bpzPhase doubledOccupation
  gaussianOccupation laurentPower laurentRoot normalizedOccupation
  normalized_occupation_fourier_overlap sigma)
open OriginalFourMChargeCoset (fourierSign quadraticSign ground_exchange_first ground_exchange_second)
open NativeMixedUpperDLip (dSlitProduct dSlitProduct_tendsto_weighted_normalizedOccupation)
open OriginalFourMPeriodSource (dLip)
open OriginalFourMVariableSupport
  (inverseFlow loweredOscillator nativeSector occupationReadout wordAt)
open OriginalFourMSectorContinuation (slitChargeSector slitChargeSector_differentiableOn)
open OriginalFourMActualChart (Chart Puncture parameter)
open OriginalGaussianSewnAnalytic (coefficient)

open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod (slitDomain ball_subset_slitDomain)

open private original_ground_dimension from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset
open private mixedGroundWeight from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedWickCuspGerm
open private analytic_neg_square_even_part coefficient_const_mul from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMChargeGerm
open private detectorSewn detectorSewn_analyticAt detectorSewn_eq punctureExcitation
  punctureExcitation_cast punctureModes wordAt_grade b_loweredOscillator_eq_inverseFlow from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedUpperProductCusp
open private d_loweredP_eq_inverseFlow from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedUpperDLip
open private punctureLowering_eq_word from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeLaurent

open OriginalFourMCompactLowering (punctureLowering)
open OriginalFourMActualChart (loweringParameter)
open private fourierSign_swap translated_gauss_sum from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDFourCurrent

local notation "ℒ" => leechData

set_option maxHeartbeats 4000000 in
-- Compare coefficients of the analytic detector and its negative-square pullback.
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

private theorem bSewnNumerator_differentiableOn (K L N : ℕ)
    (P Q R S : Oscillator ℒ) (p q r d : ActualGround ℒ leechUnit) :
    DifferentiableOn ℂ (bSewnNumerator K L N P Q R S p q r d) slitDomain := by
  classical
  have hsector (a : ModTwoCharge ℒ) (β γ δ η : Exponent ℒ) :
      DifferentiableOn ℂ (slitChargeSector ℒ a β γ δ η) slitDomain :=
    slitChargeSector_differentiableOn ℒ leech_spec.2.2.1 a β γ δ η
  unfold bSewnNumerator bSlitOccupation occupationReadout
  fun_prop

set_option maxHeartbeats 4000000 in
-- Elaborate the field coefficient and the Taylor series at the physical root.
/-- The genuine B energy diagonal sums on the full positive sewing interval.
The change from the positive root to the upper root gives the displayed
phase and leaves the same slit Gaussian numerator. -/
theorem b_upper_product_hasSum_unitInterval (s t : Bool) (M K L N : ℕ)
    (v : Twisted ℒ leechUnit s) (w : Twisted ℒ leechUnit (!s))
    (u : Twisted ℒ leechUnit t) (b : Twisted ℒ leechUnit (!t))
    (P Q R S : Oscillator ℒ) (p q r d : ActualGround ℒ leechUnit)
    (hv : v.val ∈ actualGrade ℒ leechUnit K) (hw : w.val ∈ actualGrade ℒ leechUnit L)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    (hvQ : v.val = Q ⊗ₜ[ℂ] q) (hwR : w.val = R ⊗ₜ[ℂ] r)
    (huP : u.val = P ⊗ₜ[ℂ] p) (hbS : b.val = S ⊗ₜ[ℂ] d)
    (hKL : Odd ((K : ℤ) + L)) (hNM : Odd ((N : ℤ) - M))
    {y : ℝ} (hy : 0 < y) (hy₁ : y < 1) :
    HasSum (fun E : ℕ => bProductCoeff s t M K L N v w u b E *
      (Real.sqrt y : ℂ) ^ (2 * (E : ℤ) - (6 + (K : ℤ) + L)))
      ((I * (Real.sqrt y : ℂ)) ^ (-(6 + (K : ℤ) + L)) *
        I ^ (3 + 2 * (L : ℤ) + N - M - K) * bSewnNumerator K L N P Q R S p q r d y) := by
  let B := bSewnNumerator K L N P Q R S p q r d
  let x : ℂ := Real.sqrt y
  let A : ℤ := 6 + (K : ℤ) + L
  let phase : ℤ := (N : ℤ) - M + ((L : ℤ) - 2 * (K : ℤ) - 3)
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
  change HasSum (fun E : ℕ => bProductCoeff s t M K L N v w u b E * x ^ (2 * (E : ℤ) - A))
    ((I * x) ^ (-A) * I ^ (3 + 2 * (L : ℤ) + N - M - K) * B y)
  rw [hphase]
  refine (htaylor.mul_left (x ^ (-A) * I ^ phase)).congr_fun fun E => ?_
  have hpow : x ^ (2 * (E : ℤ) - A) = x ^ (-A) * (y : ℂ) ^ E := by
    rw [show 2 * (E : ℤ) - A = -A + 2 * (E : ℤ) by ring,
      zpow_add₀ hx, zpow_mul, zpow_natCast _ E]
    change x ^ (-A) * (x ^ (2 : ℕ)) ^ E = _
    rw [hsq]
  rw [bProductCoeff_eq_taylor s t M K L N v w u b P Q R S p q r d
    hv hw hu hb hvQ hwR huP hbS hKL hNM E, bDetector_coefficient, ← mul_assoc,
    ← zpow_add₀ Complex.I_ne_zero, hpow]
  change I ^ phase * coefficient E B * (x ^ (-A) * (y : ℂ) ^ E) = _
  ring

private theorem occupationGrade_eq {X : Type*} (slot : X → Puncture)
    (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X) (i : Puncture) :
    (doubledOccupation slot n l i).toNat = punctureExcitation slot colour n l i := by
  rw [← punctureExcitation_cast slot colour n l i, Int.toNat_natCast]

set_option maxHeartbeats 4000000 in
-- Elaborate the chart readout with all four oscillator arguments.
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
    have hP : loweredOscillator ℒ slot colour .A n l .P =
        inverseFlow ℒ (H .P / 2 + 1) (V .P) := by
      simpa only [loweredOscillator, punctureLowering, loweringParameter] using
        d_loweredP_eq_inverseFlow slot colour n l
    have hQ : loweredOscillator ℒ slot colour .A n l .Q =
        inverseFlow ℒ (H .Q / 2 + 1) (V .Q) := by
      simpa only [loweredOscillator, punctureLowering, loweringParameter] using
        b_loweredOscillator_eq_inverseFlow slot colour n l .Q rfl
    rw [hP, hQ,
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
    simp only [← punctureExcitation_cast slot colour n l, bpzPhase, laurentPower, hgauss]
    rw [show -(6 + (H .P : ℤ) + (H .Q : ℤ)) = -((H .P : ℤ) + (H .Q : ℤ) + 6) by ring]
  change _ = laurentRoot .A y ^ (-((H .P : ℤ) + (H .Q : ℤ) + 6)) *
    (I ^ ((H .Q : ℤ) - 2 * (H .P : ℤ) - 3) * ∑ a, mixedGroundWeight p q r d a * f a)
  simp only [hnorm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

set_option maxHeartbeats 4000000 in
-- Elaborate the finite sums over the Leech charge quotient.
/-- Contract the mixed Fourier law with the original ordered ground forms. -/
private theorem hhbb_ground_weighted_A_eq_neg_B {X : Type*} [Finite X]
    (slot : X → Puncture) (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X)
    (hl : l.Nodup) (hpar : MixedParity slot n l)
    (p q r d : ActualGround ℒ leechUnit) {y : ℝ} (hy : (1 / 2 : ℝ) < y) (hy₁ : y < 1) :
    let H := doubledOccupation slot n l
    let s := sigma (H .P) (H .Q) (H .R) (H .S)
    let F := fun (c : Chart) a => normalizedOccupation ℒ slot colour n l c y a
    (∑ a : ModTwoCharge ℒ, mixedGroundWeight p q r d a * F .A a) =
      -((y : ℂ) ^ s * ∑ a : ModTwoCharge ℒ, mixedGroundWeight q r p d a * F .B a) := by
  classical
  letI := Fintype.ofFinite X
  let H := doubledOccupation slot n l
  let s := sigma (H .P) (H .Q) (H .R) (H .S)
  let F := fun (c : Chart) a => normalizedOccupation ℒ slot colour n l c y a
  let W := mixedGroundWeight q r p d
  let k : ℂ := (2 : ℂ) ^ (12 : ℕ)
  have hk : k ≠ 0 := pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)
  have hFour (a : ModTwoCharge ℒ) :
      (∑ b, fourierSign ℒ a b * quadraticSign ℒ b * F .A b) = -(k * (y : ℂ) ^ s * F .B a) := by
    have h := (normalized_occupation_fourier_overlap ℒ leechUnit leech_spec.2.2.1 leech_spec.1
      slot colour n l hl hpar hy hy₁ a).1
    simpa only [neg_neg] using (congrArg Neg.neg h).symm
  have hW (a : ModTwoCharge ℒ) :
      mixedGroundWeight p q r d a =
        ∑ b, k⁻¹ * quadraticSign ℒ a * fourierSign ℒ a b * W b := by
    have h := ground_exchange_first ℒ leechUnit a p q r d
    rw [original_ground_dimension ℒ leechUnit leech_spec.1] at h
    simpa only [mixedGroundWeight, W, k, mul_assoc] using h
  change (∑ a, mixedGroundWeight p q r d a * F .A a) =
    -((y : ℂ) ^ s * ∑ b, W b * F .B b)
  calc
    _ = ∑ a, ∑ b, (k⁻¹ * quadraticSign ℒ a * fourierSign ℒ a b * W b) * F .A a := by
      simp only [hW, Finset.sum_mul]
    _ = ∑ b, W b * (k⁻¹ * ∑ a, fourierSign ℒ b a * quadraticSign ℒ a * F .A a) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
      rw [fourierSign_swap ℒ a b]
      ring
    _ = _ := by
      conv_rhs => rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hFour b]
      calc
        _ = (k⁻¹ * k) * (-((y : ℂ) ^ s * (W b * F .B b))) := by ring
        _ = _ := by rw [inv_mul_cancel₀ hk, one_mul]

set_option maxHeartbeats 4000000 in
-- Elaborate both field series at the grades of the marked words.
/-- On the real overlap both series sum, and the scalar of the actual A
iterate is minus the scalar of the actual B product times `y^sigma`.
The H states occupy P and Q and the B states occupy R and S. -/
theorem hhbb_actual_overlap {X : Type*} [Finite X]
    (slot : X → Puncture) (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X)
    (hl : l.Nodup) (hpar : MixedParity slot n l)
    (u v : TwistedEven) (w b : TwistedOdd) (p q r d : ActualGround ℒ leechUnit)
    (hu : u.val = wordAt ℒ slot colour n l .P ⊗ₜ[ℂ] p)
    (hv : v.val = wordAt ℒ slot colour n l .Q ⊗ₜ[ℂ] q)
    (hw : w.val = wordAt ℒ slot colour n l .R ⊗ₜ[ℂ] r)
    (hb : b.val = wordAt ℒ slot colour n l .S ⊗ₜ[ℂ] d)
    {y : ℝ} (hy : (1 / 2 : ℝ) < y) (hy₁ : y < 1) :
    let G := doubledOccupation slot n l
    let H := fun i => (G i).toNat
    let s := sigma (G .P) (G .Q) (G .R) (G .S)
    let A := fun j : ℤ => fixedAIterateCoeff false (H .P) (H .Q) (H .R) (H .S) j
      u v w.val b.val * laurentRoot .A y ^ j
    let B := fun E : ℕ => bProductCoeff false false (H .P) (H .Q) (H .R) (H .S) v w u b E *
      (Real.sqrt y : ℂ) ^ (2 * (E : ℤ) - (6 + (H .Q : ℤ) + H .R))
    HasSum A (-((y : ℂ) ^ s * ∑' E, B E)) ∧ Summable B := by
  let H := punctureExcitation slot colour n l
  let V := wordAt ℒ slot colour n l
  have ⟨hP, hQ, hR, hS⟩ := hpar
  rw [← punctureExcitation_cast slot colour n l] at hP hQ hR hS
  have hPK : Even ((H .P : ℤ) + (H .Q : ℤ)) := by
    dsimp only [H]
    exact Int.even_iff.mpr (by omega)
  have hQR : Odd ((H .Q : ℤ) + (H .R : ℤ)) := by
    dsimp only [H]
    exact Int.odd_iff.mpr (by omega)
  have hSP : Odd ((H .S : ℤ) - (H .P : ℤ)) := by
    dsimp only [H]
    exact Int.odd_iff.mpr (by omega)
  have hA := fixedAIterate_hasSum_on_overlap false (H .P) (H .Q) (H .R) (H .S) u v
    (V .P) (V .Q) (V .R) (V .S) p q r d
    (hu.symm ▸ wordAt_grade slot colour n l .P p) (hv.symm ▸ wordAt_grade slot colour n l .Q q)
    hu hv (wordAt_grade slot colour n l .R r) (wordAt_grade slot colour n l .S d)
    hPK hy hy₁
  have hB := b_upper_product_hasSum_unitInterval false false (H .P) (H .Q) (H .R) (H .S) v w u b
    (V .P) (V .Q) (V .R) (V .S) p q r d
    (hv.symm ▸ wordAt_grade slot colour n l .Q q) (hw.symm ▸ wordAt_grade slot colour n l .R r)
    (hu.symm ▸ wordAt_grade slot colour n l .P p) (hb.symm ▸ wordAt_grade slot colour n l .S d)
    hv hw hu hb hQR hSP (by linarith) hy₁
  dsimp only at hA hB ⊢
  simp only [occupationGrade_eq slot colour n l]
  refine ⟨?_, hB.summable⟩
  rw [hw, hb, hB.tsum_eq, ← b_weighted_normalizedOccupation_eq slot colour n l p q r d y,
    ← hhbb_ground_weighted_A_eq_neg_B slot colour n l hl hpar p q r d hy hy₁,
    a_weighted_normalizedOccupation_eq slot colour n l p q r d y]
  exact hA

set_option maxHeartbeats 4000000 in
-- Elaborate the Fourier contraction over the Leech charge quotient.
private theorem hhbb_ground_weighted_D_eq_A {X : Type*} [Finite X]
    (slot : X → Puncture) (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X)
    (hl : l.Nodup) (hpar : MixedParity slot n l)
    (p q r d : ActualGround ℒ leechUnit) {y : ℝ} (hy : (1 / 2 : ℝ) < y) (hy₁ : y < 1) :
    (∑ a : ModTwoCharge ℒ, mixedGroundWeight p r q d a *
      normalizedOccupation ℒ slot colour n l .D y a) =
    ∑ a : ModTwoCharge ℒ, mixedGroundWeight p q r d a *
      normalizedOccupation ℒ slot colour n l .A y a := by
  classical
  letI := Fintype.ofFinite X
  let F := fun (c : Chart) a => normalizedOccupation ℒ slot colour n l c y a
  let W := mixedGroundWeight q r p d
  let k : ℂ := (2 : ℂ) ^ (12 : ℕ)
  have hk : k ≠ 0 := pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)
  have hFD (a : ModTwoCharge ℒ) :
      F .D a = k⁻¹ * ∑ c, fourierSign ℒ a c * F .A c := by
    have h : k * F .D a = ∑ c, fourierSign ℒ a c * F .A c :=
      (normalized_occupation_fourier_overlap ℒ leechUnit leech_spec.2.2.1 leech_spec.1
        slot colour n l hl hpar hy hy₁ a).2
    rw [← h, ← mul_assoc, inv_mul_cancel₀ hk, one_mul]
  have hWD (a : ModTwoCharge ℒ) :
      mixedGroundWeight p r q d a = ∑ b, k⁻¹ * quadraticSign ℒ (a + b) * W b := by
    have h := ground_exchange_second ℒ leechUnit a p q r d
    rw [original_ground_dimension ℒ leechUnit leech_spec.1] at h
    simpa only [mixedGroundWeight, W, k, mul_assoc] using h
  have hWA (c : ModTwoCharge ℒ) :
      mixedGroundWeight p q r d c =
        ∑ b, k⁻¹ * quadraticSign ℒ c * fourierSign ℒ c b * W b := by
    have h := ground_exchange_first ℒ leechUnit c p q r d
    rw [original_ground_dimension ℒ leechUnit leech_spec.1] at h
    simpa only [mixedGroundWeight, W, k, mul_assoc] using h
  have hTransform (b : ModTwoCharge ℒ) :
      (∑ a, quadraticSign ℒ (a + b) * F .D a) =
        ∑ c, quadraticSign ℒ c * fourierSign ℒ c b * F .A c := by
    calc
      _ = k⁻¹ * ∑ a, ∑ c, (quadraticSign ℒ (a + b) * fourierSign ℒ a c) * F .A c := by
        simp only [hFD, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
      _ = _ := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [← Finset.sum_mul, translated_gauss_sum ℒ leechUnit leech_spec.1 b c]
        calc
          _ = (k⁻¹ * k) * (quadraticSign ℒ c * fourierSign ℒ c b * F .A c) := by ring
          _ = _ := by rw [inv_mul_cancel₀ hk, one_mul]
  change (∑ a, mixedGroundWeight p r q d a * F .D a) =
    ∑ c, mixedGroundWeight p q r d c * F .A c
  calc
    _ = ∑ a, ∑ b, (k⁻¹ * quadraticSign ℒ (a + b) * W b) * F .D a := by
      simp only [hWD, Finset.sum_mul]
    _ = ∑ b, (k⁻¹ * W b) * (∑ a, quadraticSign ℒ (a + b) * F .D a) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
    _ = _ := by
      simp only [hTransform, hWA, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => by ring

set_option maxHeartbeats 4000000 in
-- Elaborate the field iterate and boundary continuation at the marked grades.
/-- The actual A iterate equals the upper-lip boundary value of the analytic
continuation of the D product in its native order `(P, R, Q, S)`. -/
theorem hhbb_actual_A_eq_upper_D_limit {X : Type*} [Finite X]
    (slot : X → Puncture) (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X)
    (hl : l.Nodup) (hpar : MixedParity slot n l)
    (u v : TwistedEven) (w b : TwistedOdd) (p q r d : ActualGround ℒ leechUnit)
    (hu : u.val = wordAt ℒ slot colour n l .P ⊗ₜ[ℂ] p)
    (hv : v.val = wordAt ℒ slot colour n l .Q ⊗ₜ[ℂ] q)
    (hw : w.val = wordAt ℒ slot colour n l .R ⊗ₜ[ℂ] r)
    (hb : b.val = wordAt ℒ slot colour n l .S ⊗ₜ[ℂ] d)
    {y : ℝ} (hy : (1 / 2 : ℝ) < y) (hy₁ : y < 1) :
    let H := fun i => (doubledOccupation slot n l i).toNat
    let V := wordAt ℒ slot colour n l
    Tendsto (dSlitProduct (H .P) (H .Q) (H .R) (H .S) (V .P) (V .Q) (V .R) (V .S) p q r d)
      (𝓝[dLip true] (parameter .D (y : ℂ)))
      (𝓝 (∑' j : ℤ, fixedAIterateCoeff false (H .P) (H .Q) (H .R) (H .S) j
        u v w.val b.val * laurentRoot .A y ^ j)) := by
  let H := punctureExcitation slot colour n l
  let V := wordAt ℒ slot colour n l
  have hP := hpar.1
  have hQ := hpar.2.1
  rw [← punctureExcitation_cast slot colour n l] at hP hQ
  have hPK : Even ((H .P : ℤ) + (H .Q : ℤ)) := by
    dsimp only [H]
    exact Int.even_iff.mpr (by omega)
  have hA := fixedAIterate_hasSum_on_overlap false (H .P) (H .Q) (H .R) (H .S) u v
    (V .P) (V .Q) (V .R) (V .S) p q r d
    (hu.symm ▸ wordAt_grade slot colour n l .P p) (hv.symm ▸ wordAt_grade slot colour n l .Q q)
    hu hv (wordAt_grade slot colour n l .R r) (wordAt_grade slot colour n l .S d)
    hPK hy hy₁
  have hD := dSlitProduct_tendsto_weighted_normalizedOccupation slot colour n l p q r d
    (by linarith : 0 < y) hy₁
  dsimp only at hA hD ⊢
  simp only [occupationGrade_eq slot colour n l]
  rw [hw, hb, hA.tsum_eq, ← a_weighted_normalizedOccupation_eq slot colour n l p q r d y,
    ← hhbb_ground_weighted_D_eq_A slot colour n l hl hpar p q r d hy hy₁]
  exact hD

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedPhysicalOverlap
