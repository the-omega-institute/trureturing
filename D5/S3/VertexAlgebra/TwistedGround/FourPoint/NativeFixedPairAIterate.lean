/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeFixedPairAIterate
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/NativeFixedPairAIterate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual even-intermediate Leech iterate sums to the weighted A cusp Laurent germ. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedPairFourPoint
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedWickCuspGerm
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedWickChartTransport
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.Complex.TaylorSeries

/-! The A iterate in the doubled Laurent coordinate, with both ordered ground pairings. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators Topology TensorProduct VertexOperator
open Filter Metric

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedPairAIterate

open LatticeGeneratingFieldLocality LatticeHalfFock LatticePositiveEnergy
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockGradedTrace LatticeTwistedGroundRealization
open LatticeTwistedGroundRealization.SignQuotient
open ActualLeechHyperbolic (leechData leech_spec)
open ActualChargedAdjoint (actualForm)
open ActualEnergyRestrictedDual (maxOddWeight)
open CorrectedInversion (K_R)
open Orbifold.NativeOddTwistedIntertwiner (Twisted TwistedEven leechUnit)
open Orbifold.NativeFixedPairField (nu nu_coeff_odd_zero nu_lower_truncation)
open NativeFixedPairFourPoint (nu_fourPoint_charge fixedChargeCoefficient_one_eq)
open NativeDoubledBPZWick (leftExponent groundFactor)
open NativeDoubledOccupationReadout (coset_lowering_eq_inverse_readout)
open OriginalFourMEnergyCoefficient (polynomialCoefficient)
open OriginalFourMChargeCoset (oscillatorLower)
open OriginalFourMVariableSupport (occupationReadout inverseFlow)
open OriginalFourMChargeGerm (chargeSectorSewn)
open OriginalFourMSectorContinuation (slitChargeSector slitChargeSector_differentiableOn
  slitChargeTerm_eq_native)
open OriginalGaussianSewnAnalytic (coefficient)
open NativeMixedWickCuspGerm (mixedSewn mixedOccupationSewn mixedSewn_analyticAt)
open OriginalFourMActualChart (parameter periodRoot)
open NativeMixedWickChartTransport (laurentRoot laurentRoot_values laurentRoot_sq upper_sewing_root)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod (slitDomain ball_subset_slitDomain)

open private groundForm from D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset
open private occupationReadout_coset_eq_taylor from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeDoubledOccupationReadout
open private mixedGroundWeight coefficient_mixedSewn maxOddWeight_le_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedWickCuspGerm
open private analytic_neg_square_even_part from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMChargeGerm

local notation "ℒ" => leechData

/-- The doubled front exponent of the homogeneous iterate at source energy `E`. -/
def fixedAExponent (M K E : ℕ) : ℤ :=
  2 * (E : ℤ) - ((M : ℤ) + (K : ℤ) + 6)

/-- The actual fixed-source iterate coefficient on the grading diagonal.
Its right mode at `n = fixedAExponent M K E` is `N - L - 2*E`. -/
def fixedAIterateCoeff (s : Bool) (M K L N : ℕ) (n : ℤ)
    (u v : Twisted ℒ leechUnit s) (w b : ActualTensor ℒ leechUnit) : ℂ :=
  actualForm ℒ leechUnit b
    ((correctedField ℒ leechUnit ((nu s u).coeff n v).val).coeff
      ((N : ℤ) - (L : ℤ) - (n + ((M : ℤ) + (K : ℤ) + 6))) w)

set_option maxHeartbeats 4000000 in
-- Elaborate the charge and occupation sums with their dependent supports.
/-- Each literal energy-diagonal coefficient is the signed Taylor coefficient
of the weighted occupation sum. The sign-one charge identity supplies the
actual fixed-space projection before the signed selectors are removed. -/
theorem fixedAIterateCoeff_eq_sewn_coefficient (s : Bool) (M K L N E : ℕ)
    (u v : Twisted ℒ leechUnit s)
    (P Q R S : Oscillator ℒ) (x y z d : ActualGround ℒ leechUnit)
    (hu : u.val ∈ actualGrade ℒ leechUnit M)
    (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (huP : u.val = P ⊗ₜ[ℂ] x) (hvQ : v.val = Q ⊗ₜ[ℂ] y)
    (hR : R ⊗ₜ[ℂ] z ∈ actualGrade ℒ leechUnit L)
    (hS : S ⊗ₜ[ℂ] d ∈ actualGrade ℒ leechUnit N)
    (hpar : Even ((M : ℤ) + (K : ℤ))) :
    fixedAIterateCoeff s M K L N (fixedAExponent M K E) u v (R ⊗ₜ[ℂ] z) (S ⊗ₜ[ℂ] d) =
      (-1 : ℂ) ^ E * coefficient (2 * E) (mixedSewn M K P Q R S x y z d) := by
  classical
  let m : ℤ := ((M : ℤ) + (K : ℤ) + 4) / 2 - (E : ℤ)
  let eR : ℤ := (N : ℤ) - (L : ℤ) - 2 * (E : ℤ)
  have hE : 2 * (E : ℤ) = (M : ℤ) + (K : ℤ) + 4 - 2 * m := by
    obtain ⟨j, hj⟩ := hpar
    dsimp only [m]
    omega
  have hleft : fixedAExponent M K E = -2 * m - 2 := by
    unfold fixedAExponent
    omega
  have hright : (N : ℤ) - (L : ℤ) -
      (fixedAExponent M K E + ((M : ℤ) + (K : ℤ) + 6)) = eR := by
    dsimp only [fixedAExponent, eR]
    ring
  unfold fixedAIterateCoeff
  rw [hright, hleft, nu_fourPoint_charge s M K E m eR u v _ _ hu hv hE]
  let Charges := {q : Charge ℒ // chargeEnergy ℒ q ≤ E}
  let : Finite Charges := (chargeSublevel_finite ℒ leech_spec.2.2.1 E).to_subtype
  let := Fintype.ofFinite Charges
  let c := (-1 : ℂ) ^ E * Complex.I ^ ((K : ℤ) - 2 * (M : ℤ) - 3)
  let coset (q : Charges) := reduceCharge ℒ q.val
  let f (q : Charges) :=
    ∑ j ∈ Finset.range (M / 2 + 1), ∑ ell ∈ Finset.range (K / 2 + 1),
      ((-1 : ℂ) ^ ((j : ℤ) + (ell : ℤ)) / ((j.factorial : ℂ) * (ell.factorial : ℂ))) *
        polynomialCoefficient ℒ q.val E (leftExponent M K E j ell) eR
          ((oscillatorLower ℒ ^ j) P) ((oscillatorLower ℒ ^ ell) Q) R S
  calc
    _ = ∑ q : Charges, c * (mixedGroundWeight x y z d (coset q) * f q) := by
      rw [finsum_eq_sum_of_fintype]
      apply Finset.sum_congr rfl
      intro q _
      rw [huP, hvQ,
        fixedChargeCoefficient_one_eq q.val M K E m eR q.property hE P Q R S x y z d]
      simp only [c, coset, f, mixedGroundWeight, groundFactor, zpow_natCast, mul_assoc]
    _ = c * ∑ a : ModTwoCharge ℒ,
        ∑ q ∈ Finset.univ.filter (fun q : Charges => coset q = a),
          mixedGroundWeight x y z d (coset q) * f q := by
      rw [Finset.sum_fiberwise Finset.univ coset
        (fun q => mixedGroundWeight x y z d (coset q) * f q), Finset.mul_sum]
    _ = c * ∑ a : ModTwoCharge ℒ, mixedGroundWeight x y z d a *
        ∑ᶠ q : Charges, if coset q = a then f q else 0 := by
      simp only [finsum_eq_sum_of_fintype]
      apply congrArg (fun t : ℂ => c * t)
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_filter, Finset.mul_sum]
      exact Finset.sum_congr rfl fun q hq => by rw [(Finset.mem_filter.mp hq).2]
    _ = _ := by
      rw [coefficient_mixedSewn]
      by_cases hx : x = 0
      · simp [hx, mixedGroundWeight, groundForm]
      by_cases hy : y = 0
      · simp [hy, mixedGroundWeight, groundForm]
      by_cases hz : z = 0
      · simp [hz, mixedGroundWeight, groundForm]
      by_cases hd : d = 0
      · simp [hd, mixedGroundWeight, groundForm]
      have hcoset (a : ModTwoCharge ℒ) :=
        coset_lowering_eq_inverse_readout ℒ leechUnit leech_spec.2.2.1
          M K L N E a P Q R S x y z d hx hy hz hd (huP ▸ hu) (hvQ ▸ hv) hR hS
      have htaylor (a : ModTwoCharge ℒ) :=
        occupationReadout_coset_eq_taylor ℒ leechUnit leech_spec.2.2.1 E a
          (inverseFlow ℒ (M / 2 + 1) P) (inverseFlow ℒ (K / 2 + 1) Q) R S
      simp only [c, mul_assoc]
      apply congrArg fun t : ℂ => (-1 : ℂ) ^ E * (Complex.I ^ ((K : ℤ) - 2 * (M : ℤ) - 3) * t)
      apply Finset.sum_congr rfl
      intro a _
      exact congrArg (mixedGroundWeight x y z d a * ·) ((hcoset a).trans (htaylor a))

/-- Outside the energy range the literal iterate coefficients vanish by
the actual pair field's monodromy and lower truncation. -/
theorem fixedAIterateCoeff_eq_zero_off_energy (s : Bool) (M K L N : ℕ) (n : ℤ)
    (u v : Twisted ℒ leechUnit s) (w b : ActualTensor ℒ leechUnit)
    (hu : u.val ∈ actualGrade ℒ leechUnit M)
    (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (hpar : Even ((M : ℤ) + (K : ℤ))) (hn : n ∉ Set.range (fixedAExponent M K)) :
    fixedAIterateCoeff s M K L N n u v w b = 0 := by
  have hz : (nu s u).coeff n v = 0 := by
    by_cases he : Even n
    · have hlt : n < -((M : ℤ) + (K : ℤ) + 6) := by
        by_contra! hge
        apply hn
        refine ⟨((n + ((M : ℤ) + (K : ℤ) + 6)) / 2).toNat, ?_⟩
        obtain ⟨i, hi⟩ := he
        obtain ⟨j, hj⟩ := hpar
        unfold fixedAExponent
        omega
      have hu' : (maxOddWeight ℒ leechUnit u.val : ℤ) ≤ (M : ℤ) := by
        exact_mod_cast maxOddWeight_le_grade hu
      have hv' : (maxOddWeight ℒ leechUnit v.val : ℤ) ≤ (K : ℤ) := by
        exact_mod_cast maxOddWeight_le_grade hv
      exact nu_lower_truncation s u v n (by omega)
    · exact nu_coeff_odd_zero s n u v (Int.not_even_iff_odd.mp he)
  change K_R ℒ leechUnit _ b w ((nu s u).coeff n v).val = 0
  rw [hz]
  exact map_zero _

/-- The analytic occupation sum in the slit parameter, with the same
inverse flows, ground forms and BPZ phase as the sewn sum. -/
def fixedASlitSewn (M K : ℕ) (P Q R S : Oscillator ℒ)
    (x y z d : ActualGround ℒ leechUnit) (r : ℂ) : ℂ :=
  Complex.I ^ ((K : ℤ) - 2 * (M : ℤ) - 3) *
    ∑ a : ModTwoCharge ℒ, mixedGroundWeight x y z d a *
      occupationReadout ℒ (inverseFlow ℒ (M / 2 + 1) P) (inverseFlow ℒ (K / 2 + 1) Q) R S
        (fun β γ δ η => slitChargeSector ℒ a β γ δ η r)

private theorem fixedASlitSewn_differentiableOn (M K : ℕ) (P Q R S : Oscillator ℒ)
    (x y z d : ActualGround ℒ leechUnit) :
    DifferentiableOn ℂ (fixedASlitSewn M K P Q R S x y z d) slitDomain := by
  classical
  have hsector (a : ModTwoCharge ℒ) (β γ δ η : Exponent ℒ) :
      DifferentiableOn ℂ (slitChargeSector ℒ a β γ δ η) slitDomain :=
    slitChargeSector_differentiableOn ℒ leech_spec.2.2.1 a β γ δ η
  unfold fixedASlitSewn occupationReadout
  fun_prop

/-- The slit numerator agrees on the full sewing disk with the original
weighted native sum at the sewing root. -/
theorem fixedASlitSewn_square (M K : ℕ) (P Q R S : Oscillator ℒ)
    (x y z d : ActualGround ℒ leechUnit) {ρ : ℂ} (hρ : ‖ρ‖ < 1) :
    fixedASlitSewn M K P Q R S x y z d (ρ ^ 2) = mixedSewn M K P Q R S x y z d ρ := by
  have hsector (a : ModTwoCharge ℒ) (β γ δ η : Exponent ℒ) :
      slitChargeSector ℒ a β γ δ η (ρ ^ 2) = chargeSectorSewn ℒ a β γ δ η ρ := by
    unfold slitChargeSector chargeSectorSewn
    apply tsum_congr
    intro q
    rw [slitChargeTerm_eq_native ℒ leech_spec.1 β γ δ η q
      (chargeEnergy_nonneg ℒ leech_spec.2.2.1 q) hρ]
  simp only [fixedASlitSewn, mixedSewn, mixedOccupationSewn, hsector]

private theorem fixedASlitSewn_neg_differentiableOn (M K : ℕ) (P Q R S : Oscillator ℒ)
    (x y z d : ActualGround ℒ leechUnit) :
    DifferentiableOn ℂ (fun r => fixedASlitSewn M K P Q R S x y z d (-r))
      (ball (0 : ℂ) 1) := by
  have hneg : DifferentiableOn ℂ (fun r : ℂ => -r) (ball 0 1) := by fun_prop
  refine (fixedASlitSewn_differentiableOn M K P Q R S x y z d).comp hneg ?_
  intro r hr
  apply ball_subset_slitDomain
  simpa only [mem_ball_zero_iff, norm_neg] using hr

/-- The explicit A numerator in the negative-square variable has the actual
iterate's energy coefficients as its scalar power series at the cusp. -/
theorem fixedAIterate_negative_square_germ (s : Bool) (M K L N : ℕ)
    (u v : Twisted ℒ leechUnit s)
    (P Q R S : Oscillator ℒ) (x y z d : ActualGround ℒ leechUnit)
    (hu : u.val ∈ actualGrade ℒ leechUnit M)
    (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (huP : u.val = P ⊗ₜ[ℂ] x) (hvQ : v.val = Q ⊗ₜ[ℂ] y)
    (hR : R ⊗ₜ[ℂ] z ∈ actualGrade ℒ leechUnit L)
    (hS : S ⊗ₜ[ℂ] d ∈ actualGrade ℒ leechUnit N)
    (hpar : Even ((M : ℤ) + (K : ℤ))) :
    HasFPowerSeriesAt (fun r => fixedASlitSewn M K P Q R S x y z d (-r))
      (FormalMultilinearSeries.ofScalars ℂ (fun E =>
        fixedAIterateCoeff s M K L N (fixedAExponent M K E) u v
          (R ⊗ₜ[ℂ] z) (S ⊗ₜ[ℂ] d))) 0 := by
  obtain ⟨G, hG, hpull⟩ :=
    analytic_neg_square_even_part (mixedSewn_analyticAt M K P Q R S x y z d)
  have hSquare :
      ∀ᶠ ρ : ℂ in 𝓝 0, G (-(ρ ^ 2)) = fixedASlitSewn M K P Q R S x y z d (ρ ^ 2) := by
    filter_upwards [hpull, ball_mem_nhds (0 : ℂ) zero_lt_one] with ρ hρ hball
    have hn := mem_ball_zero_iff.mp hball
    rw [hρ, ← fixedASlitSewn_square M K P Q R S x y z d hn,
      ← fixedASlitSewn_square M K P Q R S x y z d (ρ := -ρ) (by simpa only [norm_neg] using hn),
      neg_sq]
    ring
  have hsqrt : Tendsto (fun r : ℂ => Complex.sqrt (-r)) (𝓝 (0 : ℂ)) (𝓝 0) := by
    have hc : ContinuousAt Complex.sqrt (0 : ℂ) :=
      Complex.continuousAt_sqrt (Or.inl le_rfl)
    have hn : Tendsto (fun r : ℂ => -r) (𝓝 0) (𝓝 0) := by
      simpa only [neg_zero] using continuous_neg.continuousAt (x := (0 : ℂ)).tendsto
    exact (by simpa using hc.tendsto : Tendsto Complex.sqrt (𝓝 (0 : ℂ)) (𝓝 0)).comp hn
  have hlocal : G =ᶠ[𝓝 0] fun r => fixedASlitSewn M K P Q R S x y z d (-r) := by
    filter_upwards [hsqrt.eventually hSquare] with r hr
    have hr_sq : (Complex.sqrt (-r)) ^ 2 = -r :=
      Complex.cpow_nat_inv_pow (-r) (by norm_num : (2 : ℕ) ≠ 0)
    simpa only [hr_sq, neg_neg] using hr
  have hc : (fun E : ℕ => (-1 : ℂ) ^ E *
      coefficient (2 * E) (mixedSewn M K P Q R S x y z d)) =
      fun E => fixedAIterateCoeff s M K L N (fixedAExponent M K E) u v
        (R ⊗ₜ[ℂ] z) (S ⊗ₜ[ℂ] d) := by
    funext E
    exact (fixedAIterateCoeff_eq_sewn_coefficient s M K L N E u v P Q R S x y z d
      hu hv huP hvQ hR hS hpar).symm
  rw [← hc]
  exact hG.congr hlocal

/-- The whole signed Laurent series sums on the punctured unit disk in the
doubled Laurent coordinate. The slit parameter is minus its square. -/
theorem fixedAIterate_hasSum (s : Bool) (M K L N : ℕ)
    (u v : Twisted ℒ leechUnit s)
    (P Q R S : Oscillator ℒ) (x y z d : ActualGround ℒ leechUnit)
    (hu : u.val ∈ actualGrade ℒ leechUnit M)
    (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (huP : u.val = P ⊗ₜ[ℂ] x) (hvQ : v.val = Q ⊗ₜ[ℂ] y)
    (hR : R ⊗ₜ[ℂ] z ∈ actualGrade ℒ leechUnit L)
    (hS : S ⊗ₜ[ℂ] d ∈ actualGrade ℒ leechUnit N)
    (hpar : Even ((M : ℤ) + (K : ℤ))) {ξ : ℂ} (h0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) :
    HasSum (fun n : ℤ => fixedAIterateCoeff s M K L N n u v
      (R ⊗ₜ[ℂ] z) (S ⊗ₜ[ℂ] d) * ξ ^ n)
      (ξ ^ (-((M : ℤ) + (K : ℤ) + 6)) * fixedASlitSewn M K P Q R S x y z d (-(ξ ^ 2))) := by
  let G : ℂ → ℂ := fun r => fixedASlitSewn M K P Q R S x y z d (-r)
  let A (n : ℤ) := fixedAIterateCoeff s M K L N n u v (R ⊗ₜ[ℂ] z) (S ⊗ₜ[ℂ] d)
  have hdiff : DifferentiableOn ℂ G (ball (0 : ℂ) 1) :=
    fixedASlitSewn_neg_differentiableOn M K P Q R S x y z d
  have hG : HasFPowerSeriesAt G
      (FormalMultilinearSeries.ofScalars ℂ (fun E => A (fixedAExponent M K E))) 0 :=
    fixedAIterate_negative_square_germ s M K L N u v P Q R S x y z d hu hv huP hvQ hR hS hpar
  have hana : AnalyticAt ℂ G 0 := hG.analyticAt
  have hcoef (E : ℕ) : coefficient E G = A (fixedAExponent M K E) := by
    have heq := hana.hasFPowerSeriesAt.eq_formalMultilinearSeries hG
    simpa only [FormalMultilinearSeries.coeff_ofScalars, coefficient] using
      congrArg (fun p => FormalMultilinearSeries.coeff p E) heq
  have hball : ξ ^ 2 ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_pow]
    exact pow_lt_one₀ (norm_nonneg ξ) hξ (by decide)
  have htaylor : HasSum (fun E : ℕ => coefficient E G * (ξ ^ 2) ^ E) (G (ξ ^ 2)) := by
    refine (Complex.hasSum_taylorSeries_on_ball hdiff hball).congr_fun ?_
    intro E
    simp only [coefficient, sub_zero, smul_eq_mul, div_eq_mul_inv]
    ring
  have hinj : Function.Injective (fixedAExponent M K) := by
    intro i j hij
    unfold fixedAExponent at hij
    omega
  have hout (n : ℤ) (hn : n ∉ Set.range (fixedAExponent M K)) : A n * ξ ^ n = 0 := by
    rw [show A n = 0 from
      fixedAIterateCoeff_eq_zero_off_energy s M K L N n u v _ _ hu hv hpar hn, zero_mul]
  change HasSum (fun n : ℤ => A n * ξ ^ n)
    (ξ ^ (-((M : ℤ) + (K : ℤ) + 6)) * G (ξ ^ 2))
  apply (hinj.hasSum_iff hout).mp
  refine (htaylor.mul_left (ξ ^ (-((M : ℤ) + (K : ℤ) + 6)))).congr_fun ?_
  intro E
  have hpow : ξ ^ fixedAExponent M K E =
      ξ ^ (-((M : ℤ) + (K : ℤ) + 6)) * (ξ ^ 2) ^ E := by
    simp only [show fixedAExponent M K E = -((M : ℤ) + (K : ℤ) + 6) + 2 * (E : ℤ) by
      unfold fixedAExponent
      ring,
      zpow_add₀ h0, zpow_mul, zpow_natCast _ E, zpow_ofNat]
  change A (fixedAExponent M K E) * ξ ^ fixedAExponent M K E = _
  rw [hpow, hcoef]
  ring

/-- On the real A overlap the chart Laurent root is the positive square
root of minus `r_A = 1 - 1/y`. -/
theorem fixedA_laurentRoot {y : ℝ} (hy : (1 / 2 : ℝ) < y) (hy₁ : y < 1) :
    1 - y⁻¹ < 0 ∧
      laurentRoot .A y = (Real.sqrt (-(1 - y⁻¹)) : ℂ) ∧
      (laurentRoot .A y) ^ 2 = -parameter .A (y : ℂ) := by
  have hy₀ : 0 < y := by linarith
  have hr : (1 - y) / y = -(1 - y⁻¹) := by
    field_simp [hy₀.ne']
    ring
  refine ⟨?_, ?_, laurentRoot_sq hy₀ hy₁ .A⟩
  · have hpos := div_pos (sub_pos.mpr hy₁) hy₀
    rw [hr] at hpos
    exact neg_pos.mp hpos
  · rw [(laurentRoot_values hy₁).1, hr]

/-- On the real overlap the slit numerator is the weighted sewn sum at the
upper sewing root of the A parameter. -/
theorem fixedASlitSewn_chartA (M K : ℕ) (P Q R S : Oscillator ℒ)
    (x p z d : ActualGround ℒ leechUnit) {y : ℝ}
    (hy : (1 / 2 : ℝ) < y) (hy₁ : y < 1) :
    fixedASlitSewn M K P Q R S x p z d (parameter .A (y : ℂ)) =
      mixedSewn M K P Q R S x p z d (periodRoot .D y) := by
  obtain ⟨_, hsquare, hnorm, _⟩ := upper_sewing_root hy hy₁
  rw [← hsquare]
  exact fixedASlitSewn_square M K P Q R S x p z d hnorm

/-- On the full negative real A overlap the actual pair iterate is the
weighted native A charge sum times its signed Laurent monomial. -/
theorem fixedAIterate_hasSum_on_overlap (s : Bool) (M K L N : ℕ)
    (u v : Twisted ℒ leechUnit s)
    (P Q R S : Oscillator ℒ) (x p z d : ActualGround ℒ leechUnit)
    (hu : u.val ∈ actualGrade ℒ leechUnit M)
    (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (huP : u.val = P ⊗ₜ[ℂ] x) (hvQ : v.val = Q ⊗ₜ[ℂ] p)
    (hR : R ⊗ₜ[ℂ] z ∈ actualGrade ℒ leechUnit L)
    (hS : S ⊗ₜ[ℂ] d ∈ actualGrade ℒ leechUnit N)
    (hpar : Even ((M : ℤ) + (K : ℤ))) {y : ℝ} (hy : (1 / 2 : ℝ) < y) (hy₁ : y < 1) :
    let ξ := laurentRoot .A y
    HasSum (fun n : ℤ => fixedAIterateCoeff s M K L N n u v
      (R ⊗ₜ[ℂ] z) (S ⊗ₜ[ℂ] d) * ξ ^ n)
      (ξ ^ (-((M : ℤ) + (K : ℤ) + 6)) *
        fixedASlitSewn M K P Q R S x p z d (parameter .A (y : ℂ))) := by
  dsimp only
  obtain ⟨hr, hξ, hξsq⟩ := fixedA_laurentRoot hy hy₁
  have h0 : laurentRoot .A y ≠ 0 := by
    rw [hξ]
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (neg_pos.mpr hr)).ne'
  obtain ⟨hsew, _, hsew_norm, _⟩ := upper_sewing_root hy hy₁
  have hnorm : ‖laurentRoot .A y‖ < 1 := by
    simpa only [hsew, (laurentRoot_values hy₁).1, norm_mul, Complex.norm_I, one_mul]
      using hsew_norm
  simpa only [hξsq, neg_neg] using fixedAIterate_hasSum s M K L N u v P Q R S x p z d
    hu hv huP hvQ hR hS hpar h0 hnorm

/-- An HH ground front pair with either a BB back pair or an HH back pair.
Use `t = true` for HHBB and `t = false, L = N = 0` for four ground states. -/
theorem hh_fixedAIterate_hasSum_on_overlap (t : Bool) (L N : ℕ)
    (u v : TwistedEven) (w b : Twisted ℒ leechUnit t)
    (P Q R S : Oscillator ℒ) (x p z d : ActualGround ℒ leechUnit)
    (hu : u.val ∈ actualGrade ℒ leechUnit 0)
    (hv : v.val ∈ actualGrade ℒ leechUnit 0)
    (hw : w.val ∈ actualGrade ℒ leechUnit L)
    (hb : b.val ∈ actualGrade ℒ leechUnit N)
    (huP : u.val = P ⊗ₜ[ℂ] x) (hvQ : v.val = Q ⊗ₜ[ℂ] p)
    (hwR : w.val = R ⊗ₜ[ℂ] z) (hbS : b.val = S ⊗ₜ[ℂ] d)
    {y : ℝ} (hy : (1 / 2 : ℝ) < y) (hy₁ : y < 1) :
    let ξ := laurentRoot .A y
    HasSum (fun n : ℤ => fixedAIterateCoeff false 0 0 L N n u v w.val b.val * ξ ^ n)
      (ξ ^ (-6 : ℤ) * fixedASlitSewn 0 0 P Q R S x p z d (parameter .A (y : ℂ))) := by
  dsimp only
  rw [hwR, hbS]
  exact fixedAIterate_hasSum_on_overlap false 0 0 L N u v P Q R S x p z d hu hv huP hvQ
    (hwR ▸ hw) (hbS ▸ hb) (by decide) hy hy₁

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedPairAIterate
