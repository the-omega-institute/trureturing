/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedWickCuspGerm
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedWickCuspGerm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual mixed Leech four-point energy diagonal descends to an analytic cusp germ. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeDoubledOccupationReadout
import Mathlib.RingTheory.LaurentSeries

/-! The local sewn germ for the mixed iterate of the actual Leech twisted fields. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators Topology TensorProduct VertexOperator
open Filter

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedWickCuspGerm

open LatticeGeneratingFieldLocality LatticeHalfFock LatticePositiveEnergy LatticeInvolution
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockGradedTrace LatticeTwistedGroundRealization
open LatticeTwistedGroundRealization.SignQuotient
open ActualLeechHyperbolic (leechData leech_spec)
open ActualChargedAdjoint (actualForm)
open OperatorAlgebra (chargeOperator)
open Orbifold.NativeOddTwistedIntertwiner (Twisted leechUnit OddCarrier)
open Orbifold.NativeOddUpperRightSkew (R R_pairing_finite)
open Orbifold.NativeMixedPairField (mu mu_coeff_even_zero mu_lower_truncation)
open ActualEnergyRestrictedDual (maxOddWeight)
open OriginalFourMVariableSupport (occupationReadout inverseFlow)
open OriginalFourMChargeGerm (chargeSectorSewn)
open OriginalFourMChargeCoset (oscillatorLower)
open OriginalGaussianSewnAnalytic (coefficient)
open NativeDoubledOccupationReadout (mu_fourPoint_sewn_taylor)

open private groundForm lower_power_tmul from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset
open private T lowering_eigen from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private actualGrade_eigen from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
open private J_val from D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
open private analytic_neg_square_even_part chargeSectorSewn_analyticAt
  coefficient_fun_sum coefficient_const_mul from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMChargeGerm

/-- One actual sewn charge sector with the two finite inverse flows on the left. -/
def mixedOccupationSewn (M K : ℕ) (P Q R S : Oscillator leechData)
    (a : ModTwoCharge leechData) (ρ : ℂ) : ℂ :=
  occupationReadout leechData (inverseFlow leechData (M / 2 + 1) P)
    (inverseFlow leechData (K / 2 + 1) Q) R S
    (fun β γ δ η => chargeSectorSewn leechData a β γ δ η ρ)

theorem mixedOccupationSewn_analyticAt (M K : ℕ) (P Q R S : Oscillator leechData)
    (a : ModTwoCharge leechData) :
    AnalyticAt ℂ (mixedOccupationSewn M K P Q R S a) 0 := by
  have hsector (β γ δ η : Exponent leechData) :
      AnalyticAt ℂ (chargeSectorSewn leechData a β γ δ η) 0 :=
    chargeSectorSewn_analyticAt leechData leechUnit leech_spec.2.2.1 a β γ δ η
  unfold mixedOccupationSewn occupationReadout
  fun_prop

private def mixedGroundWeight (x y z d : ActualGround leechData leechUnit)
    (a : ModTwoCharge leechData) : ℂ :=
  groundForm leechData leechUnit y
    (chargeOperator leechData (groundRepresentation leechData leechUnit) a x) *
  groundForm leechData leechUnit d
    (chargeOperator leechData (groundRepresentation leechData leechUnit) a z)

/-- The two ordered ground forms and the constant BPZ phase weight the sewn sectors. -/
def mixedSewn (M K : ℕ) (P Q R S : Oscillator leechData)
    (x y z d : ActualGround leechData leechUnit) (ρ : ℂ) : ℂ :=
  Complex.I ^ ((K : ℤ) - 2 * (M : ℤ) - 3) *
    ∑ a : ModTwoCharge leechData, mixedGroundWeight x y z d a *
      mixedOccupationSewn M K P Q R S a ρ

theorem mixedSewn_analyticAt (M K : ℕ) (P Q R S : Oscillator leechData)
    (x y z d : ActualGround leechData leechUnit) :
    AnalyticAt ℂ (mixedSewn M K P Q R S x y z d) 0 := by
  classical
  have hsector (a : ModTwoCharge leechData) :
      AnalyticAt ℂ (mixedOccupationSewn M K P Q R S a) 0 :=
    mixedOccupationSewn_analyticAt M K P Q R S a
  unfold mixedSewn
  fun_prop

private theorem coefficient_mixedSewn (M K : ℕ) (P Q R S : Oscillator leechData)
    (x y z d : ActualGround leechData leechUnit) (j : ℕ) :
    coefficient j (mixedSewn M K P Q R S x y z d) =
      Complex.I ^ ((K : ℤ) - 2 * (M : ℤ) - 3) *
        ∑ a : ModTwoCharge leechData, mixedGroundWeight x y z d a *
          coefficient j (mixedOccupationSewn M K P Q R S a) := by
  classical
  have hsector (a : ModTwoCharge leechData) :
      AnalyticAt ℂ (mixedOccupationSewn M K P Q R S a) 0 :=
    mixedOccupationSewn_analyticAt M K P Q R S a
  unfold mixedSewn
  simp (discharger := fun_prop) only [coefficient_fun_sum, coefficient_const_mul]

/-- The literal scalar coefficient of the actual mixed field on the energy diagonal. -/
def mixedScalar (s : Bool) (M K L N : ℕ)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s))
    (w b : ActualTensor leechData leechUnit) (E : ℕ) : ℂ :=
  let m : ℤ := ((M : ℤ) + (K : ℤ) + 3) / 2 - (E : ℤ)
  let eR : ℤ := (N : ℤ) - (L : ℤ) - 2 * (E : ℤ)
  actualForm leechData leechUnit b
    ((correctedField leechData leechUnit ((mu s u).coeff (-2 * m - 3) v).val).coeff eR w)

/-- Taylor extraction from the actual finite weighted occupation sum on every energy. -/
theorem mixedScalar_eq_sewn_coefficient (s : Bool) (M K L N E : ℕ)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s))
    (P Q R S : Oscillator leechData) (x y z d : ActualGround leechData leechUnit)
    (hu : u.val ∈ actualGrade leechData leechUnit M)
    (hv : v.val ∈ actualGrade leechData leechUnit K)
    (huP : u.val = P ⊗ₜ[ℂ] x) (hvQ : v.val = Q ⊗ₜ[ℂ] y)
    (hR : R ⊗ₜ[ℂ] z ∈ actualGrade leechData leechUnit L)
    (hS : S ⊗ₜ[ℂ] d ∈ actualGrade leechData leechUnit N)
    (hpar : Odd ((M : ℤ) + (K : ℤ))) :
    mixedScalar s M K L N u v (R ⊗ₜ[ℂ] z) (S ⊗ₜ[ℂ] d) E =
      (-1 : ℂ) ^ E * coefficient (2 * E) (mixedSewn M K P Q R S x y z d) := by
  let m : ℤ := ((M : ℤ) + (K : ℤ) + 3) / 2 - (E : ℤ)
  let eR : ℤ := (N : ℤ) - (L : ℤ) - 2 * (E : ℤ)
  have hE : 2 * (E : ℤ) = (M : ℤ) + (K : ℤ) + 3 - 2 * m := by
    obtain ⟨k, hk⟩ := hpar
    dsimp only [m]
    omega
  rw [coefficient_mixedSewn]
  unfold mixedGroundWeight mixedOccupationSewn
  have h := mu_fourPoint_sewn_taylor s M K L N E m eR u v P Q R S x y z d
    hu hv huP hvQ hR hS hE
  simpa only [mixedScalar, m, eR, ite_true, zpow_natCast, mul_assoc] using h

/-- The actual scalar diagonal is the Taylor series of a holomorphic germ whose
negative-square pullback is the even part of the weighted sewn occupation. -/
theorem mixedScalar_negative_square_germ (s : Bool) (M K L N : ℕ)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s))
    (P Q R S : Oscillator leechData) (x y z d : ActualGround leechData leechUnit)
    (hu : u.val ∈ actualGrade leechData leechUnit M)
    (hv : v.val ∈ actualGrade leechData leechUnit K)
    (huP : u.val = P ⊗ₜ[ℂ] x) (hvQ : v.val = Q ⊗ₜ[ℂ] y)
    (hR : R ⊗ₜ[ℂ] z ∈ actualGrade leechData leechUnit L)
    (hS : S ⊗ₜ[ℂ] d ∈ actualGrade leechData leechUnit N)
    (hpar : Odd ((M : ℤ) + (K : ℤ))) :
    let F := mixedSewn M K P Q R S x y z d
    ∃ G : ℂ → ℂ,
      HasFPowerSeriesAt G (FormalMultilinearSeries.ofScalars ℂ
        (mixedScalar s M K L N u v (R ⊗ₜ[ℂ] z) (S ⊗ₜ[ℂ] d))) 0 ∧
      ∀ᶠ ρ in 𝓝 (0 : ℂ), G (-(ρ ^ 2)) = (F ρ + F (-ρ)) / 2 := by
  dsimp only
  obtain ⟨G, hG, hpull⟩ :=
    analytic_neg_square_even_part (mixedSewn_analyticAt M K P Q R S x y z d)
  have hc : (fun E : ℕ => (-1 : ℂ) ^ E *
      coefficient (2 * E) (mixedSewn M K P Q R S x y z d)) =
      mixedScalar s M K L N u v (R ⊗ₜ[ℂ] z) (S ⊗ₜ[ℂ] d) := by
    funext E
    exact (mixedScalar_eq_sewn_coefficient s M K L N E u v P Q R S x y z d
      hu hv huP hvQ hR hS hpar).symm
  exact ⟨G, hc ▸ hG, hpull⟩

private def mixedExponent (M K : ℕ) : ℕ ↪o ℤ :=
  OrderEmbedding.ofStrictMono (fun E : ℕ => 2 * (E : ℤ) - ((M : ℤ) + (K : ℤ) + 6))
    (by
      intro i j hij
      change 2 * (i : ℤ) - ((M : ℤ) + (K : ℤ) + 6) <
        2 * (j : ℤ) - ((M : ℤ) + (K : ℤ) + 6)
      omega)

/-- The Laurent series in the doubled field coordinate, indexed by
`2 * E - (M + K + 6)` for every Taylor energy `E`. -/
def mixedFieldLaurent (s : Bool) (M K L N : ℕ)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s))
    (w b : ActualTensor leechData leechUnit) : LaurentSeries ℂ :=
  HahnSeries.embDomain (mixedExponent M K)
    (HahnSeries.toPowerSeries.symm (PowerSeries.mk (mixedScalar s M K L N u v w b)))

theorem mixedFieldLaurent_coeff_energy (s : Bool) (M K L N E : ℕ)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s))
    (w b : ActualTensor leechData leechUnit) :
    (mixedFieldLaurent s M K L N u v w b).coeff
        (2 * (E : ℤ) - ((M : ℤ) + (K : ℤ) + 6)) =
      mixedScalar s M K L N u v w b E := by
  change (HahnSeries.embDomain (mixedExponent M K) _).coeff (mixedExponent M K E) = _
  rw [HahnSeries.embDomain_coeff, HahnSeries.coeff_toPowerSeries_symm, PowerSeries.coeff_mk]

private theorem maxOddWeight_le_grade {M : ℕ} {w : ActualTensor leechData leechUnit}
    (hw : w ∈ actualGrade leechData leechUnit M) : maxOddWeight leechData leechUnit w ≤ M := by
  unfold maxOddWeight
  refine Finset.sup_le ?_
  intro i hi
  exact ((actual_grade_mem_iff_repr_support leechData leechUnit M w).mp hw i hi).le

/-- At every doubled exponent the Laurent lift has the literal mixed iterate
coefficient, including the vanishing exponents outside the energy support. -/
theorem mixedFieldLaurent_coeff (s : Bool) (M K L N : ℕ) (n : ℤ)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s))
    (w b : ActualTensor leechData leechUnit)
    (hu : u.val ∈ actualGrade leechData leechUnit M)
    (hv : v.val ∈ actualGrade leechData leechUnit K)
    (hpar : Odd ((M : ℤ) + (K : ℤ))) :
    (mixedFieldLaurent s M K L N u v w b).coeff n =
      actualForm leechData leechUnit b
        ((correctedField leechData leechUnit ((mu s u).coeff n v).val).coeff
          ((N : ℤ) - (L : ℤ) - (n + (M : ℤ) + (K : ℤ) + 6)) w) := by
  by_cases hn : n ∈ Set.range (mixedExponent M K)
  · obtain ⟨E, rfl⟩ := hn
    change (mixedFieldLaurent s M K L N u v w b).coeff
      (2 * (E : ℤ) - ((M : ℤ) + (K : ℤ) + 6)) = _
    rw [mixedFieldLaurent_coeff_energy]
    have hn : -2 * (((M : ℤ) + (K : ℤ) + 3) / 2 - (E : ℤ)) - 3 =
        mixedExponent M K E := by
      change _ = 2 * (E : ℤ) - ((M : ℤ) + (K : ℤ) + 6)
      obtain ⟨k, hk⟩ := hpar
      omega
    have heR : (N : ℤ) - (L : ℤ) - (mixedExponent M K E + (M : ℤ) + (K : ℤ) + 6) =
        (N : ℤ) - (L : ℤ) - 2 * (E : ℤ) := by
      change (N : ℤ) - (L : ℤ) -
        (2 * (E : ℤ) - ((M : ℤ) + (K : ℤ) + 6) + (M : ℤ) + (K : ℤ) + 6) = _
      ring
    simp only [mixedScalar, hn, heR]
  · have hz : (mu s u).coeff n v = 0 := by
      by_cases he : Even n
      · exact mu_coeff_even_zero s n u v he
      · have hlt : n < -((M : ℤ) + (K : ℤ) + 6) := by
          by_contra! hge
          apply hn
          refine ⟨((n + (M : ℤ) + (K : ℤ) + 6) / 2).toNat, ?_⟩
          change 2 * (((n + (M : ℤ) + (K : ℤ) + 6) / 2).toNat : ℤ) -
            ((M : ℤ) + (K : ℤ) + 6) = n
          obtain ⟨k, hk⟩ := hpar
          have hnodd := Int.not_even_iff.mp he
          omega
        have hMu : (maxOddWeight leechData leechUnit u.val : ℤ) ≤ (M : ℤ) := by
          exact_mod_cast maxOddWeight_le_grade hu
        have hMv : (maxOddWeight leechData leechUnit v.val : ℤ) ≤ (K : ℤ) := by
          exact_mod_cast maxOddWeight_le_grade hv
        exact mu_lower_truncation s u v n (by omega)
    rw [mixedFieldLaurent, HahnSeries.embDomain_of_notMem_range hn, hz]
    simp

/-- Near the puncture the Laurent lift sums to the analytic numerator
evaluated at `ξ ^ 2`, times the signed Laurent monomial. -/
theorem mixedFieldLaurent_hasSum (s : Bool) (M K L N : ℕ)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s))
    (w b : ActualTensor leechData leechUnit) {G : ℂ → ℂ}
    (hG : HasFPowerSeriesAt G (FormalMultilinearSeries.ofScalars ℂ
      (mixedScalar s M K L N u v w b)) 0) :
    ∀ᶠ ξ in 𝓝 (0 : ℂ), ξ ≠ 0 → HasSum (fun E : ℕ =>
      (mixedFieldLaurent s M K L N u v w b).coeff
        (2 * (E : ℤ) - ((M : ℤ) + (K : ℤ) + 6)) *
      ξ ^ (2 * (E : ℤ) - ((M : ℤ) + (K : ℤ) + 6)))
      (ξ ^ (-((M : ℤ) + (K : ℤ) + 6)) * G (ξ ^ 2)) := by
  have hsquare : Tendsto (fun ξ : ℂ => ξ ^ 2) (𝓝 0) (𝓝 0) := by
    have h : Continuous (fun ξ : ℂ => ξ ^ 2) := by fun_prop
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using h.tendsto 0
  filter_upwards [hsquare.eventually hG.eventually_hasSum] with ξ hξ h0
  have hpow (E : ℕ) : ξ ^ (2 * (E : ℤ) - ((M : ℤ) + (K : ℤ) + 6)) =
      ξ ^ (-((M : ℤ) + (K : ℤ) + 6)) * (ξ ^ 2) ^ E := by
    rw [show 2 * (E : ℤ) - ((M : ℤ) + (K : ℤ) + 6) =
      -((M : ℤ) + (K : ℤ) + 6) + 2 * (E : ℤ) by ring,
      zpow_add₀ h0, zpow_mul, zpow_natCast _ E]
    rfl
  have hsum : HasSum (fun E : ℕ => mixedScalar s M K L N u v w b E * (ξ ^ 2) ^ E)
      (G (ξ ^ 2)) := by
    simpa only [zero_add, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using hξ
  refine (hsum.mul_left (ξ ^ (-((M : ℤ) + (K : ℤ) + 6)))).congr_fun ?_
  intro E
  rw [mixedFieldLaurent_coeff_energy, hpow]
  ring

private theorem upper_phase_energy (e : ℤ) (E ell : ℕ) :
    Complex.I ^ (e - 2 * (E : ℤ) - 2 * (ell : ℤ)) =
      ((-1 : ℂ) ^ E * Complex.I ^ e) * (-1 : ℂ) ^ ell := by
  have hi : Complex.I ^ (-2 : ℤ) = -1 := by
    rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) by decide, zpow_neg, zpow_natCast,
      Complex.I_sq, inv_neg, inv_one]
  rw [show e - 2 * (E : ℤ) - 2 * (ell : ℤ) =
      e + (-2) * (E : ℤ) + (-2) * (ell : ℤ) by ring]
  simp only [zpow_add₀ Complex.I_ne_zero, zpow_mul Complex.I (-2), hi, zpow_natCast]
  ring

/-- Reindex the actual upper-branch `R` pairing by the source energy. The
translation transpose lowers the detector and shifts its raw mode by `-2 * ell`. -/
theorem R_pairing_energy_diagonal (s : Bool) (L N E : ℕ) (n₀ : ℤ)
    (w : Twisted leechData leechUnit s) (b : Twisted leechData leechUnit (!s))
    (a : OddCarrier leechData) (hb : b.val ∈ actualGrade leechData leechUnit N)
    (hn₀ : -2 * n₀ - 3 = (N : ℤ) - (L : ℤ)) :
    actualForm leechData leechUnit b.val (R leechData leechUnit s (n₀ + (E : ℤ)) w a).val =
      ((-1 : ℂ) ^ E * Complex.I ^ ((N : ℤ) - (L : ℤ))) *
        ∑ ell ∈ Finset.range (N / 2 + 1),
          ((-1 : ℂ) ^ ell * (ell.factorial : ℂ)⁻¹) *
            actualForm leechData leechUnit ((T leechData leechUnit ^ ell) b.val)
              ((correctedField leechData leechUnit a.val).coeff
                ((N : ℤ) - (L : ℤ) - 2 * (E : ℤ) - 2 * (ell : ℤ)) w.val) := by
  rw [R_pairing_finite leechData leechUnit s _ N w a b hb, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ell _
  have he : -2 * (n₀ + (E : ℤ) + (ell : ℤ)) - 3 =
      (N : ℤ) - (L : ℤ) - 2 * (E : ℤ) - 2 * (ell : ℤ) := by omega
  rw [J_val, he, upper_phase_energy]
  ring

/-- On the actual mixed coefficient the upper right-skew energy sign cancels
the negative-square Taylor sign, with the indicated lowered tensor detector. -/
theorem mixedR_pairing_eq_sewn_coefficient (s t : Bool) (M K L N E : ℕ) (n₀ : ℤ)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s))
    (w : Twisted leechData leechUnit t) (b : Twisted leechData leechUnit (!t))
    (P Q U S : Oscillator leechData) (x y z d : ActualGround leechData leechUnit)
    (hu : u.val ∈ actualGrade leechData leechUnit M)
    (hv : v.val ∈ actualGrade leechData leechUnit K)
    (hw : w.val ∈ actualGrade leechData leechUnit L)
    (hb : b.val ∈ actualGrade leechData leechUnit N)
    (huP : u.val = P ⊗ₜ[ℂ] x) (hvQ : v.val = Q ⊗ₜ[ℂ] y)
    (hwU : w.val = U ⊗ₜ[ℂ] z) (hbS : b.val = S ⊗ₜ[ℂ] d)
    (hpar : Odd ((M : ℤ) + (K : ℤ))) (hn₀ : -2 * n₀ - 3 = (N : ℤ) - (L : ℤ)) :
    let m : ℤ := ((M : ℤ) + (K : ℤ) + 3) / 2 - (E : ℤ)
    actualForm leechData leechUnit b.val
        (R leechData leechUnit t (n₀ + (E : ℤ)) w ((mu s u).coeff (-2 * m - 3) v)).val =
      Complex.I ^ ((N : ℤ) - (L : ℤ)) *
        ∑ ell ∈ Finset.range (N / 2 + 1),
          ((-1 : ℂ) ^ ell * (ell.factorial : ℂ)⁻¹) *
            coefficient (2 * E) (mixedSewn M K P Q U ((oscillatorLower leechData ^ ell) S) x y z d) := by
  dsimp only
  rw [R_pairing_energy_diagonal t L N E n₀ w b _ hb hn₀]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ell hell
  have hellN : 2 * ell ≤ N := by
    have h := Finset.mem_range.mp hell
    omega
  have hgrade : ((N - 2 * ell : ℕ) : ℤ) = (N : ℤ) - 2 * (ell : ℤ) := by omega
  have hbEigen := (actualGrade_eigen leechData leechUnit N b.val).mp hb
  have hlow := lowering_eigen leechData leechUnit (N : ℤ) b.val
    (by simpa only [Int.cast_natCast] using hbEigen) ell
  have hS : (oscillatorLower leechData ^ ell) S ⊗ₜ[ℂ] d ∈
      actualGrade leechData leechUnit (N - 2 * ell) := by
    apply (actualGrade_eigen leechData leechUnit _ _).mpr
    rw [← hgrade, Int.cast_natCast] at hlow
    simpa only [hbS, T, lower_power_tmul] using hlow
  have hcoeff := mixedScalar_eq_sewn_coefficient s M K L (N - 2 * ell) E u v
    P Q U ((oscillatorLower leechData ^ ell) S) x y z d hu hv huP hvQ (hwU ▸ hw) hS hpar
  have he : ((N - 2 * ell : ℕ) : ℤ) - (L : ℤ) - 2 * (E : ℤ) =
      (N : ℤ) - (L : ℤ) - 2 * (E : ℤ) - 2 * (ell : ℤ) := by omega
  simp only [mixedScalar, he] at hcoeff
  rw [hwU, hbS, T, lower_power_tmul, hcoeff]
  have hsign : (-1 : ℂ) ^ E * (-1 : ℂ) ^ E = 1 := by
    rw [← mul_pow]
    norm_num
  linear_combination
    (Complex.I ^ ((N : ℤ) - (L : ℤ)) * (((-1 : ℂ) ^ ell * (ell.factorial : ℂ)⁻¹) *
      coefficient (2 * E)
        (mixedSewn M K P Q U ((oscillatorLower leechData ^ ell) S) x y z d))) * hsign

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedWickCuspGerm
