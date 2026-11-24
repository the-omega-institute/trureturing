/- GID: D5/S3/VertexAlgebra/Characters/ActualLeechOrbifoldHeckeExpansion
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/ActualLeechOrbifoldHeckeExpansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed root-of-unity filter and the weight-zero Hecke expansion of the native Leech character. -/

import D5.S3.VertexAlgebra.Characters.ActualLeechOrbifoldMoonshineCharacter
import D5.S3.VertexAlgebra.Lattice.InvolutionRootlessLowGrades
import D5.S3.VertexAlgebra.Lattice.LeechLowSpectrum
import Mathlib.NumberTheory.Divisors
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! The triangular Hecke sum of the actual Leech orbifold character `J = j - 744`.
The signed root-of-unity filter treats the Laurent pole and positive exponents
uniformly. The convergent positive part uses the literal stress dimensions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Complex Function UpperHalfPlane
open scoped BigOperators

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldHeckeExpansion

open ActualLeechOrbifoldTraceSeries (character dimension graded_dimension_series)
open ActualLeechOrbifoldMoonshineCharacter (character_eq_j_sub_744 four_traces_eq_j_sub_744)
open ActualLeechOrbifoldAllWeightDimension
  (FixedWeight weight_finrank weightMultiplicity fixed_weight_finrank_eq_coefficients
    twistedMultiplicity)
open ActualLeechHyperbolic (leechData leechCoordinates leech_spec)
open private no_roots from D5.S3.VertexAlgebra.Lattice.LeechLowSpectrum
open ActualLeechOrbifoldMatter (leechUnit leechPosDef)
open HalfFockSpectralFiberSource (actualInverse actualInverse_left)
open LatticeSugawaraCurrents (gramComplex sugawaraMode)
open LatticeInvolution (fixedSpace)
open Lattice.InvolutionRootlessLowGrades (actual_theta_fixed_rootless_low_spectrum)

local notation "𝕢" => Periodic.qParam 1

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem low_dimensions : dimension 0 = 1 ∧ dimension 1 = 0 := by
  have hinv : actualInverse leechData = (gramComplex leechData)⁻¹ :=
    (Matrix.inv_eq_left_inv (actualInverse_left leechData leechUnit)).symm
  have h := actual_theta_fixed_rootless_low_spectrum leechData leechPosDef
    (no_roots leechCoordinates leech_spec.2.2.2)
  have hdim (n : ℤ) : dimension n = Module.finrank ℂ (FixedWeight n) + twistedMultiplicity n := by
    have hn := weight_finrank n
    change (dimension n : ℂ) = weightMultiplicity n at hn
    rw [weightMultiplicity, ← fixed_weight_finrank_eq_coefficients] at hn
    exact_mod_cast hn
  have hfixed (n : ℤ) : FixedWeight n =
      fixedSpace leechData ⊓ (sugawaraMode leechData (gramComplex leechData)⁻¹ 0).eigenspace
        (n : ℂ) := by
    unfold FixedWeight ActualLeechOrbifoldAllWeightDimension.UntwistedWeight
    rw [hinv]
  constructor
  · rw [hdim, show twistedMultiplicity 0 = 0 by norm_num [twistedMultiplicity], add_zero,
      hfixed, Int.cast_zero]
    exact h.1
  · rw [hdim, show twistedMultiplicity 1 = 0 by norm_num [twistedMultiplicity], add_zero,
      hfixed, Int.cast_one]
    exact h.2.1

/-- The Laurent coefficient of exponent `k ≥ 0` is the native dimension at weight `k+1`. -/
def coeff (k : ℕ) : ℂ :=
  (dimension ((k : ℤ) + 1) : ℂ)

@[simp] theorem coeff_zero : coeff 0 = 0 := by
  simp [coeff, low_dimensions.2]

private theorem character_hasSum (τ : ℍ) :
    HasSum (fun k : ℕ => coeff k * 𝕢 τ ^ k) (character τ - (𝕢 τ)⁻¹) := by
  let term : ℕ → ℂ := fun n => (𝕢 τ)⁻¹ * ((dimension n : ℂ) * 𝕢 τ ^ n)
  have h : HasSum term (character τ) := by
    rw [character_eq_j_sub_744, ← four_traces_eq_j_sub_744]
    exact (graded_dimension_series τ).2
  have hzero : term 0 = (𝕢 τ)⁻¹ := by simp [term, low_dimensions.1]
  have htail : HasSum (fun k : ℕ => term (k + 1)) (character τ - (𝕢 τ)⁻¹) := by
    apply (hasSum_nat_add_iff (f := term) 1).2
    rw [Finset.sum_range_one, hzero, sub_add_cancel]
    exact h
  refine htail.congr_fun fun k => ?_
  simp only [term, coeff, Nat.cast_add, Nat.cast_one, pow_succ', ← mul_assoc]
  rw [mul_right_comm (𝕢 τ)⁻¹, inv_mul_cancel₀ (Periodic.qParam_ne_zero (τ : ℂ)), one_mul]

/-- The point associated to the triangular matrix with entries `a, b, 0, d`. -/
def triangularPoint (a d : ℕ) (ha : 0 < a) (hd : 0 < d) (b : ℕ) (τ : ℍ) : ℍ :=
  ⟨((a : ℂ) * (τ : ℂ) + (b : ℂ)) / (d : ℂ), by
    rw [← Complex.ofReal_natCast d, Complex.div_ofReal_im]
    simpa [Complex.add_im, Complex.mul_im] using
      (div_pos (mul_pos (Nat.cast_pos.mpr ha) τ.im_pos) (Nat.cast_pos.mpr hd))⟩

@[simp] theorem coe_triangularPoint {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (b : ℕ) (τ : ℍ) :
    (triangularPoint a d ha hd b τ : ℂ) = ((a : ℂ) * (τ : ℂ) + b) / d :=
  rfl

private theorem q_triangularPoint {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (b : ℕ) (τ : ℍ) :
    𝕢 (triangularPoint a d ha hd b τ) =
      Periodic.qParam d ((a : ℂ) * τ) * Periodic.qParam d 1 ^ b := by
  simp only [coe_triangularPoint, Periodic.qParam, Complex.ofReal_one, div_one,
    Complex.ofReal_natCast, ← Complex.exp_nat_mul, ← Complex.exp_add, mul_one]
  congr 1
  ring

private theorem qParam_pow {a d : ℕ} (hd : 0 < d) (τ : ℍ) :
    Periodic.qParam d ((a : ℂ) * τ) ^ d = 𝕢 τ ^ a := by
  simp only [Periodic.qParam, Complex.ofReal_natCast, Complex.ofReal_one, div_one,
    ← Complex.exp_nat_mul]
  congr 1
  field_simp [show (d : ℂ) ≠ 0 from Nat.cast_ne_zero.mpr hd.ne']

/-- The finite primitive-root filter, including negative exponents. -/
theorem sum_root_zpow {ζ : ℂ} {d : ℕ} (hζ : IsPrimitiveRoot ζ d) (k : ℤ) :
    (∑ b ∈ Finset.range d, (ζ ^ b) ^ k) =
      if (d : ℤ) ∣ k then (d : ℂ) else 0 := by
  have hz (b : ℕ) : (ζ ^ b) ^ k = (ζ ^ k) ^ b := by
    rw [← zpow_natCast ζ b, ← zpow_natCast (ζ ^ k) b, ← zpow_mul, ← zpow_mul, mul_comm]
  simp only [hz]
  by_cases hk : (d : ℤ) ∣ k
  · simp [hk, (hζ.zpow_eq_one_iff_dvd k).mpr hk]
  · rw [ite_eq_right hk]
    have hp : (ζ ^ k) ^ d = 1 := by rw [← zpow_natCast, ← zpow_mul', zpow_mul, zpow_natCast,
      hζ.pow_eq_one, one_zpow]
    have hn : ζ ^ k - 1 ≠ 0 := sub_ne_zero.mpr (mt (hζ.zpow_eq_one_iff_dvd k).mp hk)
    exact (mul_eq_zero.mp ((geom_sum_mul (ζ ^ k) d).trans (sub_eq_zero.mpr hp))).resolve_right hn

/-- The signed filter for the actual q-parameters of the triangular translates. -/
theorem sum_triangular_q_zpow {a d : ℕ} (ha : 0 < a) (hd : 0 < d)
    (τ : ℍ) (k : ℤ) :
    (∑ b ∈ Finset.range d, 𝕢 (triangularPoint a d ha hd b τ) ^ k) =
      Periodic.qParam d ((a : ℂ) * τ) ^ k * (if (d : ℤ) ∣ k then (d : ℂ) else 0) := by
  have hζ : IsPrimitiveRoot (Periodic.qParam d 1) d := by
    simpa [Periodic.qParam] using Complex.isPrimitiveRoot_exp d hd.ne'
  simp only [q_triangularPoint ha hd, mul_zpow, ← Finset.mul_sum, sum_root_zpow hζ]

/-- The vacuum poles cancel when `d > 1`, and give `q⁻ᵃ` when `d = 1`. -/
theorem sum_triangular_pole {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (τ : ℍ) :
    (∑ b ∈ Finset.range d, (𝕢 (triangularPoint a d ha hd b τ))⁻¹) =
      if d = 1 then (𝕢 τ ^ a)⁻¹ else 0 := by
  have hdvd : (d : ℤ) ∣ (-1 : ℤ) ↔ d = 1 := by
    rw [dvd_neg]
    exact_mod_cast (Nat.dvd_one : d ∣ 1 ↔ d = 1)
  have h := sum_triangular_q_zpow ha hd τ (-1)
  simp only [zpow_neg_one, hdvd] at h
  rw [h]
  split_ifs with he
  · have hp := qParam_pow (a := a) hd τ
    simp [he] at hp
    simp [he, hp]
  · simp

/-- The unnormalized sum over the translates in one triangular row. -/
def triangularSum {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (τ : ℍ) : ℂ :=
  ∑ b ∈ Finset.range d, character (triangularPoint a d ha hd b τ)

private theorem hasSum_iff_multiples {d : ℕ} (hd : 0 < d) {f : ℕ → ℂ} {s : ℂ}
    (hf : ∀ k, ¬ d ∣ k → f k = 0) :
    HasSum (fun k : ℕ => f (d * k)) s ↔ HasSum f s := by
  have hi : Injective (fun k : ℕ => d * k) := fun _ _ h =>
    Nat.eq_of_mul_eq_mul_left hd h
  exact hi.hasSum_iff fun k hk => hf k fun ⟨j, hj⟩ => hk ⟨j, hj.symm⟩

private theorem triangularSum_hasSum_all {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (τ : ℍ) :
    HasSum (fun l : ℕ => (d : ℂ) * coeff (d * l) * 𝕢 τ ^ (a * l))
      (triangularSum ha hd τ - if d = 1 then (𝕢 τ ^ a)⁻¹ else 0) := by
  let f : ℕ → ℂ := fun k =>
    coeff k * Periodic.qParam d ((a : ℂ) * τ) ^ k * (if d ∣ k then (d : ℂ) else 0)
  have hs : HasSum f (triangularSum ha hd τ - if d = 1 then (𝕢 τ ^ a)⁻¹ else 0) := by
    rw [← sum_triangular_pole ha hd τ, triangularSum, ← Finset.sum_sub_distrib]
    refine (hasSum_sum fun b (_ : b ∈ Finset.range d) =>
      character_hasSum (triangularPoint a d ha hd b τ)).congr_fun fun k => ?_
    have h := sum_triangular_q_zpow ha hd τ (k : ℤ)
    simp only [zpow_natCast, Int.natCast_dvd_natCast] at h
    rw [← Finset.mul_sum, h]
    exact mul_assoc _ _ _
  have hm := (hasSum_iff_multiples hd (fun k hk => by simp [f, hk])).2 hs
  refine hm.congr_fun fun l => ?_
  simp only [f, ite_eq_left (dvd_mul_right d l), pow_mul _ d l, qParam_pow hd τ, pow_mul _ a l]
  ring

/-- The signed filter leaves a convergent series on the positive exponent multiples of `d`. -/
theorem triangularSum_hasSum {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (τ : ℍ) :
    HasSum (fun l : ℕ => (d : ℂ) * coeff (d * (l + 1)) * 𝕢 τ ^ (a * (l + 1)))
      (triangularSum ha hd τ - if d = 1 then (𝕢 τ ^ a)⁻¹ else 0) := by
  apply (hasSum_nat_add_iff (f := fun l : ℕ => (d : ℂ) * coeff (d * l) * 𝕢 τ ^ (a * l)) 1).2
  simpa using triangularSum_hasSum_all ha hd τ

/-- The row formula with its polar part and the factor `d` outside the positive series. -/
theorem triangularSum_eq {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (τ : ℍ) :
    triangularSum ha hd τ = (if d = 1 then (𝕢 τ ^ a)⁻¹ else 0) +
      (d : ℂ) * ∑' l : ℕ, coeff (d * (l + 1)) * 𝕢 τ ^ (a * (l + 1)) := by
  have h := (triangularSum_hasSum ha hd τ).tsum_eq
  simp only [mul_assoc, tsum_mul_left] at h
  rw [h]
  ring

private theorem divisorQuotient_pos {a N : ℕ} (ha : a ∈ N.divisors) : 0 < N / a :=
  Nat.div_pos
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisors ha))
      (Nat.dvd_of_mem_divisors ha))
    (Nat.pos_of_mem_divisors ha)

/-- The unnormalized weight-zero Hecke sum over all positive factorizations
`a * d = N`, with `d = N / a` and translates `0 ≤ b < d`. -/
def heckeSum (N : ℕ) (τ : ℍ) : ℂ :=
  ∑ a ∈ N.divisors.attach,
    triangularSum (Nat.pos_of_mem_divisors a.property) (divisorQuotient_pos a.property) τ

/-- The coefficient of exponent `m` in the positive part at determinant `N`. -/
def heckeCoeff (N m : ℕ) : ℂ :=
  ∑ a ∈ (N.gcd m).divisors, ((N / a : ℕ) : ℂ) * coeff ((N / a) * (m / a))

@[simp] theorem heckeCoeff_zero (N : ℕ) : heckeCoeff N 0 = 0 := by
  simp [heckeCoeff]

private theorem triangularSum_hasSum_coefficients {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (τ : ℍ) :
    HasSum (fun m : ℕ => if a ∣ m then (d : ℂ) * coeff (d * (m / a)) * 𝕢 τ ^ m else 0)
      (triangularSum ha hd τ - if d = 1 then (𝕢 τ ^ a)⁻¹ else 0) := by
  apply (hasSum_iff_multiples ha (fun m hm => ite_eq_right hm)).1
  simpa only [ite_eq_left (dvd_mul_right _ _), Nat.mul_div_cancel_left _ ha] using
    triangularSum_hasSum_all ha hd τ

private theorem heckeCoeff_eq_sum {N : ℕ} (hN : 0 < N) (m : ℕ) :
    (∑ a ∈ N.divisors,
      if a ∣ m then ((N / a : ℕ) : ℂ) * coeff ((N / a) * (m / a)) else 0) = heckeCoeff N m := by
  rw [← Finset.sum_filter, heckeCoeff]
  have hG : N.gcd m ≠ 0 := by
    intro h
    have hg := Nat.gcd_dvd_left N m
    rw [h, zero_dvd_iff] at hg
    exact hN.ne' hg
  congr 1
  ext a
  simp [Nat.mem_divisors, hN.ne', hG, Nat.dvd_gcd_iff]

private theorem heckeSum_pole {N : ℕ} (hN : 0 < N) (τ : ℍ) :
    (∑ a ∈ N.divisors, if N / a = 1 then (𝕢 τ ^ a)⁻¹ else 0) = (𝕢 τ ^ N)⁻¹ := by
  rw [Finset.sum_eq_single N]
  · simp [Nat.div_self hN]
  · intro a ha hne
    apply ite_eq_right
    intro hd
    have had := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors ha)
    rw [hd, one_mul] at had
    exact hne had
  · exact fun h => (h (Nat.mem_divisors_self N hN.ne')).elim

/-- The full positive part converges at every upper-half-plane point and the
unique polar term of the unnormalized transform is `q⁻ᴺ`. -/
theorem heckeSum_hasSum {N : ℕ} (hN : 0 < N) (τ : ℍ) :
    HasSum (fun m : ℕ => heckeCoeff N (m + 1) * 𝕢 τ ^ (m + 1))
      (heckeSum N τ - (𝕢 τ ^ N)⁻¹) := by
  have hsum := hasSum_sum
    (s := N.divisors.attach)
    (fun a _ => triangularSum_hasSum_coefficients
      (Nat.pos_of_mem_divisors a.property) (divisorQuotient_pos a.property) τ)
  rw [Finset.sum_sub_distrib, ← heckeSum,
    Finset.sum_attach N.divisors (fun a : ℕ => if N / a = 1 then (𝕢 τ ^ a)⁻¹ else 0),
    heckeSum_pole hN τ] at hsum
  have h : HasSum (fun m : ℕ => heckeCoeff N m * 𝕢 τ ^ m)
      (heckeSum N τ - (𝕢 τ ^ N)⁻¹) := by
    refine hsum.congr_fun fun m => ?_
    rw [Finset.sum_attach N.divisors (fun a : ℕ =>
      if a ∣ m then ((N / a : ℕ) : ℂ) * coeff ((N / a) * (m / a)) * 𝕢 τ ^ m else 0)]
    rw [← heckeCoeff_eq_sum hN m, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> simp
  apply (hasSum_nat_add_iff (f := fun m : ℕ => heckeCoeff N m * 𝕢 τ ^ m) 1).2
  simpa using h

/-- The Laurent expansion of the unnormalized transform of the actual character. -/
theorem heckeSum_eq {N : ℕ} (hN : 0 < N) (τ : ℍ) :
    heckeSum N τ = (𝕢 τ ^ N)⁻¹ + ∑' m : ℕ, heckeCoeff N (m + 1) * 𝕢 τ ^ (m + 1) := by
  rw [(heckeSum_hasSum hN τ).tsum_eq]
  ring

/-- The positive part is absolutely summable throughout the open unit q-disk,
including the cusp coordinate `q = 0`. -/
theorem summable_norm_heckeCoeff {N : ℕ} (hN : 0 < N) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun m : ℕ => ‖heckeCoeff N (m + 1) * q ^ (m + 1)‖) := by
  obtain rfl | hq0 := eq_or_ne q 0
  · simp
  · let τ : ℍ := ⟨Periodic.invQParam 1 q, Periodic.im_invQParam_pos_of_norm_lt_one one_pos hq hq0⟩
    have hτ : 𝕢 τ = q := Periodic.qParam_right_inv one_ne_zero hq0
    simpa only [hτ] using summable_norm_iff.mpr (heckeSum_hasSum hN τ).summable

end D5.S3.VertexAlgebra.ActualLeechOrbifoldHeckeExpansion
