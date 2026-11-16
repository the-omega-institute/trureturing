/- GID: D5/S3/Analytic/Zeta/MercaRelativeClassNumber
   generality: G
   mirror-B: D5/B/S3/Analytic/Zeta/MercaRelativeClassNumber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual Euler products and relative ideal class numbers of the Merca quartic CM field. -/

import D5.S3.Arith.CyclotomicFields.MercaQuarticEulerFactors
import D5.S3.Arith.CyclotomicFields.MercaRealEulerFactors
import D5.S3.ArithUnits.MercaQuarticMoments
import D5.S3.Analytic.Zeta.QuadraticZetaFactorization
import Mathlib.RingTheory.ClassGroup.ExtendedHom

/-!
Classical analytic class-number formulas, the genuine CM regulator theorem and the
actual local factors are combined for the historical Ma--Zhang quartic field.
Louboutin and Hudson retain attribution for the classical relative-class-number
interpretation. No formula from those sources is an assumed premise.
-/
set_option autoImplicit false
noncomputable section
open scoped NumberField BigOperators Topology

namespace D5.S3.Analytic.Zeta.MercaRelativeClassNumber

open NumberField NumberField.InfinitePlace NumberField.Units Filter DirichletCharacter
open D5.S3.Arith.CyclotomicFields
open MercaQuarticField MercaQuadraticSubfield
open D5.S3.ArithUnits.MercaQuarticCharacter
open D5.S3.ArithUnits.MercaQuarticMoments

variable (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5)

private abbrev RealField := maximalRealSubfield (MercaQuarticField.Field r hr)

private lemma inverse_character : (character r hr) ^ 3 = (character r hr)⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  rw [← pow_succ]
  simpa only [(kernel_structure r hr).1] using pow_orderOf_eq_one (character r hr)

private lemma prime_euler_factor (p : ℕ) [Fact p.Prime] (s : ℂ) :
    (∏ P : Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (MercaQuarticField.Field r hr)),
      (1 - (Ideal.absNorm P.1 : ℂ) ^ (-s))⁻¹) =
    (∏ P : Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (RealField r hr)),
      (1 - (Ideal.absNorm P.1 : ℂ) ^ (-s))⁻¹) *
      (1 - character r hr (p : ZMod r) * (p : ℂ) ^ (-s))⁻¹ *
      (1 - (character r hr)⁻¹ (p : ZMod r) * (p : ℂ) ^ (-s))⁻¹ := by
  classical
  have hnorm (K : Type) [Field K] [NumberField K]
      (P : Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)) :
      (Ideal.absNorm P.1 : ℂ) ^ (-s) =
        ((p : ℂ) ^ (-s)) ^ P.val.inertiaDeg ℤ := by
    rw [← Ideal.pow_inertiaDeg p P.1, Nat.cast_pow,
      ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]
  simp_rw [hnorm (MercaQuarticField.Field r hr), hnorm (RealField r hr)]
  rw [Finset.prod_inv_distrib, MercaQuarticEulerFactors.euler_polynomial,
    Finset.prod_inv_distrib, MercaRealEulerFactors.euler_polynomial]
  have hinv : character r hr (p : ZMod r) ^ 3 = (character r hr)⁻¹ (p : ZMod r) := by
    rw [← MulChar.pow_apply' _ (by decide : 3 ≠ 0), inverse_character]
  rw [hinv]
  simp only [mul_inv_rev]
  ring

/-- The actual quartic and maximal-real Dedekind zeta functions factor through the
normalized character and its inverse, with convergent Euler products. -/
theorem zeta_factorization {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta (MercaQuarticField.Field r hr) s =
    NumberField.dedekindZeta (RealField r hr) s *
      LFunction (character r hr) s * LFunction (character r hr)⁻¹ s := by
  have hK := QuadraticZetaFactorization.hasProd_rationalPrime_factors
    (MercaQuarticField.Field r hr) hs
  have hR := QuadraticZetaFactorization.hasProd_rationalPrime_factors (RealField r hr) hs
  have hχ := DirichletCharacter.LSeries_eulerProduct_hasProd (character r hr) hs
  have hχi := DirichletCharacter.LSeries_eulerProduct_hasProd (character r hr)⁻¹ hs
  rw [← LFunction_eq_LSeries (character r hr) hs] at hχ
  rw [← LFunction_eq_LSeries (character r hr)⁻¹ hs] at hχi
  apply hK.unique
  convert (hR.mul hχ).mul hχi using 1
  funext p
  letI : Fact (p : ℕ).Prime := ⟨p.2⟩
  exact prime_euler_factor r hr p s

/-- The actual class-group cardinalities agree under the proved square-root field
identification; this does not substitute a numerical class number for either field. -/
private lemma real_class_number :
    NumberField.classNumber (RealQuadratic r) = NumberField.classNumber (RealField r hr) := by
  exact Fintype.card_congr
    (ClassGroup.mulEquiv (((realEquiv r hr).restrictScalars ℤ).mapIntegralClosure.toRingEquiv)).toEquiv

private lemma real_torsion_order (hr5 : 5 < r) : torsionOrder (RealField r hr) = 2 := by
  obtain ⟨μ, hμ⟩ : ∃ μ : torsion (RealField r hr),
      orderOf μ = torsionOrder (RealField r hr) := IsCyclic.exists_ofOrder_eq_natCard
  rw [← IsPrimitiveRoot.iff_orderOf, ← IsPrimitiveRoot.coe_submonoidClass_iff,
    ← IsPrimitiveRoot.coe_units_iff] at hμ
  have hz := hμ.map_of_injective
    (FaithfulSMul.algebraMap_injective (𝓞 (RealField r hr)) (RealField r hr))
  have hd := dvd_torsionOrder_of_isPrimitiveRoot
    (hz.map_of_injective (FaithfulSMul.algebraMap_injective
      (RealField r hr) (MercaQuarticField.Field r hr)))
  rw [MercaQuarticField.torsion_order r hr hr5] at hd
  exact Nat.dvd_antisymm hd (even_iff_two_dvd.mp (even_torsionOrder (RealField r hr)))

private lemma regulator_ratio (hr5 : 5 < r) :
    regulator (MercaQuarticField.Field r hr) = 2 * regulator (RealField r hr) := by
  have hc : nrComplexPlaces (MercaQuarticField.Field r hr) = 2 := by
    have h := IsTotallyComplex.finrank (MercaQuarticField.Field r hr)
    rw [(field_structure r hr).1] at h
    omega
  have hrank : rank (MercaQuarticField.Field r hr) = 1 := by
    rw [rank, card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, hc]
  have h := IsCMField.regulator_div_regulator_eq_two_pow_mul_indexRealUnits_inv
    (MercaQuarticField.Field r hr)
  rw [hrank, MercaQuarticField.unit_index r hr hr5] at h
  norm_num at h
  exact (div_eq_iff (regulator_pos (RealField r hr)).ne').mp h

/-- Residue comparison from the actual class-number formula and the convergent
factorization; no sign choice for a quadratic Gauss sum is involved. -/
theorem residue_relation :
    (dedekindZeta_residue (MercaQuarticField.Field r hr) : ℂ) =
    (dedekindZeta_residue (RealField r hr) : ℂ) *
      LFunction (character r hr) 1 * LFunction (character r hr)⁻¹ 1 := by
  have hne : character r hr ≠ 1 := by
    intro h
    have := congrArg orderOf h
    rw [(kernel_structure r hr).1, orderOf_one] at this
    omega
  have hnei : (character r hr)⁻¹ ≠ 1 := by
    intro h
    apply hne
    rw [← inv_inv (character r hr), h, inv_one]
  have hL (χ : DirichletCharacter ℂ r) (hχ : χ ≠ 1) :
      Tendsto (fun s : ℝ => LFunction χ s) (𝓝[>] 1) (𝓝 (LFunction χ 1)) := by
    exact ((differentiable_LFunction hχ).continuous.tendsto 1).comp
      (by simpa using (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds)
  have hR := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT (RealField r hr)
  have hF := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT (MercaQuarticField.Field r hr)
  have hprod := (hR.mul (hL _ hne)).mul (hL _ hnei)
  apply tendsto_nhds_unique hF
  apply hprod.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [zeta_factorization r hr (by simpa using hs)]
  ring


private lemma residue_ratio (hr5 : 5 < r) :
    dedekindZeta_residue (MercaQuarticField.Field r hr) /
      dedekindZeta_residue (RealField r hr) =
    (2 * Real.pi ^ 2 / r) *
      ((NumberField.classNumber (MercaQuarticField.Field r hr) : ℝ) /
        NumberField.classNumber (RealField r hr)) := by
  have hc : nrComplexPlaces (MercaQuarticField.Field r hr) = 2 := by
    have h := IsTotallyComplex.finrank (MercaQuarticField.Field r hr)
    rw [(field_structure r hr).1] at h
    omega
  have hrp : nrRealPlaces (RealField r hr) = 2 := by
    have h := IsTotallyReal.finrank (RealField r hr)
    rw [(field_structure r hr).2.2.2] at h
    omega
  rw [dedekindZeta_residue_def, dedekindZeta_residue_def,
    IsTotallyComplex.nrRealPlaces_eq_zero, hc,
    IsTotallyReal.nrComplexPlaces_eq_zero, hrp,
    MercaQuarticField.torsion_order r hr hr5, real_torsion_order r hr hr5,
    MercaQuarticDiscriminant.discriminant r hr,
    (MercaQuadraticSubfield.real_discriminant r hr).2,
    regulator_ratio r hr hr5]
  simp only [pow_zero, pow_one, one_mul, Int.cast_pow, Int.cast_natCast, Nat.cast_ofNat]
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (Fact.out : r.Prime).pos
  rw [abs_of_nonneg (pow_nonneg hr0.le 3), abs_of_nonneg hr0.le]
  have hs : Real.sqrt ((r : ℝ) ^ 3) = r * Real.sqrt (r : ℝ) := by
    rw [show (r : ℝ) ^ 3 = r ^ 2 * r by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hr0.le]
  rw [hs]
  field_simp [(regulator_pos (RealField r hr)).ne',
    (Real.sqrt_pos_of_pos hr0).ne', hr0.ne',
    Nat.cast_ne_zero.mpr (classNumber_ne_zero (RealField r hr))]
  <;> ring

/-- The one-side product is derived from genuine Dedekind residues and CM constants. -/
theorem LFunction_one_mul_inverse (hr5 : 5 < r) :
    LFunction (character r hr) 1 * LFunction (character r hr)⁻¹ 1 =
    ((2 * Real.pi ^ 2 / r) *
      ((NumberField.classNumber (MercaQuarticField.Field r hr) : ℝ) /
        NumberField.classNumber (RealField r hr)) : ℂ) := by
  have hres := residue_relation r hr
  have hn : (dedekindZeta_residue (RealField r hr) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (dedekindZeta_residue_ne_zero _)
  have he : LFunction (character r hr) 1 * LFunction (character r hr)⁻¹ 1 =
      (dedekindZeta_residue (MercaQuarticField.Field r hr) : ℂ) /
        (dedekindZeta_residue (RealField r hr) : ℂ) := by
    apply (eq_div_iff hn).mpr
    rw [hres]
    ring
  rw [he, ← Complex.ofReal_div, residue_ratio r hr hr5]
  push_cast
  rfl


/-- The relative class number is the exact quotient of genuine ideal class numbers.
Its integrality is proved below, rather than imposed by natural division. -/
def relativeClassNumber : ℚ :=
  (NumberField.classNumber (MercaQuarticField.Field r hr) : ℚ) /
    NumberField.classNumber (RealQuadratic r)

/-- The classical relative class-number identity for the actual quartic CM field,
with the exact rational quotient and the literal normalized Bernoulli coordinates. -/
theorem relative_norm (hr5 : 5 < r) :
    (realCoordinate r hr : ℚ) ^ 2 + (imagCoordinate r hr : ℚ) ^ 2 =
      2 * relativeClassNumber r hr := by
  have hne : character r hr ≠ 1 := by
    intro h
    have ho := (kernel_structure r hr).1
    rw [h, orderOf_one] at ho
    norm_num at ho
  have hnei : (character r hr)⁻¹ ≠ 1 := by
    intro h
    apply hne
    rw [← inv_inv (character r hr), h, inv_one]
  obtain ⟨hB, _, _, _, _, _, _, _, hL⟩ := bernoulli_coordinates r hr hr5
  obtain ⟨_, _, _, _, _, hconj, _⟩ := conjugate_coordinates r hr hr5
  have hLi : LFunction (character r hr)⁻¹ 0 =
      -((realCoordinate r hr : ℂ) - (imagCoordinate r hr : ℂ) * Complex.I) := by
    rw [CatalanPrimeOddMoment.LFunction_zero_eq_neg_weighted_sum r _ hnei,
      ← D5.S3.ArithUnits.MercaPrimeCharacterMoment.character_moment_eq_zmod_sum,
      neg_div, ← MulChar.star_eq_inv, hconj]
    simp only [Int.cast_neg, neg_mul, sub_eq_add_neg]
  have hz : LFunction (character r hr) 0 * LFunction (character r hr)⁻¹ 0 =
      (realCoordinate r hr : ℂ) ^ 2 + (imagCoordinate r hr : ℂ) ^ 2 := by
    rw [hL, hB, hLi]
    linear_combination -(imagCoordinate r hr : ℂ) ^ 2 * Complex.I_sq
  have hFE := QuadraticLValueSquare.zero_mul_inverse r (by omega) (character r hr)
    (kernel_structure r hr).2.2.1 hne (kernel_structure r hr).2.2.2.1
  have hprod : LFunction (character r hr) 1 / (Real.pi : ℂ) *
      (LFunction (character r hr)⁻¹ 1 / (Real.pi : ℂ)) =
      (LFunction (character r hr) 1 * LFunction (character r hr)⁻¹ 1) /
        (Real.pi : ℂ) ^ 2 := by
    simp only [div_eq_mul_inv, inv_pow]
    ring
  rw [hz, hprod, LFunction_one_mul_inverse r hr hr5] at hFE
  push_cast at hFE
  have hc : (r : ℂ) *
      (2 * (Real.pi : ℂ) ^ 2 / r *
        ((NumberField.classNumber (MercaQuarticField.Field r hr) : ℂ) /
          NumberField.classNumber (RealField r hr)) / (Real.pi : ℂ) ^ 2) =
      2 * (NumberField.classNumber (MercaQuarticField.Field r hr) : ℂ) /
        NumberField.classNumber (RealField r hr) := by
    field_simp [Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero,
      Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  rw [hc, ← real_class_number r hr] at hFE
  dsimp [relativeClassNumber]
  apply (Rat.cast_injective (α := ℂ))
  push_cast
  simpa only [mul_div_assoc] using hFE

/-- Integrality of the genuine relative class number follows from the odd integer
coordinates and the proved norm identity. No finite conductor table is used. -/
theorem relative_class_number_integral (hr5 : 5 < r) :
    ∃ h : ℕ, (h : ℚ) = relativeClassNumber r hr := by
  obtain ⟨_, hk, ht, _, _, _, _, _, _⟩ := bernoulli_coordinates r hr hr5
  have he : _root_.Even (realCoordinate r hr ^ 2 + imagCoordinate r hr ^ 2) :=
    (hk.pow).add_odd (ht.pow)
  obtain ⟨z, hz⟩ := he
  have hz0 : 0 ≤ z := by
    nlinarith [sq_nonneg (realCoordinate r hr), sq_nonneg (imagCoordinate r hr)]
  have hnorm := relative_norm r hr hr5
  have hzQ : (realCoordinate r hr : ℚ) ^ 2 + (imagCoordinate r hr : ℚ) ^ 2 =
      (z : ℚ) + z := by exact_mod_cast hz
  have heq : (z : ℚ) = relativeClassNumber r hr := by linarith
  refine ⟨z.toNat, ?_⟩
  have hzcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
  exact (congrArg (fun n : ℤ => (n : ℚ)) hzcast).trans heq

end D5.S3.Analytic.Zeta.MercaRelativeClassNumber
