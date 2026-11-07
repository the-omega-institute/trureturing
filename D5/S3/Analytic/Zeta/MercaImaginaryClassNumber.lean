/- GID: D5/S3/Analytic/Zeta/MercaImaginaryClassNumber
   generality: G
   mirror-B: D5/B/S3/Analytic/Zeta/MercaImaginaryClassNumber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The signed L-zero class-number formula for the actual imaginary Merca quadratic field. -/

import D5.S3.Arith.QuadraticFields.MercaImaginaryEulerFactors
import D5.S3.Arith.CharacterSums.MercaImaginaryGauss
import D5.S3.Arith.CharacterSums.MercaQuadraticQuarter
import D5.S3.Analytic.Zeta.QuadraticZetaFactorization

/-!
The actual maximal-order Euler factors give the Dedekind zeta factorization.
The analytic class-number residue and the positive Gauss sign then give the
signed finite class-number formula, with the classical attribution retained.
-/
set_option autoImplicit false
noncomputable section
open scoped NumberField BigOperators Topology

namespace D5.S3.Analytic.Zeta.MercaImaginaryClassNumber
open NumberField DirichletCharacter Filter
open D5.S3.Arith.QuadraticFields MercaImaginaryQuadratic
open MercaImaginaryCharacter

variable (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5)
include hr

private lemma prime_euler_factor (p : ℕ) [Fact p.Prime] (s : ℂ) :
    (∏ P : Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Field r)),
      (1 - (Ideal.absNorm P.1 : ℂ) ^ (-s))⁻¹) =
      (1 - (p : ℂ) ^ (-s))⁻¹ *
        (1 - character r (p : ZMod (4 * r)) * (p : ℂ) ^ (-s))⁻¹ := by
  classical
  have hnorm (P : Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Field r))) :
      (Ideal.absNorm P.1 : ℂ) ^ (-s) =
        ((p : ℂ) ^ (-s)) ^ Ideal.inertiaDeg P.1 ℤ := by
    rw [← Ideal.pow_inertiaDeg p P.1, Nat.cast_pow,
      ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]
  simp_rw [hnorm]
  rw [Finset.prod_inv_distrib, MercaImaginaryEulerFactors.euler_polynomial r hr,
    mul_inv_rev, mul_comm]

/-- Convergent Euler products identify the actual quadratic Dedekind zeta function. -/
theorem zeta_factorization {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta (Field r) s =
      riemannZeta s * LFunction (character r) s := by
  have hK := QuadraticZetaFactorization.hasProd_rationalPrime_factors (Field r) hs
  have hχ := (riemannZeta_eulerProduct_hasProd hs).mul
    (DirichletCharacter.LSeries_eulerProduct_hasProd (character r) hs)
  rw [← DirichletCharacter.LFunction_eq_LSeries (character r) hs] at hχ
  apply hK.unique
  convert hχ using 1
  funext p
  letI : Fact (p : ℕ).Prime := ⟨p.2⟩
  exact prime_euler_factor r hr p s

/-- The positive value at one is the genuine ideal class number times pi over sqrt(4r). -/
theorem LFunction_one :
    LFunction (character r) 1 =
      (Real.pi * (NumberField.classNumber (Field r) : ℝ) /
        (2 * Real.sqrt (r : ℝ)) : ℂ) := by
  have ht : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝[≠] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · exact (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      intro heq
      change (s : ℂ) = 1 at heq
      exact (ne_of_gt hs) (by exact_mod_cast heq)
  have hζ := riemannZeta_residue_one.comp ht
  have hne := (character_properties r hr).2.2.2
  have hL : Tendsto (fun s : ℝ => LFunction (character r) s)
      (𝓝[>] 1) (𝓝 (LFunction (character r) 1)) := by
    exact ((differentiable_LFunction hne).continuous.tendsto 1).comp
      (by simpa using (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds)
  have hprod : Tendsto (fun s : ℝ =>
      ((s : ℂ) - 1) * NumberField.dedekindZeta (Field r) s)
      (𝓝[>] 1) (𝓝 (LFunction (character r) 1)) := by
    have h := hζ.mul hL
    simp only [Function.comp_def, one_mul] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [zeta_factorization r hr (by simpa using hs)]
    ring
  have hres := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT (Field r)
  rw [(field_invariants r hr).2.2.2.2.2] at hres
  simpa only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_ofNat] using tendsto_nhds_unique hprod hres

/-- The signed bridge uses the positive Gauss evaluation; the squared functional
identity alone would not prove this statement. -/
theorem LFunction_zero :
    LFunction (character r) 0 = (NumberField.classNumber (Field r) : ℂ) := by
  obtain ⟨hprim, hquad, hodd, _⟩ := character_properties r hr
  have hself := hquad.inv
  have hfe := hprim.completedLFunction_one_sub (1 : ℂ)
  rw [sub_self, show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num, hself] at hfe
  have hN : 4 * r ≠ 1 := by omega
  have hzero : LFunction (character r) 0 = completedLFunction (character r) 0 := by
    rw [LFunction_eq_completed_div_gammaFactor _ _ (Or.inr hN),
      hodd.gammaFactor_def, zero_add, Complex.Gammaℝ_one, div_one]
  have hone : completedLFunction (character r) 1 =
      LFunction (character r) 1 / (Real.pi : ℂ) := by
    rw [LFunction_eq_completed_div_gammaFactor _ 1 (Or.inl one_ne_zero),
      hodd.gammaFactor_def, show (1 : ℂ) + 1 = 2 by norm_num]
    have hg : Complex.Gammaℝ 2 = (Real.pi : ℂ)⁻¹ := by
      norm_num [Complex.Gammaℝ_def, Complex.cpow_neg_one]
    rw [hg]
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  rw [← hzero, hone, rootNumber, if_neg hodd.not_even, pow_one,
    D5.S3.Arith.CharacterSums.MercaImaginaryGauss.gauss_sum r hr,
    LFunction_one r hr] at hfe
  have hq : (4 * (r : ℂ)) ^ (1 / 2 : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl
      (mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero)))
  have hs : (Real.sqrt r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Fact.out : r.Prime).pos)).ne'
  push_cast at hfe
  have hc : (4 * (r : ℂ)) ^ (1 / 2 : ℂ) *
      (2 * Complex.I * (Real.sqrt r : ℂ) / Complex.I /
        (4 * (r : ℂ)) ^ (1 / 2 : ℂ)) *
      ((Real.pi : ℂ) * (NumberField.classNumber (Field r) : ℂ) /
        (2 * (Real.sqrt r : ℂ)) / (Real.pi : ℂ)) =
      (NumberField.classNumber (Field r) : ℂ) := by
    field_simp [hq, hs, Complex.I_ne_zero, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  exact hfe.trans hc

/-- The actual ideal class number equals twice the literal quadratic quarter sum.
In particular its integer half is exact, with no truncation premise. -/
theorem class_number_quarter :
    (NumberField.classNumber (Field r) : ℤ) =
      2 * D5.S3.Arith.CharacterSums.MercaQuadraticQuarter.quarterSum r ∧
    (NumberField.classNumber (Field r) : ℤ) / 2 =
      D5.S3.Arith.CharacterSums.MercaQuadraticQuarter.quarterSum r := by
  have h := (LFunction_zero r hr).symm.trans
    (D5.S3.Arith.CharacterSums.MercaQuadraticQuarter.LFunction_zero_quarter r hr)
  have hi : (NumberField.classNumber (Field r) : ℤ) =
      2 * D5.S3.Arith.CharacterSums.MercaQuadraticQuarter.quarterSum r := by
    exact_mod_cast h
  exact ⟨hi, by omega⟩

end D5.S3.Analytic.Zeta.MercaImaginaryClassNumber
