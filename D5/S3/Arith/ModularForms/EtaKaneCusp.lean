/- GID: D5/S3/Arith/ModularForms/EtaKaneCusp
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/EtaKaneCusp
   mirror-E: none(waiver:initial-component-review)
   anchors: [mathlib/module/Mathlib.NumberTheory.ModularForms.DedekindEta]
   utility: none
   digest: The exact third-cusp transform of Kane's unshifted Euler quotient. -/

import D5.S3.Arith.ModularForms.EtaCuspPhases

/-! The complex function H=E(q)^2/E(q^3) has third-cusp phase exp(-πi/9).
This analytic supplier does not assert any coefficient sign theorem. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped ComplexConjugate

namespace D5.S3.Arith.ModularForms.EtaKaneCusp

open EtaCuspTransform EtaThirdCusp EtaCuspPhases

/-- Kane's unshifted Euler quotient. -/
def kaneQuotient (q : ℂ) : ℂ := eulerProduct q ^ 2 / eulerProduct (q ^ 3)

private lemma quotient_partition (q : ℂ) :
    kaneQuotient q = partitionProduct (q ^ 3) / partitionProduct q ^ 2 := by
  simp [kaneQuotient, partitionProduct, div_eq_mul_inv, inv_pow, mul_comm]

private lemma partition_at_cusp_ne_zero (l : ℕ) (h : ℤ) (w : ℂ) (hw : 0 < w.re) :
    partitionProduct (exp (2 * Real.pi * I * h / l - w)) ≠ 0 := by
  have ht : 2 * Real.pi * I * (cuspPoint l h w hw : ℂ) =
      2 * Real.pi * I * h / l - w := by
    dsimp [cuspPoint]
    field_simp
    ring_nf
    simp [I_sq]
    <;> ring
  rw [← ht, partitionProduct_qParam]
  exact div_ne_zero (exp_ne_zero _) (ModularForm.eta_ne_zero (cuspPoint l h w hw).im_pos)

private lemma quotient_algebra (a s b x y : ℂ) (ha : a ≠ 0) (hs : s ≠ 0)
    (hb : b ≠ 0) (hx : x ≠ 0) :
    (s * b ^ 3 * y) / (a * s * b * x) ^ 2 =
      (a ^ 2)⁻¹ * s⁻¹ * b * (y / x ^ 2) := by
  field_simp

/-- Full right-half-plane transform at `1/3`. The reciprocal principal root
is written explicitly; its argument is always in `(-π/2,π/2)`. -/
theorem kane_one_third (w : ℂ) (hw : 0 < w.re) :
    kaneQuotient (exp (2 * Real.pi * I / 3 - w)) =
      exp (-Real.pi * I / 9) * (Complex.sqrt (3 * w / (2 * Real.pi)))⁻¹ *
      exp (Real.pi ^ 2 / (54 * w) - w / 24) *
      kaneQuotient (exp (-2 * Real.pi * I / 3 - 4 * Real.pi ^ 2 / (9 * w))) := by
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw
  let q := exp (2 * Real.pi * I / 3 - w)
  let u := exp (-2 * Real.pi * I / 3 - 4 * Real.pi ^ 2 / (9 * w))
  let s := Complex.sqrt (3 * w / (2 * Real.pi))
  let a := exp (Real.pi * I / 18)
  let b := exp (Real.pi ^ 2 / (54 * w) - w / 24)
  have hq : q ^ 3 = exp (-(3 * w)) := by
    dsimp [q]
    rw [← exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (3 : ℂ) * (2 * Real.pi * I / 3 - w) =
      -(3 * w) + 2 * Real.pi * I by ring, exp_add, exp_two_pi_mul_I, mul_one]
  have hu : u ^ 3 = exp (-4 * Real.pi ^ 2 / (3 * w)) := by
    dsimp [u]
    rw [← exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (3 : ℂ) * (-2 * Real.pi * I / 3 - 4 * Real.pi ^ 2 / (9 * w)) =
      -4 * Real.pi ^ 2 / (3 * w) + -(2 * Real.pi * I) by ring,
      exp_add, exp_neg, exp_two_pi_mul_I]
    simp
  have hp := partition_one_third w hw
  change partitionProduct q = a * s * b * partitionProduct u at hp
  have hz := partition_zero (3 * w) (by simpa using (mul_pos (by norm_num : (0 : ℝ) < 3) hw))
  have hex : exp (Real.pi ^ 2 / (18 * w) - 3 * w / 24) = b ^ 3 := by
    dsimp [b]
    rw [← exp_nat_mul]
    congr 1
    ring
  have hp3 : partitionProduct (q ^ 3) = s * b ^ 3 * partitionProduct (u ^ 3) := by
    rw [hq, hu]
    simpa only [show 6 * (3 * w) = 18 * w by ring, hex] using hz
  have hs : s ≠ 0 := by
    dsimp [s]
    simp [Complex.sqrt, hw0, Real.pi_ne_zero]
  have hx : partitionProduct u ≠ 0 := by
    have hq0 : partitionProduct q ≠ 0 := by
      simpa [q] using partition_at_cusp_ne_zero 3 1 w hw
    intro hu0
    apply hq0
    rw [hp, hu0, mul_zero]

  have ha : (a ^ 2)⁻¹ = exp (-Real.pi * I / 9) := by
    dsimp [a]
    rw [← exp_nat_mul, ← exp_neg]
    congr 1
    ring
  rw [quotient_partition, hp3, hp,
    quotient_algebra a s b (partitionProduct u) (partitionProduct (u ^ 3))
      (exp_ne_zero _) hs (exp_ne_zero _) hx, ha, ← quotient_partition]

private lemma kane_conj (q : ℂ) : conj (kaneQuotient q) = kaneQuotient (conj q) := by
  simp only [quotient_partition, map_div₀, map_pow, partition_conj]

/-- The conjugate third-cusp transform, representing the `2/3` cusp. -/
theorem kane_two_thirds (w : ℂ) (hw : 0 < w.re) :
    kaneQuotient (exp (4 * Real.pi * I / 3 - w)) =
      exp (Real.pi * I / 9) * (Complex.sqrt (3 * w / (2 * Real.pi)))⁻¹ *
      exp (Real.pi ^ 2 / (54 * w) - w / 24) *
      kaneQuotient (exp (2 * Real.pi * I / 3 - 4 * Real.pi ^ 2 / (9 * w))) := by
  have hperiod : exp (4 * Real.pi * I / 3 - w) = exp (-2 * Real.pi * I / 3 - w) := by
    rw [show 4 * (Real.pi : ℂ) * I / 3 - w =
      (-2 * Real.pi * I / 3 - w) + 2 * Real.pi * I by ring,
      exp_add, exp_two_pi_mul_I, mul_one]
  rw [hperiod]
  have ht := congrArg conj (kane_one_third (conj w) (by simpa using hw))
  have hr : 0 < (3 * conj w / (2 * Real.pi)).re := by
    simp [Complex.div_re, Complex.mul_re]
    positivity
  simp only [map_mul, map_sub, map_div₀, map_neg, map_ofNat, map_inv₀, map_pow,
    conj_ofReal, conj_I, conj_conj, ← exp_conj, kane_conj,
    sqrt_conj_of_re_pos hr] at ht
  convert ht using 1 <;> congr 2 <;> ring

end D5.S3.Arith.ModularForms.EtaKaneCusp

#print axioms D5.S3.Arith.ModularForms.EtaKaneCusp.kane_one_third

#print axioms D5.S3.Arith.ModularForms.EtaKaneCusp.kane_two_thirds
