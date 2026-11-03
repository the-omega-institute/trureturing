import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicKernel
import Mathlib.RingTheory.PowerSeries.Binomial

/-
UNCOMPILED source. The imported OriginalGaussianCubicKernel must be the
unchanged 29307-byte source with SHA256
4503cf38c9a60aebea20ad87716d85f2f2b80c866bd1e3217a568f5abc4080ee.
No elaboration, kernel checking, or official acceptance is asserted here.

The outer variable is x, the inner Laurent variable is a. All differentiation
below is coefficientwise in x. Residue is used as an additive map, and as a
module map for series whose a-coefficients are constants. It is never used as
a ring homomorphism on Laurent series. No change a=x/u is made.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicResidues

open D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open OriginalGaussianCubicKernel
open private neckVariable aSeries bSeries formalScalarC omega_coefficient
  omega_residue first_moment_residue first_moment_residue_zero
  from D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicKernel

private abbrev L := LaurentSeries ℂ
private abbrev A := AnnulusSeries
private abbrev dl := LaurentSeries.derivative ℂ (V := ℂ)

private lemma dl_coeff (f : L) (k : ℤ) :
    (dl f).coeff k = ((k + 1 : ℤ) : ℂ) * f.coeff (k + 1) := by
  simp [dl, LaurentSeries.derivative, LaurentSeries.hasseDeriv_coeff,
    Ring.choose_one_right, zsmul_eq_mul]

private lemma dl_coe (f : PowerSeries ℂ) :
    dl (f : L) = (PowerSeries.derivative f : L) := by
  ext k
  rw [dl_coeff]
  cases k with
  | ofNat n =>
      rw [show (Int.ofNat n + 1 : ℤ) = ((n + 1 : ℕ) : ℤ) by omega,
        LaurentSeries.coeff_coe_powerSeries,
        LaurentSeries.coeff_coe_powerSeries, PowerSeries.coeff_derivative]
      push_cast
      ring
  | negSucc n =>
      cases n with
      | zero => simp [LaurentSeries.coeff_coe]
      | succ n =>
          have hn : (Int.negSucc (n + 1) + 1 : ℤ) < 0 := by omega
          simp [LaurentSeries.coeff_coe, hn]

private lemma dl_shift (m : ℤ) (f : L) :
    dl (HahnSeries.single m 1 * f) =
      HahnSeries.single m 1 * dl f +
        HahnSeries.single (m - 1) (m : ℂ) * f := by
  ext k
  simp only [dl_coeff, HahnSeries.coeff_add, HahnSeries.coeff_single_mul, one_mul]
  rw [show k + 1 - m = k - m + 1 by omega,
    show k - (m - 1) = k - m + 1 by omega]
  push_cast
  ring

private lemma dl_shift_coe (m : ℤ) (f : PowerSeries ℂ) :
    dl (HahnSeries.single m 1 * (f : L)) =
      HahnSeries.single m 1 * (PowerSeries.derivative f : L) +
        HahnSeries.single (m - 1) (m : ℂ) * (f : L) := by
  rw [dl_shift, dl_coe]

/- Prove Leibniz from the finite-lower-bound presentation of each Laurent
series. This avoids assuming an unavailable Laurent derivative API. -/
private lemma dl_mul (f g : L) : dl (f * g) = dl f * g + f * dl g := by
  have rep (v : L) : ∃ m : ℤ, ∃ q : PowerSeries ℂ,
      v = HahnSeries.single m 1 * (q : L) :=
    ⟨v.order, v.powerSeriesPart, v.single_order_mul_powerSeriesPart.symm⟩
  obtain ⟨m, p, rfl⟩ := rep f
  obtain ⟨n, q, rfl⟩ := rep g
  have hprod : (HahnSeries.single m 1 * (p : L)) *
      (HahnSeries.single n 1 * (q : L)) =
        HahnSeries.single (m + n) 1 * ((p * q : PowerSeries ℂ) : L) := by
    rw [LaurentSeries.coe_mul]
    calc
      _ = (HahnSeries.single m 1 * HahnSeries.single n 1) *
          ((p : L) * (q : L)) := by ring
      _ = _ := by rw [HahnSeries.single_mul_single, one_mul]
  have hm : (HahnSeries.single (m + n - 1) ((m + n : ℤ) : ℂ) : L) =
      HahnSeries.single (m - 1) (m : ℂ) * HahnSeries.single n 1 +
        HahnSeries.single m 1 * HahnSeries.single (n - 1) (n : ℂ) := by
    rw [HahnSeries.single_mul_single, HahnSeries.single_mul_single]
    have hmn : m - 1 + n = m + n - 1 := by omega
    have hnm : m + (n - 1) = m + n - 1 := by omega
    simp only [hmn, hnm, mul_one, one_mul, Int.cast_add, HahnSeries.single_add]
  rw [hprod, dl_shift_coe, dl_shift_coe, dl_shift_coe,
    PowerSeries.derivative.leibniz]
  simp only [smul_eq_mul, LaurentSeries.coe_add, LaurentSeries.coe_mul]
  rw [hm]
  have hmn : (HahnSeries.single (m + n) 1 : L) =
      HahnSeries.single m 1 * HahnSeries.single n 1 := by
    rw [HahnSeries.single_mul_single, one_mul]
  rw [hmn]
  ring

private def da (f : A) : A := PowerSeries.mk (fun n => dl (PowerSeries.coeff n f))

private lemma da_coeff (f : A) (n : ℕ) : PowerSeries.coeff n (da f) =
    dl (PowerSeries.coeff n f) := by simp [da]

private lemma da_add (f g : A) : da (f + g) = da f + da g := by
  ext n
  simp [da, map_add]

private lemma da_neg (f : A) : da (-f) = -da f := by
  ext n
  simp [da, map_neg]

private lemma da_sub (f g : A) : da (f - g) = da f - da g := by
  simpa only [sub_eq_add_neg, da_add, da_neg]

private lemma da_mul (f g : A) : da (f * g) = da f * g + f * da g := by
  ext n
  simp only [da_coeff, PowerSeries.coeff_mul, map_add,
    map_sum, dl_mul, Finset.sum_add_distrib]

private lemma da_C (c : L) : da (PowerSeries.C c) = PowerSeries.C (dl c) := by
  ext n
  by_cases hn : n = 0 <;> simp [da, PowerSeries.coeff_C, hn]

private lemma dl_const (c : ℂ) : dl (HahnSeries.C c : L) = 0 := by
  ext k
  simp [dl, LaurentSeries.derivative, HahnSeries.C_apply,
    LaurentSeries.hasseDeriv_single]

private lemma da_one : da (1 : A) = 0 := by
  change da (PowerSeries.C (HahnSeries.C (1 : ℂ))) = 0
  rw [da_C, dl_const, map_zero]

private lemma da_X : da (PowerSeries.X : A) = 0 := by
  ext n
  by_cases hn : n = 1 <;> simp [da, PowerSeries.coeff_X, hn]

private def lift (f : PowerSeries ℂ) : A :=
  PowerSeries.map (HahnSeries.C : ℂ →+* L) f

private lemma lift_mul (f g : PowerSeries ℂ) : lift (f * g) = lift f * lift g := by
  exact map_mul (PowerSeries.map (HahnSeries.C : ℂ →+* L)) f g

private lemma lift_one : lift (1 : PowerSeries ℂ) = 1 := by simp [lift]

private lemma da_lift (f : PowerSeries ℂ) : da (lift f) = 0 := by
  ext n
  simp [da, lift, dl_const]

private lemma da_a : da aSeries = 1 := by
  rw [aSeries, da_C]
  congr 1
  simp [neckVariable, dl, LaurentSeries.derivative,
    LaurentSeries.hasseDeriv_single, HahnSeries.single_zero_one]

private lemma da_b (b : ℂ) : da (bSeries b) = 0 := by
  simp [bSeries, da_C, dl_const]

private lemma da_inv (f : A) (hf : PowerSeries.constantCoeff f ≠ 0) :
    da f⁻¹ = -(f⁻¹ ^ 2) * da f := by
  have hi := PowerSeries.inv_mul_cancel f hf
  have hc := PowerSeries.mul_inv_cancel f hf
  calc
    da f⁻¹ = (f⁻¹ * f) * da f⁻¹ := by rw [hi, one_mul]
    _ = f⁻¹ * (da (f * f⁻¹) - da f * f⁻¹) := by rw [da_mul]; ring
    _ = -(f⁻¹ ^ 2) * da f := by rw [hc, da_one]; ring

private lemma cancel_unit (r s u v : A) (hrs : r * s = 1)
    (h : r * u = r * v) : u = v := by
  calc
    u = s * (r * u) := by rw [← mul_assoc, mul_comm s r, hrs, one_mul]
    _ = s * (r * v) := by rw [h]
    _ = v := by rw [← mul_assoc, mul_comm s r, hrs, one_mul]

private lemma square_inverse (r s : A) (h : r * s = 1) :
    r ^ 2 * s = r ∧ r ^ 2 * s ^ 2 = 1 := by
  constructor
  · calc r ^ 2 * s = r * (r * s) := by ring
         _ = r := by rw [h, mul_one]
  · rw [← mul_pow, h, one_pow]

private def ai : L := HahnSeries.single (-1) 1
private def aiSeries : A := PowerSeries.C ai

private lemma a_ai : aSeries * aiSeries = 1 := by
  rw [aSeries, aiSeries, ← map_mul]
  simp [neckVariable, ai, HahnSeries.single_mul_single]

private lemma da_ai : da aiSeries = -aiSeries ^ 2 := by
  rw [aiSeries, da_C]
  simp [ai, dl, LaurentSeries.derivative, LaurentSeries.hasseDeriv_single,
    ← map_pow, HahnSeries.single_pow, HahnSeries.single_neg]

private def half : A := lift (PowerSeries.C (1 / 2 : ℂ))

private lemma two_half : (2 : A) * half = 1 := by
  change (2 : A) * PowerSeries.C (HahnSeries.C (1 / 2 : ℂ)) = 1
  have h2 : (2 : A) = PowerSeries.C (HahnSeries.C (2 : ℂ)) := by simp
  rw [h2, ← map_mul, ← map_mul]
  norm_num

private def bin (r : ℂ) : PowerSeries ℂ := PowerSeries.binomialSeries ℂ r

private lemma bin_coeff (r : ℂ) (n : ℕ) :
    PowerSeries.coeff n (bin r) = Ring.choose r n := by simp [bin, smul_eq_mul]

private lemma bin_half_inverse : bin (1 / 2) * bin (-1 / 2) = 1 := by
  rw [bin, bin, ← PowerSeries.binomialSeries_add]
  norm_num

private lemma bin_half_square : bin (1 / 2) ^ 2 = 1 + PowerSeries.X := by
  rw [pow_two, bin, ← PowerSeries.binomialSeries_add]
  norm_num

private lemma halfSeries_bin : halfSeries = bin (-1 / 2) := by
  ext n
  simp [halfSeries, bin_coeff, halfBinomial_choose]

private def R : L := (bin (1 / 2) : L)

private lemma R_H : R * (halfSeries : L) = 1 := by
  rw [R, halfSeries_bin, ← LaurentSeries.coe_mul, bin_half_inverse,
    LaurentSeries.coe_one]

private lemma R_square : R ^ 2 = 1 + neckVariable := by
  rw [R, ← LaurentSeries.coe_pow, bin_half_square, LaurentSeries.coe_add,
    LaurentSeries.coe_one, LaurentSeries.coe_X]

private def outerBin (r : ℂ) : A := PowerSeries.rescale ai (lift (bin r))

private lemma outer_inverse : outerBin (1 / 2) * outerBin (-1 / 2) = 1 := by
  rw [outerBin, outerBin, ← map_mul, ← lift_mul, bin_half_inverse, lift_one, map_one]

private lemma outer_square : outerBin (1 / 2) ^ 2 =
    1 + aiSeries * PowerSeries.X := by
  rw [outerBin, ← map_pow, ← map_pow (PowerSeries.map (HahnSeries.C : ℂ →+* L)),
    bin_half_square]
  simp [lift, aiSeries, PowerSeries.rescale_X, PowerSeries.map_X]

private def w : A := PowerSeries.C (neckVariable * R) * outerBin (1 / 2)

private lemma omega_factor : formalOmega =
    PowerSeries.C (ai * (halfSeries : L)) * outerBin (-1 / 2) := by
  ext n
  simp only [formalOmega, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
    outerBin, PowerSeries.coeff_rescale, lift, PowerSeries.coeff_map, bin_coeff,
    ← halfBinomial_choose]
  have hp : ai ^ n = (HahnSeries.single (-(n : ℤ)) 1 : L) := by
    simp [ai, HahnSeries.single_pow, nsmul_eq_mul]
  rw [hp, omegaCoefficient, HahnSeries.C_apply]
  calc
    _ = ((HahnSeries.single (-1) 1 * HahnSeries.single (-(n : ℤ)) 1) *
        HahnSeries.single 0 (halfBinomial n)) * (halfSeries : L) := by
      simp [HahnSeries.single_mul_single, show (-1 : ℤ) + -(n : ℤ) = -n - 1 by omega]
    _ = _ := by dsimp [ai]; ring

private lemma w_omega : w * formalOmega = 1 := by
  have ha : neckVariable * ai = (1 : L) := by
    simp [neckVariable, ai, HahnSeries.single_mul_single]
  rw [w, omega_factor]
  calc
    _ = PowerSeries.C ((neckVariable * ai) * (R * (halfSeries : L))) *
        (outerBin (1 / 2) * outerBin (-1 / 2)) := by
          simp only [map_mul]
          ring
    _ = 1 := by rw [ha, R_H, outer_inverse]; simp

private def p : A := aSeries * (aSeries + 1) * (aSeries + PowerSeries.X)

private def pp : A := 3 * aSeries ^ 2 +
  2 * (1 + PowerSeries.X) * aSeries + PowerSeries.X

private lemma w_square : w ^ 2 = p := by
  have hs : (PowerSeries.C (neckVariable * R) : A) ^ 2 =
      aSeries ^ 2 * (1 + aSeries) := by
    rw [← map_pow, mul_pow, R_square]
    simp only [map_mul, map_pow, map_add, map_one, aSeries]
  rw [w, mul_pow, hs, outer_square]
  have hi := (square_inverse aSeries aiSeries a_ai).1
  dsimp only [p]
  linear_combination (1 + aSeries) * PowerSeries.X * hi

private lemma da_p : da p = pp := by
  dsimp only [p, pp]
  simp only [da_mul, da_add, da_a, da_one, da_X]
  ring

private lemma w_p_omega : w = p * formalOmega := by
  calc
    w = w * (w * formalOmega) := by rw [w_omega, mul_one]
    _ = w ^ 2 * formalOmega := by ring
    _ = p * formalOmega := by rw [w_square]

private lemma two_dw : 2 * da w = pp * formalOmega := by
  have hd := congrArg da w_square
  rw [pow_two, da_mul, da_p] at hd
  calc
    2 * da w = (2 * w * da w) * formalOmega := by
      calc
        _ = (2 * da w) * (w * formalOmega) := by rw [w_omega, mul_one]
        _ = _ := by ring
    _ = pp * formalOmega := by
      congr 1
      linear_combination hd

private def T (b : ℂ) : A := aSeries - bSeries b
private def D (b : ℂ) : A := aSeries * bSeries b - PowerSeries.X

private def N (b : ℂ) : A :=
  aSeries * bSeries b * (aSeries + bSeries b) +
    2 * (1 + PowerSeries.X) * aSeries * bSeries b +
      PowerSeries.X * (aSeries + bSeries b)

private lemma T_constant (b : ℂ) : PowerSeries.constantCoeff (T b) ≠ 0 := by
  intro h
  have hh := congrArg (fun f : L => f.coeff 1) h
  simpa [T, aSeries, bSeries, neckVariable, HahnSeries.C_apply] using hh

private lemma D_constant (b : ℂ) (hb : b ≠ 0) :
    PowerSeries.constantCoeff (D b) ≠ 0 := by
  intro h
  have hh := congrArg (fun f : L => f.coeff 1) h
  apply hb
  simpa [D, aSeries, bSeries, neckVariable, HahnSeries.C_apply,
    HahnSeries.coeff_mul_single_zero] using hh

private lemma twice_square_constant (f : A)
    (hf : PowerSeries.constantCoeff f ≠ 0) :
    PowerSeries.constantCoeff (2 * f ^ 2) ≠ 0 := by
  simpa using
    mul_ne_zero (show (2 : L) ≠ 0 by norm_num) (pow_ne_zero 2 hf)

private lemma da_T (b : ℂ) : da (T b) = 1 := by
  simp only [T, da_sub, da_a, da_b, sub_zero]

private lemma da_D (b : ℂ) : da (D b) = bSeries b := by
  simp only [D, da_sub, da_mul, da_a, da_b, da_X, one_mul, mul_zero,
    add_zero, sub_zero]

private lemma TT_polynomial (b : ℂ) :
    aSeries * T b ^ 2 - pp * T b + 2 * p = N b := by
  dsimp only [T, pp, p, N]
  ring

private lemma UT_polynomial (b : ℂ) :
    aSeries * D b ^ 2 - aSeries * D b * pp +
      2 * (2 * aSeries * bSeries b - PowerSeries.X) * p = aSeries ^ 2 * N b := by
  dsimp only [D, pp, p, N]
  ring

private def primitiveTT (b : ℂ) : A := w * (T b)⁻¹
private def primitiveUT (b : ℂ) : A :=
  -PowerSeries.X * w * aiSeries * (D b)⁻¹

private lemma primitiveTT_cleared (b : ℂ) :
    2 * T b ^ 2 * da (primitiveTT b) = (pp * T b - 2 * p) * formalOmega := by
  have hc := PowerSeries.mul_inv_cancel (T b) (T_constant b)
  obtain ⟨h1, h2⟩ := square_inverse (T b) (T b)⁻¹ hc
  calc
    _ = (2 * da w) * (T b ^ 2 * (T b)⁻¹) -
        2 * w * (T b ^ 2 * ((T b)⁻¹) ^ 2) := by
          rw [primitiveTT, da_mul, da_inv _ (T_constant b), da_T]
          ring
    _ = (2 * da w) * T b - 2 * w := by rw [h1, h2]; ring
    _ = _ := by rw [two_dw, w_p_omega]; ring

private lemma TT_polar (b : ℂ) :
    formalOmega * (N b * (2 * T b ^ 2)⁻¹) =
      half * aSeries * formalOmega - da (primitiveTT b) := by
  have hc := PowerSeries.mul_inv_cancel (2 * T b ^ 2)
    (twice_square_constant (T b) (T_constant b))
  apply cancel_unit (2 * T b ^ 2) (2 * T b ^ 2)⁻¹ _ _ hc
  calc
    (2 * T b ^ 2) * (formalOmega * (N b * (2 * T b ^ 2)⁻¹)) =
        N b * formalOmega := by
          calc
            _ = N b * formalOmega * ((2 * T b ^ 2) * (2 * T b ^ 2)⁻¹) := by ring
            _ = _ := by rw [hc, mul_one]
    _ = (aSeries * T b ^ 2 - pp * T b + 2 * p) * formalOmega := by
      rw [TT_polynomial]
    _ = (2 * half) * aSeries * T b ^ 2 * formalOmega -
        (2 * T b ^ 2) * da (primitiveTT b) := by
          rw [two_half, primitiveTT_cleared]
          ring
    _ = _ := by ring

private lemma TT_decomposition (b hb : ℂ) :
    cubicTTSeries b hb = formalExternalOmega b hb *
      ((half * aSeries + formalScalarC) * formalOmega - da (primitiveTT b)) := by
  change formalOmega * formalExternalOmega b hb *
      (N b * (2 * T b ^ 2)⁻¹ + formalScalarC) = _
  linear_combination formalExternalOmega b hb * TT_polar b

private lemma primitiveUT_double_cleared (b : ℂ) (hb : b ≠ 0) :
    2 * aSeries ^ 2 * D b ^ 2 * da (primitiveUT b) =
      PowerSeries.X * formalOmega * (aSeries ^ 2 * N b - aSeries * D b ^ 2) := by
  have hc := PowerSeries.mul_inv_cancel (D b) (D_constant b hb)
  obtain ⟨hd1, hd2⟩ := square_inverse (D b) (D b)⁻¹ hc
  obtain ⟨ha1, ha2⟩ := square_inverse aSeries aiSeries a_ai
  calc
    _ = -PowerSeries.X * (2 * da w) *
          (aSeries ^ 2 * aiSeries) * (D b ^ 2 * (D b)⁻¹) +
        2 * PowerSeries.X * w * (aSeries ^ 2 * aiSeries ^ 2) *
          (D b ^ 2 * (D b)⁻¹) +
        2 * PowerSeries.X * w * (aSeries ^ 2 * aiSeries) *
          (D b ^ 2 * ((D b)⁻¹) ^ 2) * bSeries b := by
            dsimp only [primitiveUT]
            simp only [da_mul, da_neg, da_X, da_ai,
              da_inv (D b) (D_constant b hb), da_D]
            ring
    _ = PowerSeries.X * formalOmega *
        (-aSeries * D b * pp + 2 * p * (D b + aSeries * bSeries b)) := by
          rw [ha1, ha2, hd1, hd2, two_dw, w_p_omega]
          ring
    _ = PowerSeries.X * formalOmega *
        (-aSeries * D b * pp + 2 * (2 * aSeries * bSeries b - PowerSeries.X) * p) := by
          dsimp only [D]
          ring
    _ = _ := by
      congr 1
      linear_combination UT_polynomial b

private lemma primitiveUT_cleared (b : ℂ) (hb : b ≠ 0) :
    2 * D b ^ 2 * da (primitiveUT b) =
      PowerSeries.X * N b * formalOmega -
        PowerSeries.X * D b ^ 2 * aiSeries * formalOmega := by
  have ha2 := (square_inverse aSeries aiSeries a_ai).2
  have ha1 := (square_inverse aSeries aiSeries a_ai).1
  apply cancel_unit (aSeries ^ 2) (aiSeries ^ 2) _ _ ha2
  calc
    _ = 2 * aSeries ^ 2 * D b ^ 2 * da (primitiveUT b) := by ring
    _ = PowerSeries.X * formalOmega *
        (aSeries ^ 2 * N b - aSeries * D b ^ 2) :=
          primitiveUT_double_cleared b hb
    _ = PowerSeries.X * formalOmega *
        (aSeries ^ 2 * N b - (aSeries ^ 2 * aiSeries) * D b ^ 2) := by rw [ha1]
    _ = _ := by ring

private lemma UT_polar (b : ℂ) (hb : b ≠ 0) :
    formalOmega * (PowerSeries.X * N b * (2 * D b ^ 2)⁻¹) =
      half * PowerSeries.X * aiSeries * formalOmega + da (primitiveUT b) := by
  have hc := PowerSeries.mul_inv_cancel (2 * D b ^ 2)
    (twice_square_constant (D b) (D_constant b hb))
  apply cancel_unit (2 * D b ^ 2) (2 * D b ^ 2)⁻¹ _ _ hc
  calc
    _ = PowerSeries.X * N b * formalOmega := by
      calc
        _ = PowerSeries.X * N b * formalOmega *
            ((2 * D b ^ 2) * (2 * D b ^ 2)⁻¹) := by ring
        _ = _ := by rw [hc, mul_one]
    _ = (2 * half) * PowerSeries.X * D b ^ 2 * aiSeries * formalOmega +
        (2 * D b ^ 2) * da (primitiveUT b) := by
          rw [two_half, primitiveUT_cleared b hb]
          ring
    _ = _ := by ring

private lemma UT_decomposition (b hb : ℂ) (hb0 : b ≠ 0) :
    cubicUTSeries b hb = formalExternalOmega b hb *
      (-((half * PowerSeries.X * aiSeries + formalScalarC) * formalOmega) -
        da (primitiveUT b)) := by
  have hN : aSeries * bSeries b * (aSeries + bSeries b + 2) +
      PowerSeries.X * (aSeries + bSeries b + 2 * aSeries * bSeries b) = N b := by
    dsimp only [N]
    ring
  change -(formalOmega * formalExternalOmega b hb) *
      (PowerSeries.X *
        (aSeries * bSeries b * (aSeries + bSeries b + 2) +
          PowerSeries.X * (aSeries + bSeries b + 2 * aSeries * bSeries b)) *
            (2 * D b ^ 2)⁻¹ + formalScalarC) = _
  rw [hN]
  linear_combination -(formalExternalOmega b hb) * UT_polar b hb0

private def res (f : A) : PowerSeries ℂ :=
  PowerSeries.mk (fun n => (PowerSeries.coeff n f).coeff (-1))

private lemma res_add (f g : A) : res (f + g) = res f + res g := by
  ext n
  simp [res, HahnSeries.coeff_add]

private lemma res_neg (f : A) : res (-f) = -res f := by
  ext n
  simp [res, HahnSeries.coeff_neg]

private lemma res_sub (f g : A) : res (f - g) = res f - res g := by
  simpa only [sub_eq_add_neg, res_add, res_neg]

private lemma res_da (f : A) : res (da f) = 0 := by
  ext n
  simp [res, da, dl_coeff]

/- This is the only multiplicative compatibility used for residue. The
left factor has constant a-coefficients; the x-convolution is finite. -/
private lemma res_lift_mul (f : PowerSeries ℂ) (g : A) :
    res (lift f * g) = f * res g := by
  ext n
  simp only [res, PowerSeries.coeff_mk, PowerSeries.coeff_mul, lift,
    PowerSeries.coeff_map, HahnSeries.coeff_sum, HahnSeries.C_apply,
    HahnSeries.coeff_single_zero_mul]

private def external (b hb : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun n => hb * halfBinomial n / b ^ (n + 1))

private lemma external_lift (b hb : ℂ) : formalExternalOmega b hb = lift (external b hb) := by
  ext n
  simp [formalExternalOmega, external, lift]

private lemma res_omega : res formalOmega = periodSeries := by
  ext n
  simp only [res, formalOmega, periodSeries, PowerSeries.coeff_mk, omega_residue]

private lemma res_a_omega : res (aSeries * formalOmega) = momentSeries := by
  ext n
  simp only [res, aSeries, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
    formalOmega, momentSeries]
  simp [neckVariable, HahnSeries.coeff_single_mul]

private lemma res_x_ai_omega :
    res (PowerSeries.X * aiSeries * formalOmega) = momentSeries := by
  have hr : (PowerSeries.X : A) * aiSeries * formalOmega =
      PowerSeries.X * (aiSeries * formalOmega) := by ring
  rw [hr]
  ext n
  cases n with
  | zero =>
      simp [res, momentSeries, first_moment_residue_zero]
  | succ n =>
      simp only [res, PowerSeries.coeff_mk, PowerSeries.coeff_succ_X_mul,
        aiSeries, PowerSeries.coeff_C_mul, formalOmega, momentSeries]
      rw [ai, HahnSeries.coeff_single_mul]
      simp only [one_mul, sub_neg_eq_add, neg_add_cancel]
      rw [omega_coefficient]
      have he : (0 : ℤ) + n + 1 = ((n + 1 : ℕ) : ℤ) := by omega
      rw [he, LaurentSeries.coeff_coe_powerSeries]
      simp [halfSeries, first_moment_residue]

private lemma res_TT (b hb : ℂ) : res (cubicTTSeries b hb) = 0 := by
  rw [TT_decomposition, external_lift, res_lift_mul]
  have hinside : res ((half * aSeries + formalScalarC) * formalOmega -
      da (primitiveTT b)) = 0 := by
    rw [res_sub, res_da, sub_zero]
    calc
      _ = res (half * (aSeries * formalOmega) + formalScalarC * formalOmega) := by
        congr 1
        ring
      _ = PowerSeries.C (1 / 2 : ℂ) * momentSeries + scalarCSeries * periodSeries := by
        rw [res_add, half, res_lift_mul, res_a_omega]
        change PowerSeries.C (1 / 2 : ℂ) * momentSeries +
          res (lift scalarCSeries * formalOmega) = _
        rw [res_lift_mul, res_omega]
      _ = 0 := formal_scalar_normalization
  rw [hinside, mul_zero]

private lemma res_UT (b hb : ℂ) (hb0 : b ≠ 0) : res (cubicUTSeries b hb) = 0 := by
  rw [UT_decomposition b hb hb0, external_lift, res_lift_mul]
  have hinside : res (-((half * PowerSeries.X * aiSeries + formalScalarC) *
      formalOmega) - da (primitiveUT b)) = 0 := by
    rw [res_sub, res_neg, res_da, sub_zero]
    have hn : res ((half * PowerSeries.X * aiSeries + formalScalarC) * formalOmega) = 0 := by
      calc
        _ = res (half * (PowerSeries.X * aiSeries * formalOmega) +
            formalScalarC * formalOmega) := by congr 1; ring
        _ = PowerSeries.C (1 / 2 : ℂ) * momentSeries + scalarCSeries * periodSeries := by
          rw [res_add, half, res_lift_mul, res_x_ai_omega]
          change PowerSeries.C (1 / 2 : ℂ) * momentSeries +
            res (lift scalarCSeries * formalOmega) = _
          rw [res_lift_mul, res_omega]
        _ = 0 := formal_scalar_normalization
    rw [hn, neg_zero]
  rw [hinside, mul_zero]

/-- The a^(-1) coefficient of every x-degree of the original literal TT
kernel vanishes. The external root may be arbitrary: no root equation is
needed for this algebraic statement. -/
theorem cubicTT_residue_zero (b hb : ℂ) (_hb0 : b ≠ 0) (d : ℕ) :
    (PowerSeries.coeff d (cubicTTSeries b hb)).coeff (-1) = 0 := by
  have h := congrArg (PowerSeries.coeff d) (res_TT b hb)
  simpa only [res, PowerSeries.coeff_mk, map_zero] using h

/-- The a^(-1) coefficient of every x-degree of the original literal UT
kernel vanishes, with its original overall minus sign. Only b≠0 is used;
neither a selected root sign nor a sewing/resolvent identity is assumed. -/
theorem cubicUT_residue_zero (b hb : ℂ) (hb0 : b ≠ 0) (d : ℕ) :
    (PowerSeries.coeff d (cubicUTSeries b hb)).coeff (-1) = 0 := by
  have h := congrArg (PowerSeries.coeff d) (res_UT b hb hb0)
  simpa only [res, PowerSeries.coeff_mk, map_zero] using h

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicResidues


