/- GID: D5/S1/Recurrence/Residue/HannaMixedTrigHyperbolicModTen
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/HannaMixedTrigHyperbolicModTen
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hanna's mixed trigonometric-hyperbolic reciprocal coefficients are 3 modulo 10. -/

/-
Public theorem result:
proof_shape: content (the expanded proof includes triangular uniqueness and integrality induction).
escape_witness: D5.S1.Recurrence.Residue.HannaMixedTrigHyperbolicModTen.result
(the conclusion is produced through integrality induction and triangular uniqueness).
admission_basis: open-problem-resolution (#21582; Proved)
Direct frozen dependencies:
D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.sum_pairs
  statement_id sha256:7779f326a10cb0e250db2bbc5f0665a27b7ade7372d03e5a9d9c5e09c85d973f;
D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff
  statement_id sha256:4352a2872dd069de3ca054aab1c4950930a811b324435173c0e64781d46fc330;
D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_mul
  statement_id sha256:d77958a970452d82e689ee9878ff79fda28b9bc1537bf45041f667d5e694a1f5;
D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_zero
  statement_id sha256:69e1d2e22802c66151c2c3239fdceab9ab8a796d9f10d82c7366e4d57e790054.
The source definitions retain the rational Taylor expressions from issue #21582.
The Gaussian unit is the existing Zsqrtd.sqrtd; no type or unit alias is introduced.
The literal source sequence uses the existing factorial-normalized eCoeff owner.
All auxiliary declarations are private and used in the proof of result.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21976.
-/

import Mathlib.RingTheory.PowerSeries.WellKnown
import D5.S1.Recurrence.Residue.IntegralEGFComposition
import D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity

namespace D5.S1.Recurrence.Residue.HannaMixedTrigHyperbolicModTen

noncomputable section

/-- The rational formal Taylor series of sinh(x). -/
def sinhSeries : PowerSeries ℚ :=
  PowerSeries.mk fun m => if Even m then 0 else (m.factorial : ℚ)⁻¹

/-- The denominator in the NAME of OEIS A227051. -/
def denominator : PowerSeries ℚ :=
  PowerSeries.cos ℚ - PowerSeries.sin ℚ * sinhSeries

/-- The reciprocal EGF in the NAME of OEIS A227051. -/
def A : PowerSeries ℚ := denominator⁻¹

/-- a(n) = (2n)! [x^(2n)] A(x); odd-power coefficients are omitted. -/
def a (n : ℕ) : ℚ :=
  D5.S1.Recurrence.Residue.IntegralEGFComposition.eCoeff A (2 * n)

/-- OEIS A227051, first FORMULA: a(n) == 3 (mod 10) for n>0 (conjecture). -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ z : ℤ, a n = (z : ℚ) ∧ Int.ModEq 10 z 3

open Finset
private theorem sum_split {R : Type*} [AddCommMonoid R] (f : ℕ → R) (n : ℕ) :
    ∑ k ∈ range (2*n+1), f k =
      (∑ j ∈ range (n+1), f (2*j)) + ∑ j ∈ range n, f (2*j+1) := by
  rw [sum_range_succ,
    D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity.sum_pairs,
    sum_add_distrib, sum_range_succ]
  ac_rfl


private def rePart : (Zsqrtd (-1)) →+ ℤ where
  toFun := Zsqrtd.re
  map_zero' := rfl
  map_add' := Zsqrtd.re_add

private def imPart : (Zsqrtd (-1)) →+ ℤ where
  toFun := Zsqrtd.im
  map_zero' := rfl
  map_add' := Zsqrtd.im_add

private theorem gi_sq : (Zsqrtd.sqrtd (d := -1)) ^ 2 = -1 := by
  simpa only [pow_two, Int.cast_neg, Int.cast_one] using (Zsqrtd.dmuld (d := -1))

private theorem gi_even (j : ℕ) : (Zsqrtd.sqrtd (d := -1)) ^ (2*j) = (-1 : (Zsqrtd (-1)))^j := by
  rw [pow_mul, gi_sq]

private theorem gi_odd (j : ℕ) : (Zsqrtd.sqrtd (d := -1)) ^ (2*j+1) = (-1 : (Zsqrtd (-1)))^j * (Zsqrtd.sqrtd (d := -1)) := by
  rw [pow_succ, gi_even]

private theorem gi_cast_pow (j : ℕ) : (-1 : (Zsqrtd (-1)))^j = (((-1 : ℤ)^j : ℤ) : (Zsqrtd (-1))) := by
  norm_cast

private theorem gi_neg_one_re (j : ℕ) : ((-1 : (Zsqrtd (-1)))^j).re = (-1 : ℤ)^j := by
  rw [gi_cast_pow]
  exact Zsqrtd.re_intCast _

private theorem gi_neg_one_im (j : ℕ) : ((-1 : (Zsqrtd (-1)))^j).im = 0 := by
  rw [gi_cast_pow]
  exact Zsqrtd.im_intCast _

private theorem gauss_binomial (n : ℕ) :
    ((1+(Zsqrtd.sqrtd (d := -1)))^(2*n)).re = ∑ j ∈ range (n+1), ((2*n).choose (2*j) : ℤ)*(-1)^j ∧
    ((1+(Zsqrtd.sqrtd (d := -1)))^(2*n)).im = ∑ j ∈ range n, ((2*n).choose (2*j+1) : ℤ)*(-1)^j := by
  have h := add_pow (Zsqrtd.sqrtd (d := -1)) (1 : (Zsqrtd (-1))) (2*n)
  rw [add_comm (Zsqrtd.sqrtd (d := -1)) 1] at h
  simp only [one_pow, mul_one] at h
  rw [sum_split] at h
  simp only [gi_even, gi_odd] at h
  constructor
  · have hr := congrArg rePart h
    simp only [map_add, map_sum] at hr
    change ((1+(Zsqrtd.sqrtd (d := -1)))^(2*n)).re =
      (∑ j ∈ range (n+1), ((-1 : (Zsqrtd (-1)))^j * ((2*n).choose (2*j) : (Zsqrtd (-1)))).re) +
      ∑ j ∈ range n, ((-1 : (Zsqrtd (-1)))^j * (Zsqrtd.sqrtd (d := -1)) * ((2*n).choose (2*j+1) : (Zsqrtd (-1)))).re at hr
    simpa only [Zsqrtd.re_mul, Zsqrtd.im_mul, gi_neg_one_re, gi_neg_one_im,
      Zsqrtd.re_natCast, Zsqrtd.im_natCast, Zsqrtd.sqrtd, Zsqrtd.re_sqrtd, Zsqrtd.im_sqrtd,
      mul_zero, zero_mul, zero_add, add_zero, mul_one, one_mul, sum_const_zero, mul_comm] using hr
  · have hr := congrArg imPart h
    simp only [map_add, map_sum] at hr
    change ((1+(Zsqrtd.sqrtd (d := -1)))^(2*n)).im =
      (∑ j ∈ range (n+1), ((-1 : (Zsqrtd (-1)))^j * ((2*n).choose (2*j) : (Zsqrtd (-1)))).im) +
      ∑ j ∈ range n, ((-1 : (Zsqrtd (-1)))^j * (Zsqrtd.sqrtd (d := -1)) * ((2*n).choose (2*j+1) : (Zsqrtd (-1)))).im at hr
    simpa only [Zsqrtd.re_mul, Zsqrtd.im_mul, gi_neg_one_re, gi_neg_one_im,
      Zsqrtd.re_natCast, Zsqrtd.im_natCast, Zsqrtd.sqrtd, Zsqrtd.re_sqrtd, Zsqrtd.im_sqrtd,
      mul_zero, zero_mul, zero_add, add_zero, mul_one, one_mul, sum_const_zero, mul_comm] using hr

private theorem gauss_four (r : ℕ) :
    (1+(Zsqrtd.sqrtd (d := -1)))^(2*(2*r)) = (((-4 : ℤ)^r : ℤ) : (Zsqrtd (-1))) := by
  have h : (1+(Zsqrtd.sqrtd (d := -1)))^4 = (-4 : (Zsqrtd (-1))) := by
    exact Eq.symm (Zsqrtd.ext rfl rfl)
  rw [show 2*(2*r) = 4*r by omega, pow_mul, h]
  norm_cast

private theorem gauss_four_two (r : ℕ) :
    (1+(Zsqrtd.sqrtd (d := -1)))^(2*(2*r+1)) = ((2*(-4 : ℤ)^r : ℤ) : (Zsqrtd (-1)))*(Zsqrtd.sqrtd (d := -1)) := by
  rw [show 2*(2*r+1) = 2*(2*r)+2 by omega, pow_add, gauss_four]
  have h : (1+(Zsqrtd.sqrtd (d := -1)))^2 = 2*(Zsqrtd.sqrtd (d := -1)) := by
    exact pow_two (1 + (Zsqrtd.sqrtd (d := -1)))
  rw [h]
  push_cast
  ring


open PowerSeries
open D5.S1.Recurrence.Residue.IntegralEGFComposition

private def d (n : ℕ) : ℤ := (-1)^n - ((1+(Zsqrtd.sqrtd (d := -1)))^(2*n)).im

private theorem ec_cos (m : ℕ) : eCoeff (PowerSeries.cos ℚ) m =
    if Even m then (-1 : ℚ)^(m/2) else 0 := by
  simp only [eCoeff, PowerSeries.cos, coeff_mk]
  have hf : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  split_ifs <;> simp only [Algebra.algebraMap_self_apply, mul_zero]
  rw [mul_comm]
  exact div_mul_cancel₀ _ hf

private theorem ec_sin (m : ℕ) : eCoeff (PowerSeries.sin ℚ) m =
    if Even m then 0 else (-1 : ℚ)^(m/2) := by
  simp only [eCoeff, PowerSeries.sin, coeff_mk]
  have hf : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  split_ifs <;> simp only [Algebra.algebraMap_self_apply, mul_zero]
  rw [mul_comm]
  exact div_mul_cancel₀ _ hf

private theorem ec_sinh (m : ℕ) : eCoeff sinhSeries m =
    if Even m then 0 else 1 := by
  simp only [eCoeff, sinhSeries, coeff_mk]
  have hf : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  split_ifs <;> simp [hf]

private theorem ec_den_even (n : ℕ) : eCoeff denominator (2*n) = (d n : ℚ) := by
  have hp : eCoeff (PowerSeries.sin ℚ * sinhSeries) (2*n) =
      ∑ j ∈ range n, ((2*n).choose (2*j+1) : ℚ)*(-1)^j := by
    rw [eCoeff_mul, sum_split]
    have hz : (∑ j ∈ range (n+1), ((2*n).choose (2*j) : ℚ) *
        eCoeff (PowerSeries.sin ℚ) (2*j) * eCoeff sinhSeries (2*n-2*j)) = 0 := by
      apply sum_eq_zero
      intro j hj
      simp [ec_sin]
    rw [hz, zero_add]
    apply sum_congr rfl
    intro j hj
    have ho : ¬ Even (2*n-(2*j+1)) := by
      rw [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
      have hj' := mem_range.mp hj
      omega
    have hodd : ¬ Even (2*j+1) := Nat.not_even_two_mul_add_one j
    have hdiv : (2*j+1)/2 = j := by omega
    rw [ec_sin, if_neg hodd, ec_sinh, if_neg ho, hdiv, mul_one]
  have he : eCoeff denominator (2*n) =
      eCoeff (PowerSeries.cos ℚ) (2*n) -
      eCoeff (PowerSeries.sin ℚ * sinhSeries) (2*n) := by
    simp [denominator, eCoeff, mul_sub]
  rw [he, ec_cos, hp, d, (gauss_binomial n).2]
  push_cast
  simp

private theorem ec_den_odd (n : ℕ) : eCoeff denominator (2*n+1) = 0 := by
  have hp : eCoeff (PowerSeries.sin ℚ * sinhSeries) (2*n+1) = 0 := by
    rw [eCoeff_mul]
    apply sum_eq_zero
    intro i hi
    by_cases he : Even i
    · simp [ec_sin, he]
    · have he' : Even (2*n+1-i) := by
        rw [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero] at he ⊢
        have hi' := mem_range.mp hi
        omega
      simp [ec_sinh, he']
  have he : eCoeff denominator (2*n+1) =
      eCoeff (PowerSeries.cos ℚ) (2*n+1) -
      eCoeff (PowerSeries.sin ℚ * sinhSeries) (2*n+1) := by
    simp [denominator, eCoeff, mul_sub]
  rw [he, hp]
  simp [ec_cos]

private theorem d_even (r : ℕ) : d (2*r) = 1 := by
  rw [d, gauss_four, Zsqrtd.im_intCast]
  simp [pow_mul]

private theorem d_odd (r : ℕ) : d (2*r+1) = -1-2*(-4)^r := by
  rw [d, gauss_four_two]
  simp only [Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast, Zsqrtd.sqrtd,
    mul_one, zero_mul, add_zero]
  simp [pow_add, pow_mul]

private def conv {R : Type*} [CommRing R] (ds us : ℕ → R) (n : ℕ) : R :=
  ∑ j ∈ range (n+1), ((2*n).choose (2*j) : R)*ds j*us (n-j)

private theorem denominator_constant : constantCoeff denominator = 1 := by
  simpa only [Nat.mul_zero, eCoeff_zero, show d 0 = 1 from d_even 0, Int.cast_one] using ec_den_even 0

private theorem inverse_product (n : ℕ) :
    conv (fun j => (d j : ℚ)) a n = if n=0 then 1 else 0 := by
  have hm : denominator * A = 1 := by
    exact PowerSeries.mul_inv_cancel denominator (by rw [denominator_constant]; norm_num)
  have he := congrArg (fun s => eCoeff s (2*n)) hm
  rw [eCoeff_mul, sum_split] at he
  have hz : (∑ j ∈ range n, ((2*n).choose (2*j+1) : ℚ)*
      eCoeff denominator (2*j+1)*eCoeff A (2*n-(2*j+1))) = 0 := by
    apply sum_eq_zero
    intro j hj
    rw [ec_den_odd]
    ring
  rw [hz, add_zero] at he
  have hh : (∑ j ∈ range (n+1), ((2*n).choose (2*j) : ℚ)*
      eCoeff denominator (2*j)*eCoeff A (2*n-2*j)) =
      conv (fun j => (d j : ℚ)) a n := by
    apply sum_congr rfl
    intro j hj
    rw [ec_den_even, ← Nat.mul_sub_left_distrib]
    rfl
  rw [hh] at he
  by_cases hn : n=0 <;> simpa [eCoeff, coeff_one, hn] using he


private theorem conv_unique {R : Type*} [CommRing R] (ds u v : ℕ → R)
    (hd : ds 0 = 1) (h : ∀ n, conv ds u n = conv ds v n) : u = v := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hn := h n
    simp only [conv, sum_range_succ', Nat.mul_zero, Nat.choose_zero_right,
      Nat.cast_one, one_mul, hd, Nat.sub_zero] at hn
    have hs : (∑ j ∈ range n, ((2*n).choose (2*(j+1)) : R)*ds (j+1)*u (n-(j+1))) =
        ∑ j ∈ range n, ((2*n).choose (2*(j+1)) : R)*ds (j+1)*v (n-(j+1)) := by
      apply sum_congr rfl
      intro j hj
      rw [ih _ (by have := mem_range.mp hj; omega)]
    rw [hs] at hn
    exact add_left_cancel hn

private def z : ℕ → ℤ
  | 0 => 1
  | n+1 => - ∑ j : Fin (n+1), ((2*(n+1)).choose (2*(j.val+1)) : ℤ)*
      d (j.val+1)*z (n-j.val)
termination_by n => n

private theorem z_bridge (n : ℕ) : a n = (z n : ℚ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hn := inverse_product n
    cases n with
    | zero => simpa [conv, show d 0 = 1 from d_even 0, z] using hn
    | succ n =>
      unfold conv at hn
      rw [sum_range_succ'] at hn
      simp only [Nat.mul_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero] at hn
      have hd : d 0 = 1 := d_even 0
      rw [hd, Int.cast_one, one_mul, if_neg (by omega : n+1 ≠ 0)] at hn
      rw [z]
      push_cast
      rw [Fin.sum_univ_eq_sum_range (fun j => ((2*(n+1)).choose (2*(j+1)) : ℚ)*
        (d (j+1) : ℚ)*(z (n-j) : ℚ))]
      have hs : (∑ j ∈ range (n+1), ((2*(n+1)).choose (2*(j+1)) : ℚ)*
          (d (j+1) : ℚ)*a (n+1-(j+1))) =
          ∑ j ∈ range (n+1), ((2*(n+1)).choose (2*(j+1)) : ℚ)*
          (d (j+1) : ℚ)*(z (n-j) : ℚ) := by
        apply sum_congr rfl
        intro j hj
        rw [show n+1-(j+1) = n-j by omega, ih _ (by omega)]
      rw [hs] at hn
      linear_combination hn

private theorem z_product (n : ℕ) : conv d z n = if n=0 then 1 else 0 := by
  have h := inverse_product n
  simp only [conv, z_bridge] at h
  unfold conv
  exact_mod_cast h

private theorem conv_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (ds us : ℕ → R) (n : ℕ) :
    φ (conv ds us n) = conv (fun j => φ (ds j)) (fun j => φ (us j)) n := by
  simp [conv]

private def T (n : ℕ) : ℤ := ∑ j ∈ range (n+1), ((2*n).choose (2*j) : ℤ)
private def E (n : ℕ) : ℤ := ∑ j ∈ range (n+1), ((2*n).choose (2*j) : ℤ)*(-1)^j

/-
Bind-first owner: D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.symmetric_binomial_chi_square.
At B = 2*n and z = 1, with n > 0, its closed-form and finite-sum identities give
the sum over Icc 1 n as 2^(2*n)/2 - 1 over the reals. Adjoining the zero-index
term, multiplying by two, and using injectivity of the integer-to-real cast
gives the statement below. The S1 placement is not a mathematical obstruction
to this specialization. The current proof uses add_pow and does not consume
that owner.
-/
private theorem even_binomial (n : ℕ) (hn : 0<n) : 2*T n = 2^(2*n) := by
  have hp := add_pow (1 : ℤ) 1 (2*n)
  have hm := add_pow (-1 : ℤ) 1 (2*n)
  rw [sum_split] at hp hm
  simp only [one_add_one_eq_two, one_pow, one_mul, mul_one,
    neg_add_cancel, zero_pow (by omega : 2*n ≠ 0)] at hp hm
  have hneg (j : ℕ) : (-1 : ℤ)^(2*j) = 1 := by simp
  have hodd (j : ℕ) : (-1 : ℤ)^(2*j+1) = -1 := by simp [pow_add]
  simp only [hneg, hodd, one_mul, neg_one_mul] at hm
  rw [sum_neg_distrib] at hm
  unfold T
  linear_combination -hp -hm

private theorem even_binomial_pow (n : ℕ) (hn : 0<n) : T n = 2^(2*n-1) := by
  have h := even_binomial n hn
  rw [show 2*n = (2*n-1)+1 by omega, pow_succ] at h
  linarith

private theorem E_even (r : ℕ) : E (2*r) = (-4)^r := by
  have h := (gauss_binomial (2*r)).1
  rw [gauss_four, Zsqrtd.re_intCast] at h
  simpa only [E] using h.symm

private theorem E_odd (r : ℕ) : E (2*r+1) = 0 := by
  have h := (gauss_binomial (2*r+1)).1
  rw [gauss_four_two] at h
  simpa only [E, Zsqrtd.re_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast, Zsqrtd.sqrtd,
    Zsqrtd.re_sqrtd, Zsqrtd.im_sqrtd, mul_zero, mul_one, add_zero, zero_add] using h.symm

private theorem d_two (n : ℕ) : (d n : ZMod 2) = 1 := by
  obtain ⟨r, hr | hr⟩ := Nat.even_or_odd' n <;> subst n
  · rw [d_even]
    norm_num
  · rw [d_odd]
    push_cast
    rw [show (2 : ZMod 2) = 0 from ZMod.natCast_self 2]
    simp only [zero_mul, sub_zero]
    decide

private theorem d_five (n : ℕ) : (d n : ZMod 5) = if Even n then 1 else 2 := by
  obtain ⟨r, hr | hr⟩ := Nat.even_or_odd' n <;> subst n
  · rw [d_even]
    simp
  · rw [d_odd]
    push_cast
    rw [show (-4 : ZMod 5) = 1 by decide, one_pow]
    simp only [Nat.not_even_bit1, ite_false]
    decide

private theorem E_five (n : ℕ) : (E n : ZMod 5) = if Even n then 1 else 0 := by
  obtain ⟨r, hr | hr⟩ := Nat.even_or_odd' n <;> subst n
  · rw [E_even]
    push_cast
    rw [show (-4 : ZMod 5) = 1 by decide, one_pow]
    simp
  · rw [E_odd]
    simp

private theorem T_two (n : ℕ) (hn : 0<n) : (T n : ZMod 2) = 0 := by
  rw [even_binomial_pow n hn]
  push_cast
  rw [show (2 : ZMod 2)=0 from ZMod.natCast_self 2, zero_pow (by omega : 2*n-1 ≠ 0)]

private theorem T_five (n : ℕ) (hn : 0<n) :
    (T n : ZMod 5) = if Even n then 3 else 2 := by
  have h := congrArg (Int.castRingHom (ZMod 5)) (even_binomial n hn)
  simp only [map_mul, map_ofNat, map_pow, Int.coe_castRingHom] at h
  rw [pow_mul, show (2 : ZMod 5)^2 = -1 by decide] at h
  by_cases he : Even n
  · rw [if_pos he]
    have hh := congrArg (fun t : ZMod 5 => 3*t) h
    rw [← mul_assoc, show (3 : ZMod 5)*2=1 by decide, one_mul, he.neg_one_pow,
      mul_one] at hh
    exact hh
  · rw [if_neg he]
    have hh := congrArg (fun t : ZMod 5 => 3*t) h
    rw [← mul_assoc, show (3 : ZMod 5)*2=1 by decide, one_mul,
      (Nat.not_even_iff_odd.mp he).neg_one_pow, show (3 : ZMod 5)*(-1)=2 by decide] at hh
    exact hh


private theorem S_five (n : ℕ) :
    ((conv d (fun _ => 1) n : ℤ) : ZMod 5) = 3*(3*(T n : ZMod 5)-(E n : ZMod 5)) := by
  have hd (j : ℕ) : (d j : ZMod 5) = 3*(3-(-1 : ZMod 5)^j) := by
    rw [d_five]
    by_cases he : Even j
    · rw [if_pos he, he.neg_one_pow]
      decide
    · rw [if_neg he, (Nat.not_even_iff_odd.mp he).neg_one_pow]
      decide
  change (↑(∑ j ∈ range (n+1), ((2*n).choose (2*j) : ℤ)*d j*1) : ZMod 5) = _
  push_cast
  simp only [mul_one]
  simp_rw [hd]
  have hterm (j : ℕ) : ((2*n).choose (2*j) : ZMod 5)*(3*(3-(-1 : ZMod 5)^j)) =
      9*((2*n).choose (2*j) : ZMod 5)-3*(((2*n).choose (2*j) : ZMod 5)*(-1 : ZMod 5)^j) := by ring
  simp_rw [hterm]
  rw [sum_sub_distrib, ← mul_sum, ← mul_sum]
  simp only [T, E]
  push_cast
  ring

private theorem inverse_two (n : ℕ) :
    conv (fun j => (d j : ZMod 2)) (fun _ => 1) n = if n=0 then 1 else 0 := by
  by_cases hn : n=0
  · subst n
    simp [conv, show d 0 = 1 from d_even 0]
  · have ht := T_two n (by omega)
    simp only [conv, d_two, mul_one, if_neg hn]
    simpa [T] using ht

private theorem inverse_five (n : ℕ) :
    conv (fun j => (d j : ZMod 5)) (fun k => if k=0 then 1 else 3) n =
      if n=0 then 1 else 0 := by
  by_cases hn : n=0
  · subst n
    simp [conv, show d 0 = 1 from d_even 0]
  · have hc : conv (fun j => (d j : ZMod 5)) (fun k => if k=0 then 1 else 3) n =
        3*((conv d (fun _ => 1) n : ℤ) : ZMod 5)-2*(d n : ZMod 5) := by
      have hs : ((conv d (fun _ => 1) n : ℤ) : ZMod 5) =
          ∑ j ∈ range (n+1), ((2*n).choose (2*j) : ZMod 5)*(d j : ZMod 5) := by
        unfold conv
        push_cast
        simp only [mul_one]
      rw [hs]
      simp only [conv, sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul,
        Nat.sub_self, ite_true]
      have he : (∑ j ∈ range n, ((2*n).choose (2*j) : ZMod 5)*(d j : ZMod 5)*
          (if n-j=0 then 1 else 3)) =
          ∑ j ∈ range n, 3*(((2*n).choose (2*j) : ZMod 5)*(d j : ZMod 5)) := by
        apply sum_congr rfl
        intro j hj
        rw [if_neg (by have := mem_range.mp hj; omega : n-j ≠ 0)]
        ring
      rw [he, ← mul_sum]
      ring
    rw [hc, S_five, T_five n (by omega), E_five, d_five, if_neg hn]
    split_ifs <;> decide

private theorem z_two (n : ℕ) : (z n : ZMod 2) = 1 := by
  have hp (m : ℕ) : conv (fun j => (d j : ZMod 2)) (fun j => (z j : ZMod 2)) m =
      if m=0 then 1 else 0 := by
    have h := congrArg (Int.castRingHom (ZMod 2)) (z_product m)
    simpa only [conv_map, Int.coe_castRingHom, apply_ite, map_one, map_zero] using h
  exact congrFun (conv_unique _ _ _ (d_two 0)
    (fun m => (hp m).trans (inverse_two m).symm)) n

private theorem z_five (n : ℕ) (hn : 0<n) : (z n : ZMod 5) = 3 := by
  have hp (m : ℕ) : conv (fun j => (d j : ZMod 5)) (fun j => (z j : ZMod 5)) m =
      if m=0 then 1 else 0 := by
    have h := congrArg (Int.castRingHom (ZMod 5)) (z_product m)
    simpa only [conv_map, Int.coe_castRingHom, apply_ite, map_one, map_zero] using h
  have h := congrFun (conv_unique _ _ _ (by simpa using d_five 0)
    (fun m => (hp m).trans (inverse_five m).symm)) n
  simpa [show n ≠ 0 by omega] using h

theorem result : D5.S1.Recurrence.Residue.HannaMixedTrigHyperbolicModTen.claim := by
  intro n hn
  refine ⟨z n, z_bridge n, ?_⟩
  have h2 : Int.ModEq 2 (z n) 3 := by
    apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
    exact z_two n
  have h5 : Int.ModEq 5 (z n) 3 := by
    apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
    exact z_five n (by omega)
  exact (Int.modEq_and_modEq_iff_modEq_mul (by decide : (2 : ℤ).natAbs.Coprime (5 : ℤ).natAbs)).mp ⟨h2,h5⟩


end
end D5.S1.Recurrence.Residue.HannaMixedTrigHyperbolicModTen
