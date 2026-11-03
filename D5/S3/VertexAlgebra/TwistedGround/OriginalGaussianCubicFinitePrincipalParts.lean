import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicKernel
import D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
UNCOMPILED SOURCE ATTEMPT. No elaboration, kernel or official acceptance.

The imported OriginalGaussianCubicKernel is the unchanged, hash-pinned
29307-byte supplier, itself uncompiled. This file preserves its definitions
and their order. It does not assert CubicOriginalCoefficientIdentity.

Content supplied here: the finite current numerator, its identification with
the literal currentRow, ALL its negative and regular Laurent coefficients,
and finite numerator uniqueness using native truncation. The regular
coefficient proof reuses the committed halfBinomial_positive_convolution,
not bounded tests or an assumed pair-kernel correspondence.

Both actual all-degree pole bounds are supplied: TT vanishes for d<=s and
UT for d<s. The moving UT denominator uses native invUnitsSub; no infinite
Laurent substitution is performed. The polynomial polar identities and
actual UT degree-zero calculation are additional literal-cubic content.
All-degree finite-class membership and the admissible sewing coefficient
bridge remain open; they are not hypotheses of a claimed cubic identity.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicKernel

open D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection

private abbrev rootSeries : PowerSeries ℂ :=
  PowerSeries.binomialSeries ℂ (1 / 2 : ℂ)

private lemma rootSeries_coeff (n : ℕ) :
    PowerSeries.coeff n rootSeries = Ring.choose (1 / 2 : ℂ) n := by
  simp [rootSeries, PowerSeries.binomialSeries_coeff]

private lemma halfSeries_binomial :
    halfSeries = PowerSeries.binomialSeries ℂ (-1 / 2 : ℂ) := by
  ext n
  simp [halfSeries, PowerSeries.binomialSeries_coeff, halfBinomial_choose]

private lemma root_mul_half : rootSeries * halfSeries = 1 := by
  rw [halfSeries_binomial, rootSeries, ← PowerSeries.binomialSeries_add,
    show (1 / 2 : ℂ) + -1 / 2 = 0 by norm_num,
    PowerSeries.binomialSeries_zero]

/-- The actual finite numerator in c_s, before its s/hypotenuse factors. -/
def finiteCurrentNumerator (s : ℕ) : Polynomial ℂ :=
  PowerSeries.trunc (s + 1) rootSeries

/-- The finite expression s H(a) a^(-s-1) sum_{k<=s} choose(1/2,k)a^k.
This is a basis current; neither cubic is defined using it. -/
def finiteCurrentLaurent (s : ℕ) : LaurentSeries ℂ :=
  HahnSeries.single (-(s : ℤ) - 1) (s : ℂ) *
    (((finiteCurrentNumerator s : PowerSeries ℂ) * halfSeries) : LaurentSeries ℂ)

theorem finite_current_numerator_degree (s : ℕ) :
    (finiteCurrentNumerator s).degree < (s + 1 : ℕ) :=
  PowerSeries.degree_trunc_lt rootSeries (s + 1)

private lemma current_truncated_product (s : ℕ) :
    PowerSeries.trunc (s + 1)
      ((finiteCurrentNumerator s : PowerSeries ℂ) * halfSeries) = 1 := by
  rw [finiteCurrentNumerator, PowerSeries.trunc_trunc_mul,
    root_mul_half, PowerSeries.trunc_one]

private lemma current_product_low (s n : ℕ) (hn : n < s + 1) :
    PowerSeries.coeff n
      ((finiteCurrentNumerator s : PowerSeries ℂ) * halfSeries) =
        if n = 0 then 1 else 0 := by
  have h := congrArg (fun p : Polynomial ℂ => p.coeff n)
    (current_truncated_product s)
  simpa only [PowerSeries.coeff_trunc, if_pos hn, Polynomial.coeff_one] using h

/-- Every negative exponent is accounted for, including the residue.
No positivity assumption on s is necessary for this totalized formula. -/
theorem finite_current_negative_coeff (s : ℕ) (k : ℤ) (hk : k < 0) :
    (finiteCurrentLaurent s).coeff k =
      if k = -(s : ℤ) - 1 then (s : ℂ) else 0 := by
  rw [finiteCurrentLaurent, HahnSeries.coeff_single_mul]
  have he : k - (-(s : ℤ) - 1) = k + s + 1 := by omega
  rw [he]
  by_cases hneg : k + (s : ℤ) + 1 < 0
  · rw [LaurentSeries.coeff_coe, if_pos hneg, mul_zero,
      if_neg (by omega : k ≠ -(s : ℤ) - 1)]
  · let n : ℕ := (k + (s : ℤ) + 1).toNat
    have hncast : (n : ℤ) = k + (s : ℤ) + 1 :=
      Int.toNat_of_nonneg (le_of_not_gt hneg)
    have hn : n < s + 1 := by omega
    rw [← hncast, LaurentSeries.coeff_coe_powerSeries, current_product_low s n hn]
    by_cases heq : k = -(s : ℤ) - 1
    · have hn0 : n = 0 := by omega
      simp only [heq, hn0, ite_true, mul_one]
    · have hn0 : n ≠ 0 := by omega
      simp only [heq, hn0, ite_false, mul_zero]

theorem finite_current_residue (s : ℕ) :
    (finiteCurrentLaurent s).coeff (-1) = 0 := by
  rw [finite_current_negative_coeff s (-1) (by norm_num)]
  by_cases hs : s = 0
  · simp [hs]
  · rw [if_neg (by omega : (-1 : ℤ) ≠ -(s : ℤ) - 1)]

private lemma current_product_as_sum (s n : ℕ) (hsn : s ≤ n) :
    PowerSeries.coeff n
      ((finiteCurrentNumerator s : PowerSeries ℂ) * halfSeries) =
        ∑ k ∈ Finset.range (s + 1),
          Ring.choose (1 / 2 : ℂ) k * halfBinomial (n - k) := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Polynomial.coeff_coe, finiteCurrentNumerator,
    PowerSeries.coeff_trunc, rootSeries_coeff, halfSeries, PowerSeries.coeff_mk]
  have hsub : Finset.range (s + 1) ⊆ Finset.range (n + 1) :=
    Finset.range_mono (by omega)
  calc
    _ = ∑ k ∈ Finset.range (s + 1),
        (if k < s + 1 then Ring.choose (1 / 2 : ℂ) k else 0) *
          halfBinomial (n - k) := by
      symm
      apply Finset.sum_subset hsub
      intro k _ hk
      rw [if_neg (by simpa only [Finset.mem_range] using hk), zero_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [if_pos (Finset.mem_range.mp hk)]

private lemma current_product_high (s t : ℕ) (ht : 0 < t) :
    PowerSeries.coeff (s + t)
      ((finiteCurrentNumerator s : PowerSeries ℂ) * halfSeries) =
        (t : ℂ) * halfBinomial t * halfBinomial s / ((t : ℂ) + s) := by
  rw [current_product_as_sum s (s + t) (by omega)]
  have hreflect := Finset.sum_range_reflect
    (fun k => Ring.choose (1 / 2 : ℂ) k * halfBinomial (s + t - k)) (s + 1)
  rw [← hreflect]
  calc
    _ = ∑ j ∈ Finset.range (s + 1),
        halfBinomial (t + j) * Ring.choose (1 / 2 : ℂ) (s - j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j ≤ s := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
      have hsub : s + t - (s + 1 - 1 - j) = t + j := by omega
      rw [hsub, show s + 1 - 1 - j = s - j by omega]
      ring
    _ = _ := halfBinomial_positive_convolution t s ht

/-- The ENTIRE regular tail is the original pairScalar, including s=t.
This is an all-index finite convolution proof, not finite testing. -/
theorem finite_current_regular_coeff (s t : ℕ) (ht : 0 < t) :
    (finiteCurrentLaurent s).coeff ((t : ℤ) - 1) = pairScalar s t := by
  rw [finiteCurrentLaurent, HahnSeries.coeff_single_mul]
  have he : (t : ℤ) - 1 - (-(s : ℤ) - 1) = ((s + t : ℕ) : ℤ) := by omega
  rw [he, LaurentSeries.coeff_coe_powerSeries, current_product_high s t ht]
  unfold pairScalar
  rw [add_comm (t : ℂ) (s : ℂ)]
  ring

private lemma current_numerator_eval (b : ℂ) (s : ℕ) :
    (finiteCurrentNumerator s).eval b =
      ∑ k ∈ Finset.range (s + 1), Ring.choose (1 / 2 : ℂ) k * b ^ k := by
  simpa only [finiteCurrentNumerator, Polynomial.eval₂_id, RingHom.id_apply,
    rootSeries_coeff] using
    (PowerSeries.eval₂_trunc_eq_sum_range b (RingHom.id ℂ) (s + 1) rootSeries)

/-- Exact binding to the supplied original row. Both signs of hb remain.
The identity even holds at totalized b=0; no external restriction is added. -/
theorem currentRow_eq_finite_numerator (b hb : ℂ) (s : ℕ) :
    currentRow b hb s =
      (s : ℂ) * hb * (finiteCurrentNumerator s).eval b / b ^ (s + 1) := by
  rw [currentRow, current_numerator_eval, Finset.sum_div]
  ring

/- Native finite uniqueness. These adapters are private and are actually
used by the following numerator uniqueness theorem. There is no cubic
normalization or target identity among their hypotheses. -/
private lemma cancel_half_trunc (N : ℕ) (f : PowerSeries ℂ)
    (h : PowerSeries.trunc N (halfSeries * f) = 0) :
    PowerSeries.trunc N f = 0 := by
  have hmul := congrArg (fun p : Polynomial ℂ =>
    PowerSeries.trunc N (rootSeries * (p : PowerSeries ℂ))) h
  simpa only [PowerSeries.trunc_mul_trunc, ← mul_assoc, root_mul_half,
    one_mul, Polynomial.coe_zero, mul_zero, map_zero] using hmul

private lemma polynomial_zero_of_half_trunc (N : ℕ) (p : Polynomial ℂ)
    (hdeg : p.degree < N)
    (h : PowerSeries.trunc N (halfSeries * (p : PowerSeries ℂ)) = 0) : p = 0 := by
  have hp := cancel_half_trunc N (p : PowerSeries ℂ) h
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_zero]
  by_cases hn : n < N
  · have hc := congrArg (fun q : Polynomial ℂ => q.coeff n) hp
    simpa only [PowerSeries.coeff_trunc, if_pos hn, Polynomial.coeff_coe,
      Polynomial.coeff_zero] using hc
  · exact (Polynomial.degree_lt_iff_coeff_zero p N).mp hdeg n (le_of_not_gt hn)

/-- In the proposed finite class the current numerator is forced by its
principal part. This concerns the explicit basis current only; finite-class
membership of the literal cubic still has to be derived. -/
theorem finite_current_numerator_unique (s : ℕ) (p : Polynomial ℂ)
    (hdeg : p.degree < (s + 1 : ℕ))
    (h : PowerSeries.trunc (s + 1) (halfSeries * (p : PowerSeries ℂ)) = 1) :
    p = finiteCurrentNumerator s := by
  apply sub_eq_zero.mp
  apply polynomial_zero_of_half_trunc (s + 1) (p - finiteCurrentNumerator s)
  · exact (Polynomial.degree_sub_le _ _).trans_lt
      (max_lt hdeg (finite_current_numerator_degree s))
  · have hcurrent : PowerSeries.trunc (s + 1)
        (halfSeries * (finiteCurrentNumerator s : PowerSeries ℂ)) = 1 := by
      rw [mul_comm]
      exact current_truncated_product s
    rw [Polynomial.coe_sub, mul_sub, map_sub, h, hcurrent, sub_self]

/-- The original external-root hypothesis excludes the branch point.
Neither a principal square-root convention nor positivity is used. -/
theorem external_root_exclusions (b hb : ℂ) (hroot : (1 + b) * hb ^ 2 = 1) :
    hb ≠ 0 ∧ b ≠ -1 := by
  constructor
  · intro h
    rw [h] at hroot
    norm_num at hroot
  · intro h
    rw [h] at hroot
    norm_num at hroot

/-- The derivative numerator is written out to avoid a new curve API. -/
private def cubicDerivative (x a : ℂ) : ℂ :=
  3 * a ^ 2 + 2 * (1 + x) * a + x

/-- Exact identity behind the literal TT total derivative. -/
theorem literal_polar_derivative_identity (x a b : ℂ) :
    a * (a - b) ^ 2 - cubicDerivative x a * (a - b) + 2 * cubic x a =
      polar x a b := by
  unfold cubicDerivative cubic polar
  ring

/-- Exact expansions, with no degree cutoff: the two diagonal coefficients
are 2P(b), P'(b). The root cancellation must still be applied to the actual
formalOmega and externalOmega, on both sheets, in the remaining proof. -/
theorem literal_diagonal_polynomials (x b v : ℂ) :
    polar x (b + v) b =
      2 * cubic x b + cubicDerivative x b * v + b * v ^ 2 ∧
    cubic x (b + v) = cubic x b + cubicDerivative x b * v +
      (3 * b + 1 + x) * v ^ 2 + v ^ 3 := by
  constructor <;> unfold polar cubic cubicDerivative <;> ring

/-- Cleared finite rational pullback of the literal polar. This is NOT
substitution of x/u into unrestricted iterated formal power series. -/
theorem literal_pullback_polar (x u b : ℂ) (hu : u ≠ 0) :
    u ^ 2 * polar x (x / u) b =
      x * (u * b * (u + b + 2) + x * (u + b + 2 * u * b)) := by
  unfold polar
  field_simp [hu]
  <;> ring

private lemma scalarCSeries_constant_zero : PowerSeries.constantCoeff scalarCSeries = 0 := by
  simp [scalarCSeries]

/- The following private coefficient-support adapters are used to prove
the literal cubic pole bounds. They neither substitute a=x/u into a series
nor posit rational regularity or a desired sewing equation. -/
private def annularFloor (K : AnnulusSeries) (c : ℤ) : Prop :=
  ∀ d : ℕ, ∀ k : ℤ, k + d < c → (PowerSeries.coeff d K).coeff k = 0

private lemma laurent_product_vanish (f g : LaurentSeries ℂ) (p q : ℤ)
    (hf : ∀ k : ℤ, k < p → f.coeff k = 0)
    (hg : ∀ k : ℤ, k < q → g.coeff k = 0)
    (k : ℤ) (hk : k < p + q) : (f * g).coeff k = 0 := by
  have hf' : (p : WithTop ℤ) ≤ f.orderTop :=
    HahnSeries.le_orderTop_iff_forall.mpr (fun j hj => hf j (by exact_mod_cast hj))
  have hg' : (q : WithTop ℤ) ≤ g.orderTop :=
    HahnSeries.le_orderTop_iff_forall.mpr (fun j hj => hg j (by exact_mod_cast hj))
  have hprod : ((p + q : ℤ) : WithTop ℤ) ≤ (f * g).orderTop := by
    simpa using (add_le_add hf' hg').trans HahnSeries.orderTop_add_le_mul
  exact HahnSeries.coeff_eq_zero_of_lt_orderTop
    ((show (k : WithTop ℤ) < ((p + q : ℤ) : WithTop ℤ) by exact_mod_cast hk).trans_le
      hprod)

private lemma annular_floor_mono {K : AnnulusSeries} {c c' : ℤ}
    (h : annularFloor K c) (hc : c' ≤ c) : annularFloor K c' := by
  intro d k hk
  exact h d k (hk.trans_le hc)

private lemma annular_floor_add {K L : AnnulusSeries} {c : ℤ}
    (hK : annularFloor K c) (hL : annularFloor L c) : annularFloor (K + L) c := by
  intro d k hk
  simp only [map_add, HahnSeries.coeff_add, hK d k hk, hL d k hk, add_zero]

private lemma annular_floor_neg {K : AnnulusSeries} {c : ℤ}
    (hK : annularFloor K c) : annularFloor (-K) c := by
  intro d k hk
  simp only [map_neg, HahnSeries.coeff_neg, hK d k hk, neg_zero]

private lemma annular_floor_mul {K L : AnnulusSeries} {p q : ℤ}
    (hK : annularFloor K p) (hL : annularFloor L q) : annularFloor (K * L) (p + q) := by
  intro d k hk
  rw [PowerSeries.coeff_mul, HahnSeries.coeff_sum]
  apply Finset.sum_eq_zero
  intro ij hij
  have hij' : ij.1 + ij.2 = d := Finset.mem_antidiagonal.mp hij
  apply laurent_product_vanish _ _ (p - ij.1) (q - ij.2)
  · intro j hj
    exact hK ij.1 j (by omega)
  · intro j hj
    exact hL ij.2 j (by omega)
  · omega

private lemma annular_floor_coe (f : PowerSeries ℂ) :
    annularFloor (PowerSeries.C (f : LaurentSeries ℂ)) 0 := by
  intro d k hk
  by_cases hd : d = 0
  · subst d
    rw [PowerSeries.coeff_zero_C, LaurentSeries.coeff_coe,
      if_pos (by omega : k < 0)]
  · rw [PowerSeries.coeff_C_of_ne_zero hd]
    simp

private lemma annular_floor_scalar (c : ℂ) :
    annularFloor (PowerSeries.C (HahnSeries.C c)) 0 := by
  simpa only [HahnSeries.ofPowerSeries_C] using annular_floor_coe (PowerSeries.C c)

private abbrev localA : AnnulusSeries :=
  PowerSeries.C (HahnSeries.single 1 (1 : ℂ))

private abbrev localB (b : ℂ) : AnnulusSeries := PowerSeries.C (HahnSeries.C b)

private abbrev localC : AnnulusSeries :=
  PowerSeries.map (HahnSeries.C : ℂ →+* LaurentSeries ℂ) scalarCSeries

private lemma annular_floor_a : annularFloor localA 1 := by
  intro d k hk
  by_cases hd : d = 0
  · subst d
    rw [PowerSeries.coeff_zero_C, HahnSeries.coeff_single,
      if_neg (by omega)]
  · rw [PowerSeries.coeff_C_of_ne_zero hd]
    simp

private lemma annular_floor_x : annularFloor (PowerSeries.X : AnnulusSeries) 1 := by
  intro d k hk
  by_cases hd : d = 1
  · subst d
    rw [PowerSeries.coeff_one_X]
    change (HahnSeries.single 0 (1 : ℂ)).coeff k = 0
    rw [HahnSeries.coeff_single, if_neg (by omega)]
  · rw [PowerSeries.coeff_X, if_neg hd]
    simp

private lemma annular_floor_omega : annularFloor formalOmega (-1) := by
  intro d k hk
  change (omegaCoefficient d).coeff k = 0
  rw [omegaCoefficient, HahnSeries.coeff_single_mul]
  have hneg : k - (-(d : ℤ) - 1) < 0 := by omega
  rw [LaurentSeries.coeff_coe, if_pos hneg, mul_zero]

private lemma annular_floor_external (b hb : ℂ) :
    annularFloor (formalExternalOmega b hb) 0 := by
  intro d k hk
  change (HahnSeries.C (hb * halfBinomial d / b ^ (d + 1))).coeff k = 0
  rw [HahnSeries.C_apply, HahnSeries.coeff_single, if_neg (by omega)]

private lemma annular_floor_c : annularFloor localC 1 := by
  intro d k hk
  rw [PowerSeries.coeff_map]
  by_cases hd : d = 0
  · subst d
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, scalarCSeries_constant_zero,
      map_zero]
    simp
  · rw [HahnSeries.C_apply, HahnSeries.coeff_single, if_neg (by omega)]

private lemma coe_inverse_of_unit (f : PowerSeries ℂ)
    (hf : PowerSeries.constantCoeff f ≠ 0) :
    ((f⁻¹ : PowerSeries ℂ) : LaurentSeries ℂ) = (f : LaurentSeries ℂ)⁻¹ := by
  have hmul : (f : LaurentSeries ℂ) * ((f⁻¹ : PowerSeries ℂ) : LaurentSeries ℂ) = 1 := by
    change HahnSeries.ofPowerSeries ℤ ℂ f * HahnSeries.ofPowerSeries ℤ ℂ f⁻¹ = 1
    rw [← map_mul, PowerSeries.mul_inv_cancel f hf, map_one]
  have hne : (f : LaurentSeries ℂ) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hmul
    exact zero_ne_one hmul
  exact mul_left_cancel₀ hne (hmul.trans (mul_inv_cancel₀ hne).symm)

private lemma annular_floor_tt_inverse (b : ℂ) (hb : b ≠ 0) :
    annularFloor ((2 * (localA - localB b) ^ 2)⁻¹) 0 := by
  let D : PowerSeries ℂ := 2 * (PowerSeries.X - PowerSeries.C b) ^ 2
  have hD : PowerSeries.constantCoeff D ≠ 0 := by
    simpa [D] using mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (pow_ne_zero 2 (neg_ne_zero.mpr hb))
  have he : 2 * (localA - localB b) ^ 2 =
      PowerSeries.C (D : LaurentSeries ℂ) := by
    simp [D, localA, localB, map_mul, map_sub, map_pow, HahnSeries.ofPowerSeries_X,
      HahnSeries.ofPowerSeries_C]
  rw [he, PowerSeries.C_inv, ← coe_inverse_of_unit D hD]
  exact annular_floor_coe D⁻¹

/-- TT's stronger all-degree bound follows from the literal numerator's
factor a at degree zero and factor x in its remaining terms. -/
theorem cubic_tt_pole_bound (b hb : ℂ) (hb0 : b ≠ 0) (s d : ℕ) (hds : d ≤ s) :
    negativeCoefficient (cubicTTSeries b hb) s d = 0 := by
  have ha0 := annular_floor_mono annular_floor_a (by norm_num : (0 : ℤ) ≤ 1)
  have hB := annular_floor_scalar b
  have h2 : annularFloor (2 : AnnulusSeries) 0 := by
    simpa only [map_ofNat] using annular_floor_scalar (2 : ℂ)
  let E := formalOmega * formalExternalOmega b hb
  let D : AnnulusSeries := (2 * (localA - localB b) ^ 2)⁻¹
  have hE : annularFloor E (-1) := by
    simpa [E] using annular_floor_mul annular_floor_omega (annular_floor_external b hb)
  have hD : annularFloor D 0 := annular_floor_tt_inverse b hb0
  have hP : annularFloor (localB b * (localA + localB b + 2) * D) 0 := by
    simpa using annular_floor_mul
      (annular_floor_mul hB (annular_floor_add (annular_floor_add ha0 hB) h2)) hD
  have hQ : annularFloor ((2 * localA * localB b + localA + localB b) * D) 0 := by
    simpa using annular_floor_mul
      (annular_floor_add (annular_floor_add
        (by simpa using annular_floor_mul (annular_floor_mul h2 ha0) hB) ha0) hB) hD
  have hEA : annularFloor (E * localA) 0 := by
    simpa using annular_floor_mul hE annular_floor_a
  have hEX : annularFloor (E * PowerSeries.X) 0 := by
    simpa using annular_floor_mul hE annular_floor_x
  have hEC : annularFloor (E * localC) 0 := by
    simpa using annular_floor_mul hE annular_floor_c
  have hsum : annularFloor
      (E * localA * (localB b * (localA + localB b + 2) * D) +
        E * PowerSeries.X * ((2 * localA * localB b + localA + localB b) * D) +
        E * localC) 0 := by
    exact annular_floor_add
      (annular_floor_add (by simpa using annular_floor_mul hEA hP)
        (by simpa using annular_floor_mul hEX hQ)) hEC
  have heq : cubicTTSeries b hb =
      E * localA * (localB b * (localA + localB b + 2) * D) +
        E * PowerSeries.X * ((2 * localA * localB b + localA + localB b) * D) +
        E * localC := by
    change E * ((localA * localB b * (localA + localB b) +
      2 * (1 + PowerSeries.X) * localA * localB b +
      PowerSeries.X * (localA + localB b)) * D + localC) = _
    ring
  rw [negativeCoefficient, heq]
  exact hsum d (-(s : ℤ) - 1) (by omega)

private lemma annular_floor_ut_inverse (b : ℂ) (hb : b ≠ 0) :
    annularFloor ((2 * (localA * localB b - PowerSeries.X) ^ 2)⁻¹) (-2) := by
  let u : (LaurentSeries ℂ)ˣ :=
    Units.mk0 (HahnSeries.single 1 b) (HahnSeries.single_ne_zero hb)
  let J : AnnulusSeries := PowerSeries.invUnitsSub u
  have hAB : localA * localB b = PowerSeries.C (HahnSeries.single 1 b) := by
    change PowerSeries.C (HahnSeries.single 1 (1 : ℂ)) *
      PowerSeries.C (HahnSeries.C b) = _
    rw [← map_mul, HahnSeries.C_apply, HahnSeries.single_mul_single]
    simp
  have hJ : J * (localA * localB b - PowerSeries.X) = 1 := by
    rw [hAB]
    exact PowerSeries.invUnitsSub_mul_sub u
  have hJfloor : annularFloor J (-1) := by
    intro d k hk
    rw [PowerSeries.coeff_invUnitsSub, one_divp, Units.val_inv_eq_inv_val,
      Units.val_pow_eq_pow_val]
    change (((HahnSeries.single 1 b : LaurentSeries ℂ) ^ (d + 1))⁻¹).coeff k = 0
    rw [HahnSeries.single_pow, HahnSeries.inv_single]
    simp only [nsmul_eq_mul, mul_one]
    rw [HahnSeries.coeff_single, if_neg (by omega)]
  have hconst : PowerSeries.constantCoeff
      (2 * (localA * localB b - PowerSeries.X) ^ 2) ≠ 0 := by
    rw [hAB]
    simpa using mul_ne_zero (by norm_num : (2 : LaurentSeries ℂ) ≠ 0)
      (pow_ne_zero 2 (HahnSeries.single_ne_zero hb))
  have hhalf : (PowerSeries.C (1 / 2 : LaurentSeries ℂ) : AnnulusSeries) * 2 = 1 := by
    have h := congrArg (PowerSeries.C (R := LaurentSeries ℂ))
      (by norm_num : (1 / 2 : LaurentSeries ℂ) * 2 = 1)
    simpa only [map_mul, map_ofNat, map_one] using h
  have hmul : (PowerSeries.C (1 / 2 : LaurentSeries ℂ) * J ^ 2) *
      (2 * (localA * localB b - PowerSeries.X) ^ 2) = 1 := by
    calc
      _ = (PowerSeries.C (1 / 2 : LaurentSeries ℂ) * 2) *
          (J * (localA * localB b - PowerSeries.X)) ^ 2 := by ring
      _ = 1 := by rw [hhalf, hJ]; simp
  have heq : (2 * (localA * localB b - PowerSeries.X) ^ 2)⁻¹ =
      PowerSeries.C (1 / 2 : LaurentSeries ℂ) * J ^ 2 :=
    ((PowerSeries.eq_inv_iff_mul_eq_one hconst).mpr hmul).symm
  rw [heq, pow_two]
  have hh : annularFloor (PowerSeries.C (1 / 2 : LaurentSeries ℂ)) 0 := by
    simpa using annular_floor_scalar (1 / 2 : ℂ)
  simpa using annular_floor_mul hh (annular_floor_mul hJfloor hJfloor)

/-- All-degree UT pole order, proved with the native invUnitsSub expansion.
The moving denominator contributes exactly its admissible degree support. -/
theorem cubic_ut_pole_bound (b hb : ℂ) (hb0 : b ≠ 0) (s d : ℕ) (hds : d < s) :
    negativeCoefficient (cubicUTSeries b hb) s d = 0 := by
  have ha0 := annular_floor_mono annular_floor_a (by norm_num : (0 : ℤ) ≤ 1)
  have hB := annular_floor_scalar b
  have h2 : annularFloor (2 : AnnulusSeries) 0 := by
    simpa only [map_ofNat] using annular_floor_scalar (2 : ℂ)
  let E := formalOmega * formalExternalOmega b hb
  let D : AnnulusSeries := (2 * (localA * localB b - PowerSeries.X) ^ 2)⁻¹
  let N : AnnulusSeries := PowerSeries.X *
    (localA * localB b * (localA + localB b + 2) +
      PowerSeries.X * (localA + localB b + 2 * localA * localB b))
  have hE : annularFloor E (-1) := by
    simpa [E] using annular_floor_mul annular_floor_omega (annular_floor_external b hb)
  have hD : annularFloor D (-2) := annular_floor_ut_inverse b hb0
  have hP : annularFloor (localA * localB b * (localA + localB b + 2)) 1 := by
    simpa using annular_floor_mul (annular_floor_mul annular_floor_a hB)
      (annular_floor_add (annular_floor_add ha0 hB) h2)
  have hQ : annularFloor (localA + localB b + 2 * localA * localB b) 0 := by
    exact annular_floor_add (annular_floor_add ha0 hB)
      (by simpa using annular_floor_mul (annular_floor_mul h2 ha0) hB)
  have hN : annularFloor N 2 := by
    dsimp only [N]
    simpa using annular_floor_mul annular_floor_x
      (annular_floor_add hP (by simpa using annular_floor_mul annular_floor_x hQ))
  have hmain : annularFloor (E * N * D) (-1) := by
    simpa using annular_floor_mul (annular_floor_mul hE hN) hD
  have hEC : annularFloor (E * localC) (-1) := by
    apply annular_floor_mono (c := 0)
    · simpa using annular_floor_mul hE annular_floor_c
    · norm_num
  have hsum := annular_floor_neg (annular_floor_add hmain hEC)
  have heq : cubicUTSeries b hb = -(E * N * D + E * localC) := by
    change -E * (N * D + localC) = _
    ring
  rw [negativeCoefficient, heq]
  exact hsum d (-(s : ℤ) - 1) (by omega)

/-- Actual UT degree zero, proved from the independently defined cubic. -/
theorem cubic_ut_degree_zero (b hb : ℂ) :
    PowerSeries.coeff 0 (cubicUTSeries b hb) = 0 := by
  let a : AnnulusSeries := PowerSeries.C (HahnSeries.single 1 (1 : ℂ))
  let B : AnnulusSeries := PowerSeries.C (HahnSeries.C b)
  have hmap : PowerSeries.constantCoeff
      (PowerSeries.map (HahnSeries.C : ℂ →+* LaurentSeries ℂ) scalarCSeries) = 0 := by
    change HahnSeries.C (PowerSeries.constantCoeff scalarCSeries) = 0
    rw [scalarCSeries_constant_zero, map_zero]
  change PowerSeries.constantCoeff
    (-(formalOmega * formalExternalOmega b hb) *
      (PowerSeries.X * (a * B * (a + B + 2) +
        PowerSeries.X * (a + B + 2 * a * B)) *
        (2 * (a * B - PowerSeries.X) ^ 2)⁻¹ +
        PowerSeries.map (HahnSeries.C : ℂ →+* LaurentSeries ℂ) scalarCSeries)) = 0
  simp only [map_mul, map_add, map_neg, PowerSeries.constantCoeff_X,
    zero_mul, zero_add, hmap, mul_zero]

/- No cubic_original_coefficient_identity declaration is supplied here.
The result envelope gives the exact all-degree reconstruction and sewing
equations which remain unproved, with their original telescopes.
-/

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicKernel
