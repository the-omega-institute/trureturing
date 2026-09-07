/- GID: D5/S3/Zeros/Convolution/FiniteFreeCommutatorDegreeFive
   generality: I
   mirror-B: D5/B/S3/Zeros/Convolution/FiniteFreeCommutatorDegreeFive
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=terminal=gid:D5/S3/Zeros/Convolution/FiniteFreeCommutatorDegreeFive.real_rooted
   digest: The source-defined finite free commutator preserves real roots in degree five. -/

import D5.S3.Zeros.Convolution.FiniteFreeCommutatorDegreeFour
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Data.Fin.Tuple.Sort

/-!
Conjecture 5.3, degree five, of Campbell, Morales and Perales,
arXiv:2502.00254v2. Notation 5.1 uses two multiplicative convolutions and z_n.
Preregistration: docs/reports/r18-quintic-preregistration.md.
The escape witness is exactly w <= 4*u^2/15 for centered real-rooted quintics.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Zeros.Convolution.FiniteFreeCommutatorDegreeFive

open Polynomial
open scoped BigOperators
open FiniteFreeCommutatorDegreeFour

def centeredQuintic (u v w t : ℝ) : ℝ[X] :=
  X ^ 5 + C u * X ^ 3 + C v * X ^ 2 + C w * X + C t

/-- Five real linear factors, with zero and repeated roots permitted. -/
def RealRooted5 (p : ℝ[X]) : Prop :=
  ∃ r : Fin 5 → ℝ, p = ∏ i, (X - C (r i))

/-- The degree-five instance of the source's Notation 5.1. -/
def square5 (p q : ℝ[X]) : ℝ[X] :=
  multiplicativeConvolution 5
    (multiplicativeConvolution 5 (symmetrize 5 p) (symmetrize 5 q))
    (commutatorKernel 5)

private def quintic (a u v w t : ℝ) : ℝ[X] :=
  X^5 + C a * X^4 + C u * X^3 + C v * X^2 + C w * X + C t

private theorem dilate_quintic (a u v w t : ℝ) :
    dilate 5 (-1) (quintic a u v w t) = quintic (-a) u (-v) w (-t) := by
  simp [dilate, quintic]
  ring

private theorem symmetrize_quintic (a u v w t : ℝ) :
    symmetrize 5 (quintic a u v w t) =
      centeredQuintic (2*u-4*a^2/5) 0 (2*w-4*a*v/5+3*u^2/10) 0 := by
  rw [symmetrize, dilate_quintic]
  change (∑ k ∈ Finset.range (5+1),
    C ((-1)^k * ((descPochhammer ℝ k).eval 5 *
      ∑ i ∈ Finset.range (k+1),
        elementaryCoeff 5 (quintic a u v w t) i *
          elementaryCoeff 5 (quintic (-a) u (-v) w (-t)) (k-i) /
          ((descPochhammer ℝ i).eval 5 * (descPochhammer ℝ (k-i)).eval 5))) *
      X^(5-k)) = _
  ext j
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, elementaryCoeff, quintic,
    centeredQuintic, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X,
    coeff_X, coeff_X_pow, coeff_C, coeff_sum,
    descPochhammer_succ_eval, descPochhammer_zero, eval_one,
    map_zero, map_one, zero_add, add_zero, one_mul, mul_one, mul_zero, zero_mul,
    pow_zero, pow_one, ite_true, ite_false]
  split_ifs <;> first | contradiction | omega | ring

private theorem symmetrize_centered (u v w t : ℝ) :
    symmetrize 5 (centeredQuintic u v w t) =
      centeredQuintic (2*u) 0 (2*w+3*u^2/10) 0 := by
  simpa [quintic, centeredQuintic] using symmetrize_quintic 0 u v w t

private theorem multiplicative_odd (u w U W : ℝ) :
    multiplicativeConvolution 5 (centeredQuintic u 0 w 0) (centeredQuintic U 0 W 0) =
      centeredQuintic (u*U/10) 0 (w*W/5) 0 := by
  change (∑ k ∈ Finset.range (5+1), C ((-1)^k *
    (elementaryCoeff 5 (centeredQuintic u 0 w 0) k *
      elementaryCoeff 5 (centeredQuintic U 0 W 0) k / (Nat.choose 5 k : ℝ))) *
    X^(5-k)) = _
  ext j
  norm_num [Finset.sum_range_succ, elementaryCoeff, centeredQuintic,
    coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X, coeff_X_pow,
    coeff_C, coeff_sum, Nat.choose]

private theorem commutatorKernel_five :
    commutatorKernel 5 = centeredQuintic (-(125/6)) 0 (50/9) 0 := by
  ext j
  norm_num only [commutatorKernel, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceDiv, centeredQuintic,
    descPochhammer_succ_eval, descPochhammer_zero, eval_one, Nat.choose,
    coeff_sum, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow,
    coeff_C, coeff_neg, map_zero, zero_add, add_zero, one_mul, mul_one,
    mul_zero, zero_mul, pow_zero, pow_one, coeff_zero]

/-- The coefficients are expanded from Sym, both multiplicative convolutions,
and the source kernel z(5). -/
theorem centered_expansion (u v w t U V W T : ℝ) :
    square5 (centeredQuintic u v w t) (centeredQuintic U V W T) =
      X^5 - C (5*u*U/6) * X^3 + C ((3*u^2+20*w)*(3*U^2+20*W)/450) * X := by
  rw [square5, symmetrize_centered, symmetrize_centered, commutatorKernel_five,
    multiplicative_odd, multiplicative_odd]
  ext j
  norm_num only [centeredQuintic, coeff_add, coeff_sub, coeff_C_mul_X_pow,
    coeff_C_mul_X, coeff_X_pow, coeff_C, map_zero, zero_mul, add_zero, coeff_zero]
  split_ifs <;> first | omega | ring

private theorem ordered_moment_bound (a b c d e : ℝ)
    (h : a + b + c + d + e = 0)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hde : d ≤ e) :
    7 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) ^ 2 ≤
      30 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4 + e ^ 4) := by
  let A := b - a
  let B := c - b
  let C := d - c
  let D := e - d
  have hA : 0 ≤ A := sub_nonneg.mpr hab
  have hB : 0 ≤ B := sub_nonneg.mpr hbc
  have hC : 0 ≤ C := sub_nonneg.mpr hcd
  have hD : 0 ≤ D := sub_nonneg.mpr hde
  have he : e = -a - b - c - d := by linarith only [h]
  -- On the ordered-root cone the sharp quartic has nonnegative gap coefficients.
  have hid :
      30 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4 + e ^ 4) -
        7 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) ^ 2 =
      8 * (A ^ 4 + 3 * A ^ 3 * B + 2 * A ^ 3 * C + A ^ 3 * D +
        3 * A ^ 2 * B ^ 2 + 4 * A ^ 2 * B * C + 2 * A ^ 2 * B * D +
        A ^ 2 * C ^ 2 + A ^ 2 * C * D + A * B * C ^ 2 + A * B * C * D +
        A * B * D ^ 2 + 2 * A * C * D ^ 2 + A * D ^ 3 + B ^ 2 * C ^ 2 +
        B ^ 2 * C * D + B ^ 2 * D ^ 2 + 4 * B * C * D ^ 2 +
        2 * B * D ^ 3 + 3 * C ^ 2 * D ^ 2 + 3 * C * D ^ 3 + D ^ 4) := by
    dsimp [A, B, C, D]
    rw [he]
    ring
  apply sub_nonneg.mp
  rw [hid]
  positivity

/-- The preregistered sharp coefficient estimate. Equality occurs at roots
`(2,2,2,-3,-3)`, so its constant cannot be decreased. -/
theorem centered_quintic_coefficient_bound (u v w t : ℝ)
    (hp : RealRooted5 (centeredQuintic u v w t)) : w ≤ (4 / 15) * u ^ 2 := by
  obtain ⟨r, hr⟩ := hp
  let s := r ∘ Tuple.sort r
  have hs : Monotone s := Tuple.monotone_sort r
  have hprod : centeredQuintic u v w t = ∏ i, (X - C (s i)) := by
    rw [hr]
    exact (Equiv.prod_comp (Tuple.sort r) (fun i => X - C (r i))).symm
  have hc := congrArg (fun p : ℝ[X] => p.coeff 4) hprod
  have hu := congrArg (fun p : ℝ[X] => p.coeff 3) hprod
  have hw := congrArg (fun p : ℝ[X] => p.coeff 1) hprod
  norm_num [centeredQuintic, Fin.prod_univ_succ, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    coeff_add, coeff_sub, coeff_X_pow, coeff_X, coeff_C, Fin.succ] at hc hu hw
  change 0 = -s 0 + (-s 1 + (-s 2 + (-s 3 + -s 4))) at hc
  change u = -(s 0 * (-s 1 + (-s 2 + (-s 3 + -s 4)))) +
    (-(s 1 * (-s 2 + (-s 3 + -s 4))) + (-(s 2 * (-s 3 + -s 4)) + s 3 * s 4)) at hu
  change w = -(s 0 * (-(s 1 * (-(s 2 * (-s 3 + -s 4)) + s 3 * s 4)) +
    -(s 2 * (s 3 * s 4)))) + s 1 * (s 2 * (s 3 * s 4)) at hw
  have hcenter : s 0 + s 1 + s 2 + s 3 + s 4 = 0 := by linarith only [hc]
  have he : s 4 = -s 0 - s 1 - s 2 - s 3 := by linarith only [hcenter]
  have h2 : s 0 ^ 2 + s 1 ^ 2 + s 2 ^ 2 + s 3 ^ 2 + s 4 ^ 2 = -2 * u := by
    rw [hu, he]
    ring
  have h4 : s 0 ^ 4 + s 1 ^ 4 + s 2 ^ 4 + s 3 ^ 4 + s 4 ^ 4 =
      2 * u ^ 2 - 4 * w := by
    rw [hu, hw, he]
    ring
  have hb := ordered_moment_bound (s 0) (s 1) (s 2) (s 3) (s 4) hcenter
    (hs (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
  rw [h2, h4] at hb
  nlinarith only [hb]

private theorem derivative_real_rooted (u v w t : ℝ)
    (hp : RealRooted5 (centeredQuintic u v w t)) :
    RealRooted4 (centeredQuartic (3*u/5) (2*v/5) (w/5)) := by
  let q := centeredQuartic (3*u/5) (2*v/5) (w/5)
  have hderiv : (centeredQuintic u v w t).derivative = C 5 * q := by
    ext j
    by_cases hj : j ≤ 4
    · interval_cases j <;>
        norm_num [centeredQuintic, q, centeredQuartic, coeff_derivative,
          coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C_mul,
          coeff_X_pow, coeff_X, coeff_C] <;> ring
    · norm_num only [centeredQuintic, q, centeredQuartic, coeff_derivative,
        coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C_mul,
        coeff_X_pow, coeff_X, coeff_C]
      split_ifs <;> first | contradiction | omega | ring
  have hdegree : q.natDegree ≤ 4 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    simp [q, centeredQuartic, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X,
      coeff_X_pow, coeff_X, coeff_C, show j ≠ 4 by omega,
      show j ≠ 2 by omega, show 1 ≠ j by omega, show j ≠ 0 by omega]
  have hcoeff : q.coeff 4 = 1 := by
    norm_num [q, centeredQuartic, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X,
      coeff_X_pow, coeff_X, coeff_C]
  have hmonic := monic_of_natDegree_le_of_coeff_eq_one 4 hdegree hcoeff
  have hnat : q.natDegree = 4 := natDegree_eq_of_le_of_coeff_ne_zero hdegree (by
    rw [hcoeff]; norm_num)
  have hroots : (centeredQuintic u v w t).roots.card = 5 := by
    obtain ⟨r, hr⟩ := hp
    rw [hr, roots_prod _ _ (monic_prod_X_sub_C r Finset.univ).ne_zero]
    simp
  have hrolle := card_roots_le_derivative (centeredQuintic u v w t)
  rw [hroots, hderiv, roots_C_mul _ (by norm_num : (5 : ℝ) ≠ 0)] at hrolle
  have hcard : q.roots.card = 4 := by have := q.card_roots'; omega
  have hfactor := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic
    (hcard.trans hnat.symm)
  obtain ⟨a, b, c, d, habcd⟩ := Multiset.card_eq_four.mp hcard
  refine ⟨![a, b, c, d], ?_⟩
  change q = _
  rw [← hfactor, habcd]
  simp [Fin.prod_univ_succ]

/-- Rolle supplies the lower bound from the frozen quartic theorem; the new
sharp estimate supplies the stronger upper bound needed by the discriminant. -/
theorem centered_quintic_invariant_bounds (u v w t : ℝ)
    (hp : RealRooted5 (centeredQuintic u v w t)) :
    u ≤ 0 ∧ 0 ≤ 3*u^2+20*w ∧ 3*u^2+20*w ≤ 25*u^2/3 := by
  obtain ⟨hu, hlo, -⟩ := centered_quartic_invariant_bounds (3*u/5) (2*v/5) (w/5)
    (derivative_real_rooted u v w t hp)
  have hhi := centered_quintic_coefficient_bound u v w t hp
  constructor
  · linarith only [hu]
  constructor <;> nlinarith only [hlo, hhi]

/-- The requested quantitative discriminant lower bound, including degenerate inputs. -/
theorem centered_discriminant_bound (u v w t U V W T : ℝ)
    (hp : RealRooted5 (centeredQuintic u v w t))
    (hq : RealRooted5 (centeredQuintic U V W T)) :
    25*u^2*U^2/324 ≤ (5*u*U/6)^2 -
      4*((3*u^2+20*w)*(3*U^2+20*W)/450) := by
  obtain ⟨-, hi, hib⟩ := centered_quintic_invariant_bounds u v w t hp
  obtain ⟨-, hj, hjb⟩ := centered_quintic_invariant_bounds U V W T hq
  have hrem : (5*u*U/6)^2 - 4*((3*u^2+20*w)*(3*U^2+20*W)/450) -
      25*u^2*U^2/324 =
      2/225 * ((25*u^2/3)*(25*U^2/3-(3*U^2+20*W)) +
        (3*U^2+20*W)*(25*u^2/3-(3*u^2+20*w))) := by ring
  have hnonneg : 0 ≤ 2/225 * ((25*u^2/3)*(25*U^2/3-(3*U^2+20*W)) +
      (3*U^2+20*W)*(25*u^2/3-(3*u^2+20*w))) :=
    mul_nonneg (by norm_num) (add_nonneg
      (mul_nonneg (by positivity) (sub_nonneg.mpr hjb))
      (mul_nonneg hj (sub_nonneg.mpr hib)))
  linarith only [hrem, hnonneg]

/-- The commutator is X times two quadratics with nonnegative squared roots. -/
theorem centered_factorization (u v w t U V W T : ℝ)
    (hp : RealRooted5 (centeredQuintic u v w t))
    (hq : RealRooted5 (centeredQuintic U V W T)) :
    ∃ s t' : ℝ, 0 ≤ s ∧ 0 ≤ t' ∧
      square5 (centeredQuintic u v w t) (centeredQuintic U V W T) =
        X * (X^2-C s) * (X^2-C t') := by
  obtain ⟨hu, hi, -⟩ := centered_quintic_invariant_bounds u v w t hp
  obtain ⟨hU, hj, -⟩ := centered_quintic_invariant_bounds U V W T hq
  let A := 5*u*U/6
  let B := (3*u^2+20*w)*(3*U^2+20*W)/450
  let D := A^2-4*B
  have hA : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg
      (mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hu) hU)
      (by norm_num)
  have hB : 0 ≤ B := div_nonneg (mul_nonneg hi hj) (by norm_num)
  have hD : 0 ≤ D := le_trans (by positivity)
    (centered_discriminant_bound u v w t U V W T hp hq)
  have hsqrt : Real.sqrt D ≤ A := Real.sqrt_le_iff.mpr ⟨hA, by dsimp [D]; linarith⟩
  let s := (A+Real.sqrt D)/2
  let t' := (A-Real.sqrt D)/2
  have hsum : s+t' = A := by dsimp [s, t']; ring
  have hprod : s*t' = B := by
    have hsquare := Real.sq_sqrt hD
    dsimp [s, t']
    dsimp [D] at hsquare
    nlinarith only [hsquare]
  refine ⟨s, t', div_nonneg (add_nonneg hA (Real.sqrt_nonneg _)) (by norm_num),
    div_nonneg (sub_nonneg.mpr hsqrt) (by norm_num), ?_⟩
  rw [centered_expansion]
  change X^5-C A*X^3+C B*X = _
  rw [← hsum, ← hprod]
  simp only [map_add, map_mul]
  ring

/-- Five explicit real roots: zero and two opposite pairs, with all multiplicities retained. -/
theorem centered_real_rooted (u v w t U V W T : ℝ)
    (hp : RealRooted5 (centeredQuintic u v w t))
    (hq : RealRooted5 (centeredQuintic U V W T)) :
    RealRooted5 (square5 (centeredQuintic u v w t) (centeredQuintic U V W T)) := by
  obtain ⟨s, t', hs, ht, hfactor⟩ := centered_factorization u v w t U V W T hp hq
  refine ⟨![0, Real.sqrt s, -Real.sqrt s, Real.sqrt t', -Real.sqrt t'], ?_⟩
  rw [hfactor]
  have hsC : (C (Real.sqrt s) : ℝ[X])^2 = C s := by rw [← map_pow, Real.sq_sqrt hs]
  have htC : (C (Real.sqrt t') : ℝ[X])^2 = C t' := by rw [← map_pow, Real.sq_sqrt ht]
  calc
    X*(X^2-C s)*(X^2-C t') =
        X*(X^2-(C (Real.sqrt s))^2)*(X^2-(C (Real.sqrt t'))^2) := by rw [hsC, htC]
    _ = _ := by simp [Fin.prod_univ_succ]; ring

private theorem exists_quintic (p : ℝ[X]) (hp : RealRooted5 p) :
    ∃ a u v w t : ℝ, p = quintic a u v w t := by
  obtain ⟨r, hr⟩ := hp
  have hm : p.Monic := hr ▸ monic_prod_X_sub_C r Finset.univ
  have hn : p.natDegree = 5 := by
    rw [hr, natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (r i))]
    simp
  have hc : p.coeff 5 = 1 := by rw [← hn]; exact hm.coeff_natDegree
  refine ⟨p.coeff 4, p.coeff 3, p.coeff 2, p.coeff 1, p.coeff 0, ?_⟩
  calc
    p = ∑ i ∈ Finset.range (5+1), C (p.coeff i)*X^i :=
      p.as_sum_range_C_mul_X_pow' (by omega)
    _ = _ := by norm_num [Finset.sum_range_succ, hc, quintic]; ring

private theorem quintic_translate (a u v w t c : ℝ) :
    (quintic a u v w t).comp (X+C c) =
      quintic (a+5*c) (u+4*a*c+10*c^2) (v+3*u*c+6*a*c^2+10*c^3)
        (w+2*v*c+3*u*c^2+4*a*c^3+5*c^4)
        (t+w*c+v*c^2+u*c^3+a*c^4+c^5) := by
  simp [quintic, map_add, map_mul, map_pow, map_ofNat]
  ring

private theorem real_rooted_translate (p : ℝ[X]) (hp : RealRooted5 p) (c : ℝ) :
    RealRooted5 (p.comp (X+C c)) := by
  obtain ⟨r, hr⟩ := hp
  refine ⟨fun i => r i-c, ?_⟩
  rw [hr, Polynomial.prod_comp]
  apply Finset.prod_congr rfl
  intro i _
  simp [map_sub]
  ring

private theorem symmetrize_translate_quintic (a u v w t c : ℝ) :
    symmetrize 5 ((quintic a u v w t).comp (X+C c)) =
      symmetrize 5 (quintic a u v w t) := by
  rw [quintic_translate, symmetrize_quintic, symmetrize_quintic]
  congr 1 <;> ring

private theorem centered_translate (a u v w t : ℝ) :
    (quintic a u v w t).comp (X+C (-a/5)) =
      centeredQuintic (u-2*a^2/5) (v-3*a*u/5+4*a^3/25)
        (w-2*a*v/5+3*a^2*u/25-3*a^4/125)
        (t-a*w/5+a^2*v/25-a^3*u/125+4*a^5/3125) := by
  rw [quintic_translate]
  have ha : a+5*(-a/5) = 0 := by ring
  rw [ha]
  ext j
  norm_num only [quintic, centeredQuintic, coeff_add, coeff_C_mul_X_pow,
    coeff_C_mul_X, coeff_X_pow, coeff_C, map_zero, zero_mul, add_zero, coeff_zero]
  split_ifs <;> first | contradiction | omega | ring

/-- Conjecture 5.3 for every pair in P_5(R). No centering, simplicity of roots,
or factorization assumption from Theorem 5.6 is required. -/
theorem real_rooted (p q : ℝ[X]) (hp : RealRooted5 p) (hq : RealRooted5 q) :
    RealRooted5 (square5 p q) := by
  obtain ⟨a, u, v, w, t, rfl⟩ := exists_quintic p hp
  obtain ⟨A, U, V, W, T, rfl⟩ := exists_quintic q hq
  have hp' := real_rooted_translate (quintic a u v w t) hp (-a/5)
  have hq' := real_rooted_translate (quintic A U V W T) hq (-A/5)
  rw [centered_translate] at hp' hq'
  have hout := centered_real_rooted _ _ _ _ _ _ _ _ hp' hq'
  rw [← centered_translate, ← centered_translate] at hout
  simpa only [square5, symmetrize_translate_quintic] using hout

example : RealRooted5 (centeredQuintic (-15) 10 60 (-72)) := by
  refine ⟨![2, 2, 2, -3, -3], ?_⟩
  norm_num [centeredQuintic, Fin.prod_univ_succ, map_ofNat]
  ring

example : (60 : ℝ) = (4 / 15) * (-15) ^ 2 := by norm_num

#print axioms centered_quintic_coefficient_bound
#print axioms centered_quintic_invariant_bounds
#print axioms centered_expansion
#print axioms centered_discriminant_bound
#print axioms centered_factorization
#print axioms centered_real_rooted
#print axioms real_rooted

end D5.S3.Zeros.Convolution.FiniteFreeCommutatorDegreeFive
