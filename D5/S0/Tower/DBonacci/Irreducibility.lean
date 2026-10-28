/- GID: D5/S0/Tower/DBonacci/Irreducibility
   generality: I
   mirror-B: D5/B/S0/Tower/DBonacci/Irreducibility
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Simple Perron root, unit-disc root location, and multinacci irreducibility. -/

import D5.S0.Tower.DBonacci.PerronRoot
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S0.Tower.DBonacci.PerronRoot

open Polynomial
open scoped BigOperators

/- Equality in the relevant reverse triangle inequality, proved with squares.
   In particular this also works when norm z = 1. -/
private lemma eq_of_norm_two_sub (z : ℂ)
    (h : ‖(2 : ℂ) - z‖ = 2 - ‖z‖) : z = (‖z‖ : ℂ) := by
  have hz := Complex.sq_norm_sub_sq_re z
  have hw : ‖(2 : ℂ) - z‖ ^ 2 - (2 - z.re) ^ 2 = z.im ^ 2 := by
    simpa using Complex.sq_norm_sub_sq_re ((2 : ℂ) - z)
  rw [h] at hw
  have hre : z.re = ‖z‖ := by nlinarith
  have himsq : z.im ^ 2 = 0 := by nlinarith
  have him : z.im = 0 := (sq_eq_zero_iff).mp himsq
  apply Complex.ext
  · simpa using hre
  · simpa using him

private lemma root_equation_eq_perron (q : ℕ) (hq : 2 ≤ q) (z : ℂ)
    (hz : z ^ q = ∑ i ∈ Finset.range q, z ^ i)
    (hone : 1 ≤ ‖z‖) : z = (dbonacciPerronRoot q : ℂ) := by
  let r : ℝ := ‖z‖
  have hrone : 1 ≤ r := hone
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hrone
  have hrpow : 0 < r ^ q := pow_pos hrpos q
  have hbpos : 0 < dbonacciPerronRoot q :=
    lt_trans zero_lt_one (one_lt_dbonacciPerronRoot q hq)
  have htriangle : r ^ q ≤ ∑ i ∈ Finset.range q, r ^ i := by
    calc
      r ^ q = ‖z ^ q‖ := (norm_pow z q).symm
      _ = ‖∑ i ∈ Finset.range q, z ^ i‖ := congrArg norm hz
      _ ≤ ∑ i ∈ Finset.range q, ‖z ^ i‖ := norm_sum_le _ _
      _ = ∑ i ∈ Finset.range q, r ^ i := by simp only [norm_pow, r]
  have hrrec : 1 ≤ dbonacciReciprocalSum q r := by
    have hid := pow_mul_dbonacciReciprocalSum q (ne_of_gt hrpos)
    nlinarith
  have hrle : r ≤ dbonacciPerronRoot q := by
    by_contra hn
    have hlt : dbonacciReciprocalSum q r <
        dbonacciReciprocalSum q (dbonacciPerronRoot q) :=
      dbonacci_reciprocalSum_strictAntiOn q (by omega)
        hbpos hrpos (lt_of_not_ge hn)
    rw [dbonacciPerronRoot_reciprocalSum q hq] at hlt
    exact (not_lt_of_ge hrrec) hlt
  have hproduct : z ^ q * (2 - z) = 1 := by
    have hg := geom_sum_mul z q
    rw [← hz] at hg
    linear_combination -hg
  have hnorm : r ^ q * ‖(2 : ℂ) - z‖ = 1 := by
    simpa only [norm_mul, norm_pow, norm_one] using congrArg norm hproduct
  have hreverse : 2 - r ≤ ‖(2 : ℂ) - z‖ := by
    simpa [r] using norm_sub_norm_le (2 : ℂ) z
  have hrne : r ≠ 1 := by
    intro hr
    have hn : ‖(2 : ℂ) - z‖ = 1 := by simpa [hr] using hnorm
    have heq : z = (‖z‖ : ℂ) :=
      eq_of_norm_two_sub z (by change ‖(2 : ℂ) - z‖ = 2 - r; linarith)
    have hz1 : z = 1 := by simpa [show ‖z‖ = 1 from hr] using heq
    have hqcast : (1 : ℂ) = q := by simpa [hz1] using hz
    have hqnat : (1 : ℕ) = q := by exact_mod_cast hqcast
    omega
  have hrgt : 1 < r := lt_of_le_of_ne hrone hrne.symm
  have hreq : r = dbonacciPerronRoot q := by
    apply le_antisymm hrle
    by_contra hn
    have hlt : r < dbonacciPerronRoot q := lt_of_not_ge hn
    have hrec : 1 < dbonacciReciprocalSum q r := by
      have ha := dbonacci_reciprocalSum_strictAntiOn q (by omega)
        hrpos hbpos hlt
      rwa [dbonacciPerronRoot_reciprocalSum q hq] at ha
    have hchar : r ^ q < ∑ i ∈ Finset.range q, r ^ i := by
      calc
        r ^ q = r ^ q * 1 := (mul_one _).symm
        _ < r ^ q * dbonacciReciprocalSum q r :=
          mul_lt_mul_of_pos_left hrec hrpow
        _ = ∑ i ∈ Finset.range q, r ^ i :=
          pow_mul_dbonacciReciprocalSum q (ne_of_gt hrpos)
    have hg := geom_sum_mul r q
    have hm := mul_lt_mul_of_pos_right hchar (sub_pos.mpr hrgt)
    have hlarge : 1 < r ^ q * (2 - r) := by nlinarith
    have hsmall := mul_le_mul_of_nonneg_left hreverse hrpow.le
    rw [hnorm] at hsmall
    exact (not_lt_of_ge hsmall) hlarge
  have hbproduct : r ^ q * (2 - r) = 1 := by
    rw [hreq]
    have hb := dbonacciPerronRoot_nontrivial_equation q hq
    rw [pow_succ] at hb
    nlinarith
  have hnormeq : ‖(2 : ℂ) - z‖ = 2 - r :=
    mul_left_cancel₀ (ne_of_gt hrpow) (hnorm.trans hbproduct.symm)
  have heq := eq_of_norm_two_sub z hnormeq
  change z = (r : ℂ) at heq
  rwa [hreq] at heq

/-- For every q ≥ 2, every complex root other than the exact existing Perron
    root lies in the open unit disk. -/
theorem dbonacci_complex_root_location (q : ℕ) (hq : 2 ≤ q) {z : ℂ}
    (hz : (X ^ q - ∑ i ∈ Finset.range q, X ^ i : ℂ[X]).IsRoot z) :
    1 ≤ ‖z‖ ↔ z = (dbonacciPerronRoot q : ℂ) := by
  constructor
  · intro hone
    apply root_equation_eq_perron q hq z _ hone
    simpa only [IsRoot, eval_sub, eval_pow, eval_X, eval_finsetSum,
      sub_eq_zero] using hz
  · rintro rfl
    have hp : 0 < dbonacciPerronRoot q :=
      lt_trans zero_lt_one (one_lt_dbonacciPerronRoot q hq)
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp] using
      (one_lt_dbonacciPerronRoot q hq).le

/- Literal Euler identity. The subtraction below is subtraction in R, not
   natural subtraction. This proof does not assume irreducibility. -/
private lemma weighted_derivative {R : Type*} [CommRing R]
    (q : ℕ) (x : R) (hx : x ^ q = ∑ i ∈ Finset.range q, x ^ i) :
    x * (X ^ q - ∑ i ∈ Finset.range q, X ^ i : R[X]).derivative.eval x =
      ∑ i ∈ Finset.range q, ((q : R) - (i : R)) * x ^ i := by
  have heuler (n : ℕ) :
      x * (X ^ n : R[X]).derivative.eval x = (n : R) * x ^ n := by
    cases n with
    | zero => simp
    | succ n =>
      rw [derivative_X_pow]
      simp only [eval_mul, eval_C, eval_pow, eval_X, Nat.add_sub_cancel,
        Nat.cast_add, Nat.cast_one, pow_succ]
      ring
  calc
    x * (X ^ q - ∑ i ∈ Finset.range q, X ^ i : R[X]).derivative.eval x =
        (q : R) * x ^ q - ∑ i ∈ Finset.range q, (i : R) * x ^ i := by
      simp only [derivative_sub, derivative_sum, eval_sub, eval_finsetSum,
        mul_sub, Finset.mul_sum]
      rw [heuler q]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact heuler i
    _ = (q : R) * (∑ i ∈ Finset.range q, x ^ i) -
        ∑ i ∈ Finset.range q, (i : R) * x ^ i := by rw [hx]
    _ = ∑ i ∈ Finset.range q, ((q : R) - (i : R)) * x ^ i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The chosen complex Perron root is a root and its formal derivative is
    nonzero; hence its multiplicity is exactly one. -/
theorem dbonacciPerronRoot_simple (q : ℕ) (hq : 2 ≤ q) :
    (X ^ q - ∑ i ∈ Finset.range q, X ^ i : ℂ[X]).IsRoot
        (dbonacciPerronRoot q : ℂ) ∧
      (X ^ q - ∑ i ∈ Finset.range q, X ^ i : ℂ[X]).derivative.eval
        (dbonacciPerronRoot q : ℂ) ≠ 0 := by
  have hb : 0 < dbonacciPerronRoot q :=
    lt_trans zero_lt_one (one_lt_dbonacciPerronRoot q hq)
  have hroot : (dbonacciPerronRoot q : ℂ) ^ q =
      ∑ i ∈ Finset.range q, (dbonacciPerronRoot q : ℂ) ^ i := by
    exact_mod_cast dbonacciPerronRoot_characteristic q hq
  have hpositive : 0 < ∑ i ∈ Finset.range q,
      ((q : ℝ) - (i : ℝ)) * dbonacciPerronRoot q ^ i := by
    apply Finset.sum_pos'
    · intro i hi
      have hiq : (i : ℝ) < (q : ℝ) := by
        exact_mod_cast Finset.mem_range.mp hi
      exact mul_nonneg (sub_nonneg.mpr hiq.le) (pow_nonneg hb.le i)
    · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
      have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
      simpa using hqpos
  have hnonzero : (∑ i ∈ Finset.range q,
      ((q : ℂ) - (i : ℂ)) * (dbonacciPerronRoot q : ℂ) ^ i) ≠ 0 := by
    have hc : (((∑ i ∈ Finset.range q,
        ((q : ℝ) - (i : ℝ)) * dbonacciPerronRoot q ^ i) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hpositive)
    simpa only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_sub,
      Complex.ofReal_natCast, Complex.ofReal_pow] using hc
  refine ⟨?_, ?_⟩
  · simpa only [IsRoot, eval_sub, eval_pow, eval_X, eval_finsetSum,
      sub_eq_zero] using hroot
  · intro hderivative
    have he := weighted_derivative q (dbonacciPerronRoot q : ℂ) hroot
    rw [hderivative, mul_zero] at he
    exact hnonzero he.symm

private lemma norm_product_lt_one (s : Multiset ℂ) (hs : s ≠ 0)
    (h : ∀ z ∈ s, ‖z‖ < 1) : ‖s.prod‖ < 1 := by
  revert hs h
  induction s using Multiset.induction_on with
  | empty =>
    intro hs _
    exact (hs rfl).elim
  | @cons z s ih =>
    intro _ h
    have hz : ‖z‖ < 1 := h z (Multiset.mem_cons_self _ _)
    rw [Multiset.prod_cons, norm_mul]
    by_cases he : s = 0
    · simpa [he] using hz
    · have ht : ‖s.prod‖ < 1 :=
        ih he (fun w hw => h w (Multiset.mem_cons_of_mem hw))
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left ht.le (norm_nonneg z))
        (by simpa using hz)

/- A monic integer polynomial with nonzero constant and all roots strictly
   inside the unit disk is constant. The roots multiset retains multiplicities. -/
private lemma monic_factor_eq_one_of_roots_small (G : ℤ[X]) (hG : G.Monic)
    (hconstant : G.coeff 0 ≠ 0)
    (hroots : ∀ z ∈ (G.map (algebraMap ℤ ℂ)).roots, ‖z‖ < 1) : G = 1 := by
  by_contra hG1
  let Gc : ℂ[X] := G.map (algebraMap ℤ ℂ)
  have hsplit : Gc.Splits := IsAlgClosed.splits Gc
  have hmonic : Gc.Monic := hG.map (algebraMap ℤ ℂ)
  have hdegree : 0 < Gc.natDegree := by
    change 0 < (G.map (algebraMap ℤ ℂ)).natDegree
    rw [natDegree_map_eq_of_injective (algebraMap ℤ ℂ).injective_int]
    exact Nat.pos_of_ne_zero (fun hn => hG1 (hG.natDegree_eq_zero.mp hn))
  have hnonempty : Gc.roots ≠ 0 := by
    intro he
    have hd := hsplit.natDegree_eq_card_roots
    rw [he] at hd
    simp only [Multiset.card_zero] at hd
    omega
  have hproduct : ‖Gc.roots.prod‖ < 1 :=
    norm_product_lt_one Gc.roots hnonempty hroots
  have hcoeff := hsplit.coeff_zero_eq_prod_roots_of_monic hmonic
  have hnorm : ‖(G.coeff 0 : ℂ)‖ < 1 := by
    calc
      ‖(G.coeff 0 : ℂ)‖ = ‖Gc.coeff 0‖ := by simp [Gc]
      _ = ‖(-1 : ℂ) ^ Gc.natDegree * Gc.roots.prod‖ := congrArg norm hcoeff
      _ = ‖Gc.roots.prod‖ := by
        simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      _ < 1 := hproduct
  rw [Complex.norm_intCast] at hnorm
  have hint : |G.coeff 0| < (1 : ℤ) := by exact_mod_cast hnorm
  have hbounds := abs_lt.mp hint
  have hzero : G.coeff 0 = 0 := by omega
  exact hconstant hzero

/-- Uniform multinacci irreducibility over ℤ and ℚ for every q ≥ 2.
    The ℚ clause is transferred by the existing Gauss lemma, with no
    separately retained public alias. -/
theorem dbonacci_irreducible (q : ℕ) (hq : 2 ≤ q) :
    Irreducible (X ^ q - ∑ i ∈ Finset.range q, X ^ i : ℤ[X]) ∧
      Irreducible (X ^ q - ∑ i ∈ Finset.range q, X ^ i : ℚ[X]) := by
  let P : ℤ[X] := X ^ q - ∑ i ∈ Finset.range q, X ^ i
  let σ : ℤ →+* ℂ := algebraMap ℤ ℂ
  have hPmonic : P.Monic := by
    apply monic_X_pow_sub
    simpa only [Fin.sum_univ_eq_sum_range, map_one, one_mul] using
      (degree_sum_fin_lt (fun _ : Fin q => (1 : ℤ)))
  have hPconstant : P.coeff 0 = -1 := by
    have hq0 : q ≠ 0 := by omega
    have hsum : (∑ i ∈ Finset.range q, (0 : ℤ) ^ i) = 1 := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro i _ hi
        simp [hi]
      · intro hn
        exact (hn (Finset.mem_range.mpr (by omega))).elim
    change (X ^ q - ∑ i ∈ Finset.range q, X ^ i : ℤ[X]).coeff 0 = -1
    rw [coeff_zero_eq_eval_zero]
    simpa only [eval_sub, eval_pow, eval_X, eval_finsetSum,
      zero_pow hq0, hsum, zero_sub]
  have hP1 : P ≠ 1 := by
    intro he
    have hc := congrArg (fun p : ℤ[X] => p.coeff 0) he
    rw [hPconstant] at hc
    norm_num at hc
  have hmapP : P.map σ = (X ^ q - ∑ i ∈ Finset.range q, X ^ i : ℂ[X]) := by
    simp only [P, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_sum,
      Polynomial.map_X]
  have hbeta := dbonacciPerronRoot_simple q hq
  have hZ : Irreducible P := by
    apply (Polynomial.irreducible_of_monic hPmonic hP1).mpr
    intro A B hA hB hAB
    have hconstant : A.coeff 0 * B.coeff 0 = -1 := by
      have hc := congrArg (fun p : ℤ[X] => p.coeff 0) hAB
      simpa only [mul_coeff_zero, hPconstant] using hc
    have hAconstant : A.coeff 0 ≠ 0 := by
      intro he
      rw [he, zero_mul] at hconstant
      norm_num at hconstant
    have hBconstant : B.coeff 0 ≠ 0 := by
      intro he
      rw [he, mul_zero] at hconstant
      norm_num at hconstant
    have hmapAB : A.map σ * B.map σ =
        (X ^ q - ∑ i ∈ Finset.range q, X ^ i : ℂ[X]) := by
      rw [← Polynomial.map_mul, hAB, hmapP]
    have hbetaproduct : (A.map σ).eval (dbonacciPerronRoot q : ℂ) *
        (B.map σ).eval (dbonacciPerronRoot q : ℂ) = 0 := by
      rw [← eval_mul, hmapAB]
      exact hbeta.1
    have hnotboth : ¬ ((A.map σ).eval (dbonacciPerronRoot q : ℂ) = 0 ∧
        (B.map σ).eval (dbonacciPerronRoot q : ℂ) = 0) := by
      rintro ⟨ha, hb⟩
      have he := congrArg (fun p : ℂ[X] =>
        p.derivative.eval (dbonacciPerronRoot q : ℂ)) hmapAB
      rw [derivative_mul, eval_add, eval_mul, eval_mul, ha, hb,
        mul_zero, zero_mul, add_zero] at he
      exact hbeta.2 he.symm
    have factor_one (G : ℤ[X]) (hG : G.Monic) (hGconstant : G.coeff 0 ≠ 0)
        (hdiv : G ∣ P)
        (hGn : (G.map σ).eval (dbonacciPerronRoot q : ℂ) ≠ 0) : G = 1 := by
      apply monic_factor_eq_one_of_roots_small G hG hGconstant
      intro z hz
      have hGz : (G.map σ).eval z = 0 := isRoot_of_mem_roots hz
      obtain ⟨K, hK⟩ := hdiv
      have hPz : (P.map σ).IsRoot z := by
        change (P.map σ).eval z = 0
        rw [hK, Polynomial.map_mul, eval_mul, hGz, zero_mul]
      rw [hmapP] at hPz
      by_contra hn
      have heq := (dbonacci_complex_root_location q hq hPz).mp (le_of_not_gt hn)
      rw [heq] at hGz
      exact hGn hGz
    rcases mul_eq_zero.mp hbetaproduct with ha | hb
    · right
      apply factor_one B hB hBconstant (by rw [← hAB]; exact dvd_mul_left B A)
      intro hb
      exact hnotboth ⟨ha, hb⟩
    · left
      apply factor_one A hA hAconstant (by rw [← hAB]; exact dvd_mul_right A B)
      intro ha
      exact hnotboth ⟨ha, hb⟩
  refine ⟨hZ, ?_⟩
  have hQ : Irreducible (P.map (algebraMap ℤ ℚ)) :=
    (hPmonic.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp hZ
  simpa only [P, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_sum,
    Polynomial.map_X] using hQ

end D5.S0.Tower.DBonacci.PerronRoot
