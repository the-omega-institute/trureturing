/- GID: D5/S3/Arith/InterlaceFan/Cyclotomic
   generality: G
   mirror-B: D5/B/S3/Arith/InterlaceFan/Cyclotomic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex, mathlib/module/Mathlib.NumberTheory.Cyclotomic.Basic, mathlib/module/Mathlib.RingTheory.Polynomial.Cyclotomic.Roots, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Cosine evaluation, order-class propagation, and Ramanujan witnesses for the interlace fan. -/

import D5.S3.Arith.InterlaceFan.Defs
import D5.S3.Analytic.Certified.FiniteRamanujanDivisorIdentity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic

noncomputable section

open Finset Polynomial
open scoped BigOperators Nat Real Classical

namespace D5.S3.Arith.InterlaceFan.Cyclotomic

open D5.S3.Arith.InterlaceFan.Defs
open D5.S3.Analytic.Certified.FiniteRamanujanDivisorIdentity

/- The real evaluation of the palindromic Fourier polynomial at the j-th
   root.  Writing it as a real sum keeps the sigma-coordinate convention
   explicit and avoids a hidden choice of the middle coefficient. -/
def evalCos (n j : ℕ) (x : Fin (n / 2) → ℝ) : ℝ :=
  ∑ k : Fin (n / 2), 2 * Real.cos (2 * Real.pi * j * ((k : ℕ) + 1) / n) * x k

/- The factor two in `evalCos` is the pair of reciprocal monomials; `I` is
   the negative half of this real evaluation. -/
theorem I_eq_eval (n j : ℕ) (x : Fin (n / 2) → ℝ) :
    I n j x = -(1 / 2 : ℝ) * evalCos n j x := by
  simp only [I, evalCos]
  change (∑ k : Fin (n / 2),
      -Real.cos (2 * Real.pi * j * ((k : ℕ) + 1) / n) * x k) =
    (-(1 / 2 : ℝ)) • ∑ k : Fin (n / 2),
      2 * Real.cos (2 * Real.pi * j * ((k : ℕ) + 1) / n) * x k
  rw [Finset.smul_sum (s := (Finset.univ : Finset (Fin (n / 2))))]
  simp only [smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring


/-- The reciprocal polynomial in the pinned sigma coordinates. -/
def sigmaPoly {R : Type*} [CommRing R] (n : ℕ) (x : Fin (n / 2) → R) : R[X] :=
  ∑ k : Fin (n / 2), Polynomial.C (x k) *
    (Polynomial.X ^ ((k : ℕ) + 1) + Polynomial.X ^ (n - ((k : ℕ) + 1)))

/-- The standard primitive root of unity. -/
def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

private lemma zeta_pow (n j m : ℕ) :
    (zeta n ^ j) ^ m = Complex.exp
      ((2 * Real.pi * j * m / n : ℝ) * Complex.I) := by
  simp only [zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private lemma reciprocal_pair (n j m : ℕ) (hn : 0 < n) (hm : m ≤ n) :
    (zeta n ^ j) ^ m + (zeta n ^ j) ^ (n - m) =
      (2 * Real.cos (2 * Real.pi * j * m / n) : ℝ) := by
  have hz := Complex.isPrimitiveRoot_exp n hn.ne'
  have hz0 : zeta n ^ j ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
  have hzn : (zeta n ^ j) ^ n = 1 := by
    rw [← pow_mul, mul_comm j n, pow_mul]
    simpa [zeta] using congrArg (fun z : ℂ => z ^ j) hz.pow_eq_one
  rw [pow_sub₀ _ hz0 hm, hzn, one_mul, zeta_pow, ← Complex.exp_neg]
  have hc := Complex.two_cos ((2 * Real.pi * j * m / n : ℝ) : ℂ)
  push_cast at hc ⊢
  rw [show -((2 * (Real.pi : ℂ) * j * m / n) * Complex.I) =
    -(2 * (Real.pi : ℂ) * j * m / n) * Complex.I by ring]
  simpa using hc.symm

/-- Evaluation of the reciprocal polynomial is the real cosine sum. -/
theorem I_eq_eval_poly (n j : ℕ) (x : Fin (n / 2) → ℝ) :
    ((sigmaPoly n x).map Complex.ofRealHom).eval (zeta n ^ j) =
      (evalCos n j x : ℂ) := by
  classical
  simp only [sigmaPoly, Polynomial.map_sum, Polynomial.eval_finsetSum,
    Polynomial.map_mul, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, evalCos,
    Complex.ofReal_sum, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hklt := k.isLt
  rw [reciprocal_pair n j ((k : ℕ) + 1) (by omega) (by omega)]
  simp only [Complex.ofRealHom_eq_coe]
  push_cast
  ring

private lemma primitive_orderClass (n d j : ℕ) (hn : 0 < n)
    (hj : j ∈ orderClass n d) : IsPrimitiveRoot (zeta n ^ j) d := by
  have hd := (Finset.mem_filter.mp hj).2
  rw [← hd]
  exact (Complex.isPrimitiveRoot_exp n hn.ne').pow_div_gcd j
    (Nat.ne_of_gt (Nat.gcd_pos_of_pos_left j hn))

/-- Rational values propagate across every primitive-root order class. -/
theorem rational_const_on_orderClass (n d : ℕ) (hn : 0 < n) (hd : d ∣ n)
    (x : Fin (n / 2) → ℝ) (hx : IsRationalPt x) (c : ℚ)
    (s t : ℕ) (hs : s ∈ orderClass n d) (ht : t ∈ orderClass n d)
    (hcs : I n s x = (c : ℝ)) : I n t x = (c : ℝ) := by
  classical
  choose q hq using hx
  have hpmap : (sigmaPoly n q).map (algebraMap ℚ ℂ) =
      (sigmaPoly n x).map Complex.ofRealHom := by
    simp only [sigmaPoly, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_add,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hq k]
    simp
  have he (j : ℕ) : aeval (zeta n ^ j) (sigmaPoly n q) =
      (evalCos n j x : ℂ) := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hpmap]
    exact I_eq_eval_poly n j x
  have hEs : evalCos n s x = -2 * (c : ℝ) := by
    have := I_eq_eval n s x
    linarith
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hn
  have hdiv : cyclotomic d ℚ ∣ sigmaPoly n q - Polynomial.C (-2 * c) := by
    rw [cyclotomic_eq_minpoly_rat (primitive_orderClass n d s hn hs) hdpos]
    apply minpoly.dvd ℚ (zeta n ^ s)
    simp [he, hEs]
  have hroot : aeval (zeta n ^ t) (cyclotomic d ℚ) = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic]
    exact (primitive_orderClass n d t hn ht).isRoot_cyclotomic hdpos
  have hz := Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hdiv hroot
  rw [map_sub, he] at hz
  have hEt : evalCos n t x = -2 * (c : ℝ) := by
    have hreal := congrArg Complex.re hz
    have hr : evalCos n t x + 2 * (c : ℝ) = 0 := by simpa using hreal
    linarith
  rw [I_eq_eval, hEt]
  ring

private lemma ramanujan_integer (d k : ℕ) (hd : 0 < d) :
    ∃ a : ℤ, ramanujanSum d k = (a : ℂ) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    classical
    let S := d.divisors.erase d
    have he (e : ℕ) (he : e ∈ S) : ∃ a : ℤ, ramanujanSum e k = (a : ℂ) := by
      have heD := Finset.mem_of_mem_erase he
      have hene := Finset.ne_of_mem_erase he
      have hed := (Nat.mem_divisors.mp heD).1
      exact ih e (lt_of_le_of_ne (Nat.le_of_dvd hd hed) hene)
        (Nat.pos_of_dvd_of_pos hed hd)
    let a (e : ℕ) : ℤ := if h : e ∈ S then (he e h).choose else 0
    have ha : (∑ e ∈ S, ramanujanSum e k) = ((∑ e ∈ S, a e : ℤ) : ℂ) := by
      push_cast
      apply sum_congr rfl
      intro e heS
      exact (he e heS).choose_spec.trans (by simp [a, heS])
    have hsum : (∑ e ∈ S, ramanujanSum e k) + ramanujanSum d k =
        if d ∣ k then (d : ℂ) else 0 := by
      rw [show S = d.divisors.erase d from rfl,
        Finset.sum_erase_add _ _ (Nat.mem_divisors.mpr ⟨dvd_refl d, hd.ne'⟩)]
      exact sum_ramanujanSum_divisors d k hd
    refine ⟨(if d ∣ k then (d : ℤ) else 0) - ∑ e ∈ S, a e, ?_⟩
    push_cast
    rw [ha] at hsum
    push_cast at hsum
    split_ifs at hsum ⊢ <;> linear_combination hsum

private lemma ramanujan_pow_sum (d k : ℕ) :
    ramanujanSum d k = ∑ a ∈ (range d).filter (fun a => a.Coprime d),
      (zeta d ^ a) ^ k := by
  apply sum_congr rfl
  intro a ha
  simp only [zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private lemma geometric_period (n : ℕ) (z : ℂ) (hz : z ^ n = 1) :
    ∑ k ∈ range n, z ^ k = if z = 1 then (n : ℂ) else 0 := by
  classical
  by_cases h : z = 1
  · simp [h]
  · rw [if_neg h, geom_sum_eq h, hz, sub_self, zero_div]

private lemma ramanujan_fourier (n d : ℕ) (hn : 0 < n) (hd : d ∣ n)
    (z : ℂ) (hz : z ^ n = 1) :
    ∑ k ∈ range n, ramanujanSum d k * z ^ k =
      if IsPrimitiveRoot z d then (n : ℂ) else 0 := by
  classical
  have hdpos := Nat.pos_of_dvd_of_pos hd hn
  have hz0 : z ≠ 0 := by
    intro h
    simpa [h, hn.ne'] using hz
  let A := (range d).filter (fun a => a.Coprime d)
  have hp (a : ℕ) (ha : a ∈ A) : IsPrimitiveRoot (zeta d ^ a) d := by
    exact (Complex.isPrimitiveRoot_exp d hdpos.ne').pow_of_coprime a
      (mem_filter.mp ha).2
  have hs : (∑ k ∈ range n, ramanujanSum d k * z ^ k) =
      ∑ a ∈ A, if zeta d ^ a * z = 1 then (n : ℂ) else 0 := by
    simp_rw [ramanujan_pow_sum, Finset.sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro a ha
    simp_rw [← mul_pow]
    apply geometric_period
    have hpn : (zeta d ^ a) ^ n = 1 := by
      obtain ⟨r, rfl⟩ := hd
      rw [pow_mul, (hp a ha).pow_eq_one, one_pow]
    rw [mul_pow, hpn, hz, one_mul]
  rw [hs]
  by_cases hprim : IsPrimitiveRoot z d
  · rw [if_pos hprim]
    obtain ⟨a, had, hac, hphase⟩ :=
      (Complex.isPrimitiveRoot_iff z⁻¹ d hdpos.ne').mp hprim.inv
    have hphase' : zeta d ^ a = z⁻¹ := by
      rw [zeta, ← Complex.exp_nat_mul]
      convert hphase using 1 <;> congr 1 <;> ring
    have haA : a ∈ A := mem_filter.mpr ⟨mem_range.mpr had, hac⟩
    rw [sum_eq_single a]
    · rw [hphase', inv_mul_cancel₀ hz0, if_pos rfl]
    · intro b hb hba
      rw [if_neg]
      intro hbz
      have hba' : zeta d ^ b = zeta d ^ a := by
        rw [hphase']
        exact (mul_eq_one_iff_eq_inv₀ hz0).mp hbz
      exact hba ((Complex.isPrimitiveRoot_exp d hdpos.ne').pow_inj
        (mem_range.mp (mem_filter.mp hb).1) had hba')
    · exact fun h => (h haA).elim
  · rw [if_neg hprim]
    apply sum_eq_zero
    intro a ha
    rw [if_neg]
    intro h
    have heq : zeta d ^ a = z⁻¹ := (mul_eq_one_iff_eq_inv₀ hz0).mp h
    exact hprim (IsPrimitiveRoot.inv_iff.mp (heq ▸ hp a ha))


end D5.S3.Arith.InterlaceFan.Cyclotomic
