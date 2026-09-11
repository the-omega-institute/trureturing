/- GID: D5/S3/Weil/ZetaBridge/RieszBaezDuarte
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaBridge/RieszBaezDuarte
   mirror-E: none(waiver:analytic-identities)
   anchors: [mathlib/module/Mathlib.NumberTheory.LSeries.Dirichlet]
   utility: none
   digest: The Riesz series and Baez-Duarte coefficients have convergent exponential and signed Moebius transforms. -/

import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.Basic

open scoped BigOperators

namespace D5.S3.Weil.RieszBaezDuarte

noncomputable def riesz (x : Real) : Real := x * tsum (fun j : Nat =>
  (-1 : Real)^j * x^j / ((Nat.factorial j : Real) *
    (riemannZeta ((2*j+2 : Nat) : Complex)).re))

noncomputable def baezDuarte (k : Nat) : Real :=
  Finset.sum (Finset.range (k+1)) (fun j => (-1 : Real)^j *
    (Nat.choose k j : Real) / (riemannZeta ((2*j+2 : Nat) : Complex)).re)

private noncomputable def q (n : Nat) : Real := 1 / ((n+1 : Nat) : Real)^2

private lemma q_bounds (n : Nat) : 0 < q n ∧ q n ≤ 1 := by
  have hn : (1 : Real) ≤ (n+1 : Nat) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  constructor
  · exact one_div_pos.mpr (sq_pos_of_pos (by positivity))
  · exact (div_le_one (by positivity)).mpr (by nlinarith)

private lemma q_summable : Summable q := by
  exact (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num))

private lemma zeta_real (j : Nat) :
    ((riemannZeta ((2*j+2 : Nat) : Complex)).re : Complex) =
      riemannZeta ((2*j+2 : Nat) : Complex) := by
  have h := riemannZeta_im_eq_zero_of_one_lt (x := ((2*j+2 : Nat) : Real)) (by norm_cast; omega)
  apply Complex.ext <;> simp_all

private lemma zeta_re_ne_zero (j : Nat) :
    (riemannZeta ((2*j+2 : Nat) : Complex)).re ≠ 0 := by
  have h := riemannZeta_re_pos_of_one_lt (x := ((2*j+2 : Nat) : Real)) (by norm_cast; omega)
  exact ne_of_gt (by simpa using h)

private lemma reciprocal_cast (j : Nat) :
    ((1 / (riemannZeta ((2*j+2 : Nat) : Complex)).re : Real) : Complex) =
      1 / riemannZeta ((2*j+2 : Nat) : Complex) := by
  rw [Complex.ofReal_div, Complex.ofReal_one, zeta_real]

private lemma coefficient_hasSum (j : Nat) : HasSum (fun n : Nat =>
    (ArithmeticFunction.moebius (n+1) : Real) * q n * (q n)^j)
    (1 / (riemannZeta ((2*j+2 : Nat) : Complex)).re) := by
  have hs : 1 < (((2*j+2 : Nat) : Complex)).re := by simp; norm_cast; omega
  have hi := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at hi
  have hz : riemannZeta ((2*j+2 : Nat) : Complex) ≠ 0 := by
    rw [← zeta_real]; exact_mod_cast zeta_re_ne_zero j
  have hv : LSeries (fun n => (ArithmeticFunction.moebius n : Complex))
      ((2*j+2 : Nat) : Complex) = 1 / riemannZeta ((2*j+2 : Nat) : Complex) :=
    (eq_div_iff hz).mpr (by simpa [mul_comm] using hi)
  have hh := (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs).hasSum
  change HasSum _ (LSeries _ _) at hh
  rw [hv] at hh
  have ht := (hasSum_nat_add_iff' 1).mpr hh
  simp only [Finset.sum_range_one, LSeries.term_zero, sub_zero] at ht
  rw [← reciprocal_cast] at ht
  apply Complex.hasSum_ofReal.mp
  refine ht.congr_fun (fun n => ?_)
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), Complex.cpow_natCast]
  dsimp [q]
  push_cast
  simp only [div_eq_mul_inv, one_mul, pow_add, pow_mul, mul_inv_rev, inv_pow]
  ring

private lemma coefficient_term_bound (j n : Nat) :
    ‖(ArithmeticFunction.moebius (n+1) : Real) * q n * (q n)^j‖ ≤ q n := by
  have hm : |(ArithmeticFunction.moebius (n+1) : Real)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n+1)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (q_bounds n).1,
    abs_pow, abs_of_pos (q_bounds n).1]
  calc
    _ ≤ 1 * q n * 1 := mul_le_mul
      (mul_le_mul_of_nonneg_right hm (q_bounds n).1.le)
      (pow_le_one₀ (q_bounds n).1.le (q_bounds n).2)
      (pow_nonneg (q_bounds n).1.le _) (by simpa using (q_bounds n).1.le)
    _ = q n := by ring

private lemma coefficient_bound (j : Nat) :
    ‖1 / (riemannZeta ((2*j+2 : Nat) : Complex)).re‖ ≤ tsum q :=
  (coefficient_hasSum j).norm_le_of_bounded q_summable.hasSum (coefficient_term_bound j)

private lemma riesz_norm_summable (x : Real) : Summable (fun j : Nat =>
    ‖(-1 : Real)^j * x^j / ((Nat.factorial j : Real) *
      (riemannZeta ((2*j+2 : Nat) : Complex)).re)‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (f := fun j => tsum q * (|x|^j / (Nat.factorial j : Real)))
  · intro j
    calc
      _ = ‖1 / (riemannZeta ((2*j+2 : Nat) : Complex)).re‖ *
          (|x|^j / (Nat.factorial j : Real)) := by
        simp [norm_mul, norm_pow, Real.norm_eq_abs,
          div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_right (coefficient_bound j) (by positivity)
  · exact (Real.summable_pow_div_factorial |x|).mul_left _

theorem baez_duarte_hasSum_moebius (k : Nat) : HasSum (fun n : Nat =>
    (ArithmeticFunction.moebius (n+1) : Real) / ((n+1 : Nat) : Real)^2 *
      (1 - 1 / ((n+1 : Nat) : Real)^2)^k) (baezDuarte k) := by
  have h := hasSum_sum (s := Finset.range (k+1)) (fun j _ =>
    (coefficient_hasSum j).mul_left ((-1 : Real)^j * (Nat.choose k j : Real)))
  have hv : (∑ j ∈ Finset.range (k+1), (-1 : Real)^j * (Nat.choose k j : Real) *
      (1 / (riemannZeta ((2*j+2 : Nat) : Complex)).re)) = baezDuarte k := by
    simp [baezDuarte, div_eq_mul_inv]
  rw [hv] at h
  refine h.congr_fun (fun n => ?_)
  have hb := add_pow (-q n) (1 : Real) k
  have he : 1 - q n = -q n + 1 := by ring
  have ha : (ArithmeticFunction.moebius (n+1) : Real) / ((n+1 : Nat) : Real)^2 =
      (ArithmeticFunction.moebius (n+1) : Real) * q n := by simp [q, div_eq_mul_inv]
  change (ArithmeticFunction.moebius (n+1) : Real) / ((n+1 : Nat) : Real)^2 * (1 - q n)^k = _
  rw [ha]
  rw [he, hb, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [neg_pow]
  simp only [one_pow, mul_one]
  ring

private lemma exp_hasSum (x : Real) :
    HasSum (fun j : Nat => x^j / (Nat.factorial j : Real)) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

theorem riesz_generating_hasSum (x : Real) (hx : 0 < x) :
    HasSum (fun k : Nat => baezDuarte k * x^k / (Nat.factorial k : Real))
      (Real.exp x * (riesz x / x)) := by
  have h := hasSum_sum_range_mul_of_summable_norm (riesz_norm_summable x)
    (NormedSpace.norm_expSeries_div_summable x)
  rw [(exp_hasSum x).tsum_eq] at h
  have hv : (tsum (fun j : Nat => (-1 : Real)^j * x^j /
      ((Nat.factorial j : Real) * (riemannZeta ((2*j+2 : Nat) : Complex)).re))) =
      riesz x / x := by rw [riesz, mul_div_cancel_left₀ _ (ne_of_gt hx)]
  rw [hv, mul_comm] at h
  refine h.congr_fun (fun k => ?_)
  rw [baezDuarte, Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hfac : (Nat.choose k j : Real) * (Nat.factorial j : Real) *
      (Nat.factorial (k-j) : Real) = (Nat.factorial k : Real) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjk
  have hp : x^j * x^(k-j) = x^k := by rw [← pow_add, Nat.add_sub_of_le hjk]
  have hz := zeta_re_ne_zero j
  have hfj : (Nat.factorial j : Real) ≠ 0 := by positivity
  have hfk : (Nat.factorial k : Real) ≠ 0 := by positivity
  have hfd : (Nat.factorial (k-j) : Real) ≠ 0 := by positivity
  field_simp
  linear_combination x^k * hfac - (Nat.factorial k : Real) * hp

private lemma kernel_bound (k n : Nat) :
    ‖(ArithmeticFunction.moebius (n+1) : Real) * q n * (1-q n)^k‖ ≤ q n := by
  have hm : ‖(ArithmeticFunction.moebius (n+1) : Real) * q n‖ ≤ q n := by
    simpa using coefficient_term_bound 0 n
  have hb : |1-q n| ≤ 1 := abs_le.mpr ⟨by linarith [(q_bounds n).2],
    by linarith [(q_bounds n).1]⟩
  rw [norm_mul, norm_pow, Real.norm_eq_abs]
  simpa using mul_le_mul hm (pow_le_one₀ (abs_nonneg _) hb)
    (pow_nonneg (abs_nonneg _) _) (q_bounds n).1.le

theorem riesz_hasSum_moebius (x : Real) (hx : 0 < x) : HasSum (fun n : Nat =>
    (ArithmeticFunction.moebius (n+1) : Real) / ((n+1 : Nat) : Real)^2 *
      Real.exp (-x / ((n+1 : Nat) : Real)^2)) (riesz x / x) := by
  let f : Nat × Nat → Real := fun p =>
    (ArithmeticFunction.moebius (p.1+1) : Real) * q p.1 * (1-q p.1)^p.2 *
      (x^p.2 / (Nat.factorial p.2 : Real))
  have hmajor := q_summable.mul_of_nonneg (exp_hasSum x).summable
    (fun n => (q_bounds n).1.le) (fun k => by positivity)
  have hn : Summable (fun p => ‖f p‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) hmajor
    dsimp [f]
    rw [abs_mul, abs_of_nonneg (show 0 ≤ x^p.2 /
      (Nat.factorial p.2 : Real) by positivity)]
    exact mul_le_mul_of_nonneg_right (kernel_bound p.2 p.1) (by positivity)
  have hp := hn.of_norm
  have hrow (n : Nat) : HasSum (fun k => f (n,k))
      ((ArithmeticFunction.moebius (n+1) : Real) * q n * Real.exp (x*(1-q n))) := by
    refine ((exp_hasSum (x*(1-q n))).mul_left
      ((ArithmeticFunction.moebius (n+1) : Real) * q n)).congr_fun (fun k => ?_)
    dsimp [f]
    rw [mul_pow]
    ring
  have hcol (k : Nat) : HasSum (fun n => f (n,k))
      (baezDuarte k * x^k / (Nat.factorial k : Real)) := by
    have h := (baez_duarte_hasSum_moebius k).mul_right (x^k / (Nat.factorial k : Real))
    simpa [f, q, div_eq_mul_inv, mul_assoc] using h
  have ht : tsum f = Real.exp x * (riesz x / x) := by
    calc
      tsum f = ∑' n, ∑' k, f (n,k) := hp.tsum_prod
      _ = ∑' k, ∑' n, f (n,k) := hp.tsum_comm.symm
      _ = ∑' k, baezDuarte k * x^k / (Nat.factorial k : Real) :=
        tsum_congr (fun k => (hcol k).tsum_eq)
      _ = _ := (riesz_generating_hasSum x hx).tsum_eq
  have h := (hp.hasSum.prod_fiberwise hrow).mul_left (Real.exp (-x))
  rw [ht, ← mul_assoc, ← Real.exp_add] at h
  simp only [neg_add_cancel, Real.exp_zero, one_mul] at h
  refine h.congr_fun (fun n => ?_)
  have he : -x + x*(1-q n) = -x*q n := by ring
  calc
    _ = (ArithmeticFunction.moebius (n+1) : Real) * q n * Real.exp (-x*q n) := by
      simp [q, div_eq_mul_inv]
    _ = Real.exp (-x) * ((ArithmeticFunction.moebius (n+1) : Real) * q n *
        Real.exp (x*(1-q n))) := by rw [← he, Real.exp_add]; ring

example (j : Nat) : (1 / riemannZeta ((2*j+2 : Nat) : Complex)).re =
    1 / (riemannZeta ((2*j+2 : Nat) : Complex)).re := by
  rw [← reciprocal_cast j, Complex.ofReal_re]

example (j : Nat) : (riemannZeta ((2*j+2 : Nat) : Complex)).im = 0 := by
  rw [← zeta_real j, Complex.ofReal_im]

example (x : Real) : Summable (fun j : Nat =>
    ‖(-1 : Real)^j * x^j / ((Nat.factorial j : Real) *
      (riemannZeta ((2*j+2 : Nat) : Complex)).re)‖) := riesz_norm_summable x

example : (ArithmeticFunction.moebius 1 : Real) * q 0 * (1-q 0)^0 = 1 := by
  norm_num [q]

example : (ArithmeticFunction.moebius 1 : Real) * q 0 * (1-q 0)^1 = 0 := by
  norm_num [q]

#print axioms riesz
#print axioms baezDuarte
#print axioms q
#print axioms q_bounds
#print axioms q_summable
#print axioms zeta_real
#print axioms zeta_re_ne_zero
#print axioms reciprocal_cast
#print axioms coefficient_hasSum
#print axioms coefficient_term_bound
#print axioms coefficient_bound
#print axioms riesz_norm_summable
#print axioms baez_duarte_hasSum_moebius
#print axioms exp_hasSum
#print axioms riesz_generating_hasSum
#print axioms kernel_bound
#print axioms riesz_hasSum_moebius

end D5.S3.Weil.RieszBaezDuarte
