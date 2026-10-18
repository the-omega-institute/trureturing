/- GID: D5/S3/Quantum/FockSpace/IdealHeraldingRateMonotonicity
   generality: I
   mirror-B: D5/B/S3/Quantum/FockSpace/IdealHeraldingRateMonotonicity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The ideal heralding rate strictly decreases from n = 5 to one quarter. -/

import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.Transcendental.Lindemann.AnalyticalPart

open scoped Topology
open MeasureTheory
open private LindemannWeierstrass.integral_exp_mul_eval from Mathlib.NumberTheory.Transcendental.Lindemann.AnalyticalPart

namespace D5.S3.Quantum.FockSpace.IdealHeraldingRateMonotonicity

def pRat (n : ℕ) : ℚ :=
  ((-1 : ℚ) / (n : ℚ)) ^ (n - 1) * ((n - 1).factorial : ℚ) *
    ∑ t ∈ Finset.range n, ((n : ℚ) - (t : ℚ)) * (-(n : ℚ)) ^ t / (t.factorial : ℚ)
noncomputable def p (n : ℕ) : ℝ := (pRat n : ℝ)
def claim : Prop :=
  (∀ n : ℕ, 5 ≤ n → p (n + 1) < p n) ∧ Filter.Tendsto p Filter.atTop (𝓝 (1 / 4 : ℝ))

private lemma p_eq_sum (n : ℕ) :
    p n = ((-1 : ℝ) / (n : ℝ)) ^ (n - 1) * ((n - 1).factorial : ℝ) *
      ∑ t ∈ Finset.range n, ((n : ℝ) - (t : ℝ)) * (-(n : ℝ)) ^ t /
        (t.factorial : ℝ) := by
  simp only [p.eq_1, pRat.eq_1, Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_neg,
    Rat.cast_one, Rat.cast_natCast, Rat.cast_sum, Rat.cast_sub]

private lemma weighted_sum_shift (z : ℝ) (m : ℕ) :
    (∑ t ∈ Finset.range (m + 1), (t : ℝ) * z ^ t / (t.factorial : ℝ)) =
      z * ∑ t ∈ Finset.range m, z ^ t / (t.factorial : ℝ) := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [Nat.cast_zero, zero_mul, zero_div, add_zero]
  apply Finset.sum_congr rfl
  intro t _
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  have ht : (t : ℝ) + 1 ≠ 0 := by positivity
  field_simp (disch := first | assumption | positivity)

private lemma moment_succ (a : ℝ) (m : ℕ) :
    a * (∫ u in (0 : ℝ)..1, u ^ (m + 1) * Real.exp (a * (u - 1))) =
      1 - ((m : ℝ) + 1) * (∫ u in (0 : ℝ)..1, u ^ m * Real.exp (a * (u - 1))) := by
  have hd (u : ℝ) : HasDerivAt
      (fun v : ℝ => v ^ (m + 1) * Real.exp (a * (v - 1)))
      (((m : ℝ) + 1) * (u ^ m * Real.exp (a * (u - 1))) +
        a * (u ^ (m + 1) * Real.exp (a * (u - 1)))) u := by
    convert ((hasDerivAt_id u).pow (m + 1)).mul
      ((((hasDerivAt_id u).sub_const 1).const_mul a).exp) using 1 <;> first | rfl |
      (simp only [id_eq, Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]; ring)
  have hi (k : ℕ) : IntervalIntegrable
      (fun u : ℝ => u ^ k * Real.exp (a * (u - 1))) volume 0 1 := by
    exact ((continuous_id.pow k).mul
      (Real.continuous_exp.comp
        (continuous_const.mul (continuous_id.sub continuous_const)))).intervalIntegrable 0 1
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    ((hi m).const_mul ((m : ℝ) + 1) |>.add ((hi (m + 1)).const_mul a))
  rw [intervalIntegral.integral_add ((hi m).const_mul _) ((hi (m + 1)).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hf
  simp at hf
  linarith

private lemma moment_closed (a : ℝ) (ha : 0 < a) (m : ℕ) :
    a * (∫ u in (0 : ℝ)..1, u ^ m * Real.exp (a * (u - 1))) =
      ((-1 : ℝ) / a) ^ m * (m.factorial : ℝ) *
        ((∑ t ∈ Finset.range (m + 1), (-a) ^ t / (t.factorial : ℝ)) -
          Real.exp (-a)) := by
  have h := LindemannWeierstrass.integral_exp_mul_eval
    ((Polynomial.X : Polynomial ℂ) ^ m) (-(a : ℂ))
  have hsum : Polynomial.sumIDeriv ((Polynomial.X : Polynomial ℂ) ^ m) =
      ∑ k ∈ Finset.range (m + 1),
        Polynomial.C (Nat.descFactorial m k : ℂ) * Polynomial.X ^ (m - k) := by
    rw [Polynomial.sumIDeriv_apply_of_le (p := (Polynomial.X : Polynomial ℂ) ^ m) (n := m)
      (by rw [Polynomial.natDegree_X_pow])]
    simp_rw [Polynomial.iterate_derivative_X_pow_eq_C_mul]
  have hsum_eval (z : ℂ) :
      (∑ k ∈ Finset.range (m + 1), (Nat.descFactorial m k : ℂ) * z ^ (m - k)) =
      ∑ t ∈ Finset.range (m + 1), (m.factorial : ℂ) * z ^ t / (t.factorial : ℂ) := by
    rw [← Finset.sum_range_reflect (fun k => (Nat.descFactorial m k : ℂ) * z ^ (m - k)) (m + 1)]
    apply Finset.sum_congr rfl
    intro k hk
    have hk_le : k ≤ m := by exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hfac := Nat.factorial_mul_descFactorial (n := m) (k := m - k) (by omega)
    rw [Nat.sub_sub_self hk_le] at hfac
    have hfac' : (m.factorial : ℂ) = (k.factorial : ℂ) * (Nat.descFactorial m (m-k) : ℂ) := by
      exact_mod_cast hfac.symm
    simp only [Nat.add_sub_cancel]
    rw [Nat.sub_sub_self hk_le]
    have hkfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hdesc : (Nat.descFactorial m (m - k) : ℂ) =
        (m.factorial : ℂ) * (k.factorial : ℂ)⁻¹ := by
      calc
        (Nat.descFactorial m (m - k) : ℂ) =
            ((k.factorial : ℂ)⁻¹ * (k.factorial : ℂ)) *
              (Nat.descFactorial m (m - k) : ℂ) := by
                rw [inv_mul_cancel₀ hkfac, one_mul]
        _ = (k.factorial : ℂ)⁻¹ *
              ((k.factorial : ℂ) * (Nat.descFactorial m (m-k) : ℂ)) := by ring
        _ = (k.factorial : ℂ)⁻¹ * (m.factorial : ℂ) := by
              rw [hfac']
        _ = (m.factorial : ℂ) * (k.factorial : ℂ)⁻¹ := by ring
    rw [div_eq_mul_inv, hdesc]
    ring_nf
  have hzero :
      (∑ k ∈ Finset.range (m + 1), (Nat.descFactorial m k : ℂ) * (0 : ℂ) ^ (m - k)) =
        (m.factorial : ℂ) := by
    rw [Finset.sum_eq_single m]
    · simp [Nat.descFactorial_self]
    · intro b hb hne
      have hbm : b < m := lt_of_le_of_ne (Nat.le_of_lt_succ (Finset.mem_range.mp hb)) hne
      have hne0 : m - b ≠ 0 := Nat.sub_ne_zero_of_lt hbm
      simp [zero_pow hne0]
    · intro hm
      exact (hm (Finset.mem_range.mpr (Nat.lt_succ_self m))).elim
  have hint :
      (∫ x in (0 : ℝ)..1, Complex.exp ((x : ℂ) * (a : ℂ)) *
        (-((x : ℂ) * (a : ℂ))) ^ m) =
        (-(a : ℂ)) ^ m *
          (↑(∫ x in (0 : ℝ)..1, Real.exp (a * x) * x ^ m) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp
    rw [← Complex.ofReal_mul, ← Complex.ofReal_exp]
    simp only [Complex.ofReal_mul, Complex.ofReal_pow]
    ring_nf
  have hI :
      (∫ u in (0 : ℝ)..1, u ^ m * Real.exp (a * (u - 1))) =
        Real.exp (-a) * ∫ u in (0 : ℝ)..1, Real.exp (a * u) * u ^ m := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    calc
      u ^ m * Real.exp (a * (u - 1)) =
          u ^ m * (Real.exp (-a) * Real.exp (a * u)) := by
            rw [← Real.exp_add]
            (congr 1; ring_nf)
      _ = Real.exp (-a) * (Real.exp (a * u) * u ^ m) := by ring
  rw [hsum] at h
  simp only [smul_neg, Complex.real_smul, neg_neg, Polynomial.eval_pow, Polynomial.eval_X,
    neg_mul, map_natCast, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_natCast] at h
  rw [hint, hsum_eval, hzero] at h
  have hIcomplex :
      (↑(∫ u in (0 : ℝ)..1, u ^ m * Real.exp (a * (u - 1))) : ℂ) =
        Complex.exp (-(a : ℂ)) *
          (↑(∫ u in (0 : ℝ)..1, Real.exp (a * u) * u ^ m) : ℂ) := by
    simpa only [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg] using
      congrArg (fun x : ℝ => (x : ℂ)) hI
  have hfacsum :
      (∑ t ∈ Finset.range (m + 1), (m.factorial : ℂ) * (-(a : ℂ)) ^ t /
        (t.factorial : ℂ)) =
        (m.factorial : ℂ) *
          (∑ t ∈ Finset.range (m + 1), (-(a : ℂ)) ^ t / (t.factorial : ℂ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  have htrans :
      -(a : ℂ) * ((-(a : ℂ)) ^ m *
          (↑(∫ u in (0 : ℝ)..1, u ^ m * Real.exp (a * (u - 1))) : ℂ)) =
        -(m.factorial : ℂ) *
            (∑ t ∈ Finset.range (m + 1), (-(a : ℂ)) ^ t / (t.factorial : ℂ)) +
          (m.factorial : ℂ) * Complex.exp (-(a : ℂ)) := by
    calc
      _ = Complex.exp (-(a : ℂ)) *
          (-(a : ℂ) * ((-(a : ℂ)) ^ m *
            (↑(∫ u in (0 : ℝ)..1, Real.exp (a * u) * u ^ m) : ℂ))) := by
              rw [hIcomplex]
              ring
      _ = Complex.exp (-(a : ℂ)) *
          (-(Complex.exp (a : ℂ) *
            ∑ t ∈ Finset.range (m + 1), (m.factorial : ℂ) * (-(a : ℂ)) ^ t /
              (t.factorial : ℂ)) + (m.factorial : ℂ)) := by
                congr 1
                convert h using 1 ; ring
      _ = _ := by
        rw [hfacsum, Complex.exp_neg, mul_add]
        have hexp : (Complex.exp (a : ℂ))⁻¹ * Complex.exp (a : ℂ) = 1 :=
          inv_mul_cancel₀ (Complex.exp_ne_zero _)
        have hcancel (q : ℂ) :
            (Complex.exp (a : ℂ))⁻¹ * -(Complex.exp (a : ℂ) * q) = -q := by
          calc
            (Complex.exp (a : ℂ))⁻¹ * -(Complex.exp (a : ℂ) * q) =
                -((Complex.exp (a : ℂ))⁻¹ * (Complex.exp (a : ℂ) * q)) := by ring
            _ = -q := by rw [← mul_assoc, hexp, one_mul]
        rw [show (Complex.exp (a : ℂ))⁻¹ *
              -(Complex.exp (a : ℂ) * ((m.factorial : ℂ) *
                ∑ i ∈ Finset.range (m + 1), (-(a : ℂ)) ^ i / (i.factorial : ℂ))) =
            -((m.factorial : ℂ) *
              ∑ i ∈ Finset.range (m + 1), (-(a : ℂ)) ^ i / (i.factorial : ℂ)) by
                exact hcancel _]
        rw [show (Complex.exp (a : ℂ))⁻¹ * (m.factorial : ℂ) =
              (m.factorial : ℂ) * Complex.exp (-(a : ℂ)) by
                rw [Complex.exp_neg]
                ring]
        rw [Finset.mul_sum]
        simp only [Complex.exp_neg]
        rw [← Finset.mul_sum]
        ring
  have hsumcast :
      (↑(∑ t ∈ Finset.range (m + 1), (-a) ^ t / (t.factorial : ℝ)) : ℂ) =
        ∑ t ∈ Finset.range (m + 1), (-(a : ℂ)) ^ t / (t.factorial : ℂ) := by
    norm_cast
  have htrans_real :
      -a * ((-a) ^ m * ∫ u in (0 : ℝ)..1, u ^ m * Real.exp (a * (u - 1))) =
        -(m.factorial : ℝ) *
            (∑ t ∈ Finset.range (m + 1), (-a) ^ t / (t.factorial : ℝ)) +
          (m.factorial : ℝ) * Real.exp (-a) := by
    have htr := htrans
    rw [← hsumcast] at htr
    rw [← Complex.ofReal_neg, ← Complex.ofReal_pow, ← Complex.ofReal_exp] at htr
    push_cast at htr
    exact_mod_cast htr
  have hcoef : ((-1 : ℝ) / a) ^ m * (-a) ^ m = 1 := by
    rw [← mul_pow, div_eq_mul_inv]
    have hbase : (-1 : ℝ) * a⁻¹ * (-a) = 1 := by
      calc
        (-1 : ℝ) * a⁻¹ * (-a) = a⁻¹ * a := by ring
        _ = 1 := inv_mul_cancel₀ ha.ne'
    rw [hbase]
    simp
  have hmid :
      (-a) ^ m * a * (∫ u in (0 : ℝ)..1, u ^ m * Real.exp (a * (u - 1))) =
        (m.factorial : ℝ) *
          ((∑ t ∈ Finset.range (m + 1), (-a) ^ t / (t.factorial : ℝ)) -
            Real.exp (-a)) := by
    linear_combination -htrans_real
  calc
    a * (∫ u in (0 : ℝ)..1, u ^ m * Real.exp (a * (u - 1))) =
        (((-1 : ℝ) / a) ^ m * (-a) ^ m) *
          (a * (∫ u in (0 : ℝ)..1, u ^ m * Real.exp (a * (u - 1)))) := by
            rw [hcoef, one_mul]
    _ = ((-1 : ℝ) / a) ^ m *
          ((-a) ^ m * a *
            (∫ u in (0 : ℝ)..1, u ^ m * Real.exp (a * (u - 1)))) := by ring
    _ = ((-1 : ℝ) / a) ^ m * (m.factorial : ℝ) *
          ((∑ t ∈ Finset.range (m + 1), (-a) ^ t / (t.factorial : ℝ)) -
            Real.exp (-a)) := by rw [hmid]; ring

private noncomputable def r (u : ℝ) : ℝ := u * Real.exp (u - 1)
private noncomputable def K (u : ℝ) : ℝ := 2 * (2 * u - 1) / (1 + u) ^ 4
private noncomputable def A (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * ∫ u in (0 : ℝ)..1,
    (1 - u) * u ^ (n - 1) * Real.exp ((n : ℝ) * (u - 1))
private noncomputable def T (n : ℕ) : ℝ :=
  2 * (n.factorial : ℝ) * Real.exp (-(n : ℝ)) / (n : ℝ) ^ (n - 1)

private lemma p_split (n : ℕ) (hn : 1 ≤ n) :
    p n = A n + (-1 : ℝ) ^ (n - 1) * T n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hfac : ((n - 1).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - 1)
  let d : ℝ := ((-1 : ℝ) / n) ^ (n - 1) * ((n - 1).factorial : ℝ)
  let S : ℝ := ∑ t ∈ Finset.range n, (-(n : ℝ)) ^ t / (t.factorial : ℝ)
  let I (m : ℕ) : ℝ := ∫ u in (0 : ℝ)..1, u ^ m * Real.exp ((n : ℝ) * (u - 1))
  have hw := weighted_sum_shift (-(n : ℝ)) (n - 1)
  rw [Nat.sub_add_cancel hn] at hw
  have hs := Finset.sum_range_succ (fun t => (-(n : ℝ)) ^ t / (t.factorial : ℝ))
    (n - 1)
  rw [Nat.sub_add_cancel hn] at hs
  have hc : ((-1 : ℝ) / n) ^ (n - 1) * (-(n : ℝ)) ^ (n - 1) = 1 := by
    rw [← mul_pow]
    field_simp (disch := first | assumption | positivity)
    simp
  have hl : d * ((-(n : ℝ)) ^ (n - 1) / ((n - 1).factorial : ℝ)) = 1 := by
    dsimp [d]
    calc
      _ = ((-1 : ℝ) / n) ^ (n - 1) * (-(n : ℝ)) ^ (n - 1) := by
        field_simp (disch := first | assumption | positivity)
      _ = 1 := hc
  have hsum : (∑ t ∈ Finset.range n,
      ((n : ℝ) - (t : ℝ)) * (-(n : ℝ)) ^ t / (t.factorial : ℝ)) =
      2 * n * S - n * ((-(n : ℝ)) ^ (n - 1) / ((n - 1).factorial : ℝ)) := by
    simp_rw [sub_mul, sub_div]
    rw [Finset.sum_sub_distrib]
    simp_rw [mul_div_assoc]
    simp_rw [mul_div_assoc] at hw
    rw [← Finset.mul_sum, hw]
    dsimp [S]
    linear_combination -(n : ℝ) * hs
  have hp : p n = 2 * n * d * S - n := by
    rw [p_eq_sum, hsum]
    change d * _ = _
    linear_combination -(n : ℝ) * hl
  have hi (k : ℕ) : IntervalIntegrable
      (fun u : ℝ => u ^ k * Real.exp ((n : ℝ) * (u - 1))) volume 0 1 :=
    (by fun_prop : Continuous (fun u : ℝ =>
      u ^ k * Real.exp ((n : ℝ) * (u - 1)))).intervalIntegrable 0 1
  have hA : A n = (n : ℝ) ^ 2 * (I (n - 1) - I n) := by
    unfold A I
    rw [← intervalIntegral.integral_sub (hi (n - 1)) (hi n)]
    congr 1
    apply intervalIntegral.integral_congr
    intro u _
    dsimp
    have hpow : u ^ n = u ^ (n - 1) * u := by
      conv_lhs => rw [← Nat.sub_add_cancel hn, pow_succ]
    rw [hpow]
    ring
  have hm := moment_succ (n : ℝ) (n - 1)
  rw [Nat.sub_add_cancel hn, ← Nat.cast_add_one, Nat.sub_add_cancel hn] at hm
  have hclosed := moment_closed (n : ℝ) (by exact_mod_cast (by omega : 0 < n) : 0 < (n : ℝ)) (n - 1)
  rw [Nat.sub_add_cancel hn] at hclosed
  change (n : ℝ) * I (n - 1) = d * (S - Real.exp (-(n : ℝ))) at hclosed
  change (n : ℝ) * I n = 1 - (n : ℝ) * I (n - 1) at hm
  have hT : (-1 : ℝ) ^ (n - 1) * T n = 2 * n * d * Real.exp (-(n : ℝ)) := by
    unfold T d
    rw [← Nat.mul_factorial_pred (by omega : n ≠ 0), Nat.cast_mul, div_pow]
    ring
  rw [hp, hA, hT]
  linear_combination (n : ℝ) * hm - 2 * (n : ℝ) * hclosed

private lemma tail_bounds (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ T n ∧ T n ≤ 2 * (n : ℝ) * Real.exp (-(n : ℝ)) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hf : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by
    exact_mod_cast Nat.factorial_le_pow n
  constructor
  · unfold T; positivity
  · unfold T
    rw [div_le_iff₀ (pow_pos hnpos _)]
    have hpow : (n : ℝ) ^ n = (n : ℝ) ^ (n - 1) * n := by
      conv_lhs => rw [← Nat.sub_add_cancel hn, pow_succ]
      rw [Nat.sub_add_cancel hn]
    rw [hpow] at hf
    nlinarith [Real.exp_pos (-(n : ℝ))]

private lemma primitive_deriv (n : ℕ) (hn : 1 ≤ n) (u : ℝ)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) : HasDerivAt
    (fun v : ℝ => ((n : ℝ) * (1 - v) / (1 + v) + 2 * v / (1 + v) ^ 3) *
      v ^ n * Real.exp ((n : ℝ) * (v - 1)))
    ((n : ℝ) ^ 2 * (1 - u) * u ^ (n - 1) * Real.exp ((n : ℝ) * (u - 1)) -
      K u * r u ^ n) u := by
  have hne : 1 + u ≠ 0 := by linarith [hu.1]
  have hpow : u ^ n = u ^ (n - 1) * u := by
    conv_lhs => rw [← Nat.sub_add_cancel hn, pow_succ]
  convert ((((hasDerivAt_const u (n : ℝ)).mul
      ((hasDerivAt_const u 1).sub (hasDerivAt_id u))).div
      ((hasDerivAt_const u 1).add (hasDerivAt_id u)) hne).add
      (((hasDerivAt_id u).const_mul 2).div
        (((hasDerivAt_const u 1).add (hasDerivAt_id u)).pow 3)
        (pow_ne_zero 3 hne))).mul ((hasDerivAt_id u).pow n) |>.mul
      ((((hasDerivAt_id u).sub_const 1).const_mul (n : ℝ)).exp) using 1
  all_goals try rfl
  dsimp only [Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
  simp only [K.eq_1, r.eq_1, mul_pow, ← Real.exp_nat_mul, hpow]
  field_simp (disch := first | assumption | positivity)
  ring

private lemma kernel_continuous (n : ℕ) :
    ContinuousOn (fun u : ℝ => K u * r u ^ n) (Set.Ici 0) := by
  simp only [K.eq_1, r.eq_1]
  apply ContinuousOn.mul
  · apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro u hu
      apply pow_ne_zero
      have hu0 : 0 ≤ u := hu
      linarith
  · fun_prop

private lemma main_eq_kernel (n : ℕ) (hn : 1 ≤ n) :
    A n = (1 / 4 : ℝ) + ∫ u in (0 : ℝ)..1, K u * r u ^ n := by
  have hi : IntervalIntegrable (fun u : ℝ => K u * r u ^ n) volume 0 1 :=
    (kernel_continuous n |>.mono (by intro u hu; exact hu.1)).intervalIntegrable_of_Icc
      zero_le_one
  have hj : IntervalIntegrable (fun u : ℝ =>
      (1 - u) * u ^ (n - 1) * Real.exp ((n : ℝ) * (u - 1))) volume 0 1 :=
    (by fun_prop : Continuous (fun u : ℝ =>
      (1 - u) * u ^ (n - 1) * Real.exp ((n : ℝ) * (u - 1)))).intervalIntegrable 0 1
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1)
    (f' := fun u => (n : ℝ) ^ 2 *
      ((1 - u) * u ^ (n - 1) * Real.exp ((n : ℝ) * (u - 1))) - K u * r u ^ n)
    (fun u hu => by simpa only [mul_assoc] using
      primitive_deriv n hn u (by simpa using hu))
    ((hj.const_mul ((n : ℝ) ^ 2)).sub hi)
  rw [intervalIntegral.integral_sub (hj.const_mul _) hi,
    intervalIntegral.integral_const_mul] at hf
  have hn0 : n ≠ 0 := by omega
  norm_num [hn0] at hf
  unfold A
  linarith

private lemma main_gap_eq_integral (n : ℕ) (hn : 1 ≤ n) :
    A n - A (n + 1) = ∫ u in (0 : ℝ)..1, K u * r u ^ n * (1 - r u) := by
  have hi (m : ℕ) : IntervalIntegrable (fun u : ℝ => K u * r u ^ m) volume 0 1 :=
    (kernel_continuous m |>.mono (by intro u hu; exact hu.1)).intervalIntegrable_of_Icc
      zero_le_one
  rw [main_eq_kernel n hn, main_eq_kernel (n + 1) (by omega)]
  rw [add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub (hi n) (hi (n + 1))]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp
  rw [pow_succ]
  ring

private lemma r_bounds (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ r u ∧ r u ≤ u := by
  simp only [r.eq_1]
  constructor
  · exact mul_nonneg hu.1 (Real.exp_nonneg _)
  · calc
      u * Real.exp (u - 1) ≤ u * 1 :=
        mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by linarith [hu.2])) hu.1
      _ = u := mul_one u

private lemma kernel_abs_le_two (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) : |K u| ≤ 2 := by
  have hd : 1 ≤ (1 + u) ^ 4 := one_le_pow₀ (by linarith [hu.1])
  have hp : 0 < (1 + u) ^ 4 := by positivity
  have ha : |2 * u - 1| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
  rw [K, abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_pos hp, div_le_iff₀ hp]
  linarith

private lemma gap_integrable (n : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun u : ℝ => K u * r u ^ n * (1 - r u)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.mul
  · apply (kernel_continuous n).mono
    intro u hu
    exact le_trans (le_min ha hb) hu.1
  · simp only [r.eq_1]
    fun_prop

private lemma negative_piece_lower (n : ℕ) :
    -Real.exp (-(n : ℝ)) ≤ ∫ u in (0 : ℝ)..(1 / 2 : ℝ),
      K u * r u ^ n * (1 - r u) := by
  have he : Real.exp (1 / 2 : ℝ) ≤ 2 := by
    have h := Real.exp_bound_div_one_sub_of_interval (x := (1 / 2 : ℝ))
      (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have hi := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1 / 2)
    (f := fun _ => -2 * Real.exp (-(n : ℝ))) (by norm_num)
    (continuous_const.intervalIntegrable _ _) (gap_integrable n _ _ (by norm_num) (by norm_num))
    (fun u hu => show -2 * Real.exp (-(n : ℝ)) ≤ K u * r u ^ n * (1 - r u) from by
      have hu01 : u ∈ Set.Icc (0 : ℝ) 1 := ⟨hu.1, by linarith [hu.2]⟩
      have hr := r_bounds u hu01
      have hk := (abs_le.mp (kernel_abs_le_two u hu01)).1
      have hex : Real.exp (-1 / 2 : ℝ) = Real.exp (-1) * Real.exp (1 / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have heupper : Real.exp (u - 1) ≤ Real.exp (-1 / 2 : ℝ) :=
        Real.exp_le_exp.mpr (by linarith [hu.2])
      have hru : r u ≤ Real.exp (-1 : ℝ) := by
        simp only [r.eq_1]
        calc
          u * Real.exp (u - 1) ≤ (1 / 2) * Real.exp (-1 / 2 : ℝ) :=
            mul_le_mul hu.2 heupper (Real.exp_nonneg _) (by norm_num)
          _ ≤ Real.exp (-1 : ℝ) := by rw [hex]; nlinarith [Real.exp_pos (-1)]
      have hpower : r u ^ n ≤ Real.exp (-(n : ℝ)) := by
        calc
          r u ^ n ≤ Real.exp (-1 : ℝ) ^ n := pow_le_pow_left₀ hr.1 hru n
          _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
      have hp0 := pow_nonneg hr.1 n
      have hprod : r u ^ n * (1 - r u) ≤ Real.exp (-(n : ℝ)) := by
        nlinarith [mul_nonneg hp0 hr.1]
      have hprod0 : 0 ≤ r u ^ n * (1 - r u) := mul_nonneg hp0 (by linarith [hr.2, hu.2])
      nlinarith [mul_nonneg (by linarith : 0 ≤ K u + 2) hprod0])
  norm_num [intervalIntegral.integral_const] at hi
  linarith

private lemma window_pointwise_lower (n : ℕ) (hn : 4 ≤ n) (u : ℝ)
    (hu : u ∈ Set.Icc (1 - 1 / (n : ℝ)) (1 - 1 / (2 * (n : ℝ)))) :
    (1 - u) / 192 ≤ K u * r u ^ n * (1 - r u) := by
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hn1 : 0 < (n : ℝ) - 1 := by linarith
  have hnm : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hv : (3 / 4 : ℝ) ≤ 1 - 1 / (n : ℝ) := by
    have hdiv : 1 / (n : ℝ) ≤ 1 / 4 := by
      rw [div_le_iff₀ hn0]
      nlinarith
    linarith
  have hu01 : u ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hu.1], by
    linarith [hu.2, div_pos (by norm_num : (0 : ℝ) < 1) (by positivity : 0 < 2 * (n : ℝ))]⟩
  have hk : (1 / 16 : ℝ) ≤ K u := by
    have hd : (1 + u) ^ 4 ≤ 16 := by
      exact (pow_le_pow_left₀ (by linarith [hu01.1] : 0 ≤ 1 + u)
        (by linarith [hu01.2] : 1 + u ≤ 2) 4).trans_eq (by norm_num)
    unfold K
    rw [le_div_iff₀ (pow_pos (by linarith [hu01.1] : 0 < 1 + u) 4)]
    nlinarith [hu.1]
  have hrec : (1 - 1 / (n : ℝ)) * (1 + ((n - 1 : ℕ) : ℝ)⁻¹) = 1 := by
    rw [hnm]
    field_simp (disch := first | assumption | positivity)
    ring
  have hp0 : 0 ≤ (1 - 1 / (n : ℝ)) ^ (n - 1) := pow_nonneg (by linarith) _
  have hp : (1 / 3 : ℝ) ≤ (1 - 1 / (n : ℝ)) ^ (n - 1) := by
    have he := Real.one_add_inv_pow_le_exp (n := n - 1)
    have hm := mul_le_mul_of_nonneg_left he hp0
    rw [← mul_pow, hrec, one_pow] at hm
    nlinarith [mul_nonneg (by linarith [Real.exp_one_lt_three] : 0 ≤ 3 - Real.exp 1) hp0]
  have hvn : (1 / 4 : ℝ) ≤ (1 - 1 / (n : ℝ)) ^ n := by
    have hpow : (1 - 1 / (n : ℝ)) ^ n =
        (1 - 1 / (n : ℝ)) ^ (n - 1) * (1 - 1 / (n : ℝ)) := by
      conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ n), pow_succ]
      rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
    rw [hpow]
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hv)]
  have hex : (1 / 3 : ℝ) ≤ Real.exp (-1) := by
    have heprod : Real.exp (-1 : ℝ) * Real.exp 1 = 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [mul_nonneg (Real.exp_nonneg (-1))
      (by linarith [Real.exp_one_lt_three] : 0 ≤ 3 - Real.exp 1)]
  have hexu : Real.exp (-1 : ℝ) ≤ Real.exp ((n : ℝ) * (u - 1)) := by
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_left hu.1 hn0.le
    field_simp (disch := first | assumption | positivity) at hmul
    nlinarith
  have hru : (1 / 12 : ℝ) ≤ r u ^ n := by
    have huPow := pow_le_pow_left₀ (by linarith : 0 ≤ 1 - 1 / (n : ℝ)) hu.1 n
    have he := hex.trans hexu
    simp only [r.eq_1]
    rw [mul_pow, ← Real.exp_nat_mul]
    nlinarith [mul_nonneg (sub_nonneg.mpr (hvn.trans huPow)) (sub_nonneg.mpr he)]
  have hr := r_bounds u hu01
  have h1 : 0 ≤ 1 - u := by linarith [hu01.2]
  have hmul := mul_le_mul hk hru (by norm_num : (0 : ℝ) ≤ 1 / 12)
    (by linarith : 0 ≤ K u)
  have hmul2 := mul_le_mul hmul (by linarith [hr.2] : 1 - u ≤ 1 - r u) h1
    (mul_nonneg (by linarith : 0 ≤ K u) (pow_nonneg hr.1 _))
  norm_num at hmul2
  linarith

private lemma window_integral_lower (n : ℕ) (hn : 4 ≤ n) :
    1 / (512 * (n : ℝ) ^ 2) ≤ ∫ u in
      (1 - 1 / (n : ℝ))..(1 - 1 / (2 * (n : ℝ))), K u * r u ^ n * (1 - r u) := by
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have ha0 : 0 ≤ 1 - 1 / (n : ℝ) := by
    rw [sub_nonneg, div_le_one₀ hn0]; linarith
  have hab : 1 - 1 / (n : ℝ) ≤ 1 - 1 / (2 * (n : ℝ)) := by
    apply sub_le_sub_left
    apply one_div_le_one_div_of_le hn0
    linarith
  have hi := intervalIntegral.integral_mono_on hab
    ((by fun_prop : Continuous (fun u : ℝ => (1 - u) / 192)).intervalIntegrable _ _)
    (gap_integrable n _ _ ha0 (ha0.trans hab)) (fun u hu => window_pointwise_lower n hn u hu)
  have he : (∫ u in (1 - 1 / (n : ℝ))..(1 - 1 / (2 * (n : ℝ))),
      (1 - u) / 192) = 1 / (512 * (n : ℝ) ^ 2) := by
    simp_rw [div_eq_mul_inv]
    rw [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_sub (f := fun _ : ℝ => 1) (g := fun u : ℝ => u)
        (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _),
      intervalIntegral.integral_const, integral_id]
    ring_nf
  rw [he] at hi
  exact hi

private lemma main_gap_lower (n : ℕ) (hn : 4 ≤ n) :
    1 / (512 * (n : ℝ) ^ 2) - Real.exp (-(n : ℝ)) ≤ A n - A (n + 1) := by
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  let a : ℝ := 1 - 1 / (n : ℝ)
  let b : ℝ := 1 - 1 / (2 * (n : ℝ))
  have ha : (1 / 2 : ℝ) ≤ a := by
    dsimp [a]
    have hdiv : 1 / (n : ℝ) ≤ 1 / 2 := by
      rw [div_le_iff₀ hn0]
      nlinarith
    linarith
  have hab : a ≤ b := by
    dsimp [a, b]
    apply sub_le_sub_left
    apply one_div_le_one_div_of_le hn0
    linarith
  have hb : b ≤ 1 := by
    dsimp [b]
    linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ 2 * (n : ℝ))]
  have hpos (u : ℝ) (hu : u ∈ Set.Icc (1 / 2 : ℝ) 1) :
      0 ≤ K u * r u ^ n * (1 - r u) := by
    have hu0 : 0 ≤ u := by linarith [hu.1]
    have hr := r_bounds u ⟨hu0, hu.2⟩
    have hk : 0 ≤ K u := by
      unfold K
      apply div_nonneg
      · linarith [hu.1]
      · positivity
    exact mul_nonneg (mul_nonneg hk (pow_nonneg hr.1 _)) (by linarith [hr.2, hu.2])
  have hl := intervalIntegral.integral_nonneg (μ := volume) ha (fun u hu =>
    hpos u ⟨hu.1, le_trans hu.2 (hab.trans hb)⟩)
  have hr := intervalIntegral.integral_nonneg (μ := volume) hb (fun u hu =>
    hpos u ⟨le_trans (ha.trans hab) hu.1, hu.2⟩)
  have hs0 := intervalIntegral.integral_add_adjacent_intervals
    (gap_integrable n 0 (1 / 2) (by norm_num) (by norm_num))
    (gap_integrable n (1 / 2) 1 (by norm_num) (by norm_num))
  have hs1 := intervalIntegral.integral_add_adjacent_intervals
    (gap_integrable n (1 / 2) a (by norm_num) (by linarith))
    (gap_integrable n a b (by linarith) (by linarith))
  have hs2 := intervalIntegral.integral_add_adjacent_intervals
    (gap_integrable n (1 / 2) b (by norm_num) (by linarith))
    (gap_integrable n b 1 (by linarith) (by norm_num))
  rw [main_gap_eq_integral n (by omega)]
  have hw := window_integral_lower n hn
  have hm := negative_piece_lower n
  change 1 / (512 * (n : ℝ) ^ 2) ≤ ∫ u in a..b, K u * r u ^ n * (1 - r u) at hw
  linarith

private lemma p_gap_lower (n : ℕ) (hn : 4 ≤ n) :
    1 / (512 * (n : ℝ) ^ 2) - (4 * (n : ℝ) + 3) * Real.exp (-(n : ℝ)) ≤
      p n - p (n + 1) := by
  have ht := tail_bounds n (by omega)
  have ht1 := tail_bounds (n + 1) (by omega)
  have hs (m : ℕ) (hm : 1 ≤ m) : |(-1 : ℝ) ^ (m - 1) * T m| = T m := by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (tail_bounds m hm).1]
  have hs0 := neg_abs_le ((-1 : ℝ) ^ (n - 1) * T n)
  have hs1 := le_abs_self ((-1 : ℝ) ^ n * T (n + 1))
  rw [hs n (by omega)] at hs0
  have habs : |(-1 : ℝ) ^ n * T (n + 1)| = T (n + 1) := by
    simpa using hs (n + 1) (by omega)
  rw [habs] at hs1
  have he : Real.exp (-((n + 1 : ℕ) : ℝ)) ≤ Real.exp (-(n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    push_cast
    linarith
  have heprod := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2 * ((n + 1 : ℕ) : ℝ))
  rw [p_split n (by omega), p_split (n + 1) (by omega)]
  simp only [Nat.add_sub_cancel] at *
  push_cast at ht1 heprod
  linarith [main_gap_lower n hn]

private lemma exp_prefactor_lt (n : ℕ) (hn : 16 ≤ n) :
    512 * (n : ℝ) ^ 2 * (4 * (n : ℝ) + 3) < Real.exp (n : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base =>
    have he : (163 / 60 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    have hp : (8781824 : ℝ) < (163 / 60 : ℝ) ^ 16 := by norm_num
    have hex := pow_lt_pow_left₀ he (by norm_num : (0 : ℝ) ≤ 163 / 60) (by norm_num : (16 : ℕ) ≠ 0)
    have hpow : Real.exp (16 : ℝ) = Real.exp 1 ^ 16 := by
      convert Real.exp_nat_mul 1 16 using 1
      norm_num
    norm_num only [Nat.cast_ofNat]
    rw [hpow]
    exact hp.trans hex
  | succ n hn ih =>
    have hn16 : (16 : ℝ) ≤ n := by exact_mod_cast hn
    have hc : 3 * ((n : ℝ) + 1) ^ 2 * (4 * (n : ℝ) + 7) ≤
        8 * (n : ℝ) ^ 2 * (4 * (n : ℝ) + 3) := by
      have h0 : 0 ≤ (n : ℝ) - 16 := by linarith
      have h2 := sq_nonneg ((n : ℝ) - 16)
      have h3 := pow_nonneg h0 3
      nlinarith
    have he : (8 / 3 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    have hp : 0 < 512 * (n : ℝ) ^ 2 * (4 * (n : ℝ) + 3) := by positivity
    have hg := mul_lt_mul_of_pos_right he hp
    have hi := mul_lt_mul_of_pos_right ih (Real.exp_pos 1)
    rw [Nat.cast_add, Nat.cast_one, Real.exp_add]
    nlinarith

private lemma exp_error_lt_gap (n : ℕ) (hn : 16 ≤ n) :
    (4 * (n : ℝ) + 3) * Real.exp (-(n : ℝ)) < 1 / (512 * (n : ℝ) ^ 2) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have he := exp_prefactor_lt n hn
  rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_div_iff₀ (Real.exp_pos _) (by positivity)]
  simpa only [mul_comm, one_mul] using he

private lemma succ_lt (n : ℕ) (hn : 5 ≤ n) : p (n + 1) < p n := by
  by_cases hlarge : 16 ≤ n
  · have hg := p_gap_lower n (by omega)
    have he := exp_error_lt_gap n hlarge
    linarith
  · have hn15 : n ≤ 15 := by omega
    apply Rat.cast_lt.mpr
    apply sub_pos.mp
    interval_cases n <;> norm_num [pRat, Finset.sum_range_succ, Nat.factorial]

private lemma main_error_bound (n : ℕ) (hn : 1 ≤ n) :
    |A n - (1 / 4 : ℝ)| ≤ 2 / ((n : ℝ) + 1) := by
  have hi : IntervalIntegrable (fun u : ℝ => |K u * r u ^ n|) volume 0 1 :=
    ((kernel_continuous n).abs.mono (by intro u hu; exact hu.1)).intervalIntegrable_of_Icc
      zero_le_one
  have hm := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1) zero_le_one hi
    ((by fun_prop : Continuous (fun u : ℝ => 2 * u ^ n)).intervalIntegrable _ _)
    (fun u hu => show |K u * r u ^ n| ≤ 2 * u ^ n from by
      have hr := r_bounds u hu
      rw [abs_mul, abs_of_nonneg (pow_nonneg hr.1 _)]
      exact mul_le_mul (kernel_abs_le_two u hu) (pow_le_pow_left₀ hr.1 hr.2 _)
        (pow_nonneg hr.1 _) (by norm_num))
  rw [intervalIntegral.integral_const_mul, integral_pow] at hm
  simp only [one_pow, zero_pow (Nat.succ_ne_zero n), sub_zero, mul_one_div] at hm
  rw [main_eq_kernel n hn, add_sub_cancel_left]
  exact (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans hm

private lemma p_error_bound (n : ℕ) (hn : 16 ≤ n) :
    |p n - (1 / 4 : ℝ)| ≤ 3 / (n : ℝ) := by
  have hn16 : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have he := exp_error_lt_gap n hn
  have he0 : Real.exp (-(n : ℝ)) ≤ 1 / (512 * (n : ℝ) ^ 2) := by
    have hm := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ 4 * (n : ℝ) + 3)
      (Real.exp_nonneg (-(n : ℝ)))
    linarith
  have ht := tail_bounds n (by omega)
  have htail : T n ≤ 1 / (n : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left he0 (by positivity : 0 ≤ 2 * (n : ℝ))
    have hrat : 2 * (n : ℝ) * (1 / (512 * (n : ℝ) ^ 2)) ≤ 1 / (n : ℝ) := by
      field_simp (disch := first | assumption | positivity)
      nlinarith
    exact ht.2.trans (hm.trans hrat)
  have hmain := main_error_bound n (by omega)
  have hrat : 2 / ((n : ℝ) + 1) ≤ 2 / (n : ℝ) := by
    exact div_le_div_of_nonneg_left (by norm_num) hnpos (by linarith)
  rw [p_split n (by omega)]
  calc
    _ = |(A n - (1 / 4 : ℝ)) + (-1 : ℝ) ^ (n - 1) * T n| := by congr 1; ring
    _ ≤ |A n - (1 / 4 : ℝ)| + |(-1 : ℝ) ^ (n - 1) * T n| := abs_add_le _ _
    _ ≤ 3 / (n : ℝ) := by
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg ht.1]
      rw [show (3 : ℝ) / n = 2 / n + 1 / n by ring]
      linarith

private lemma p_tendsto : Filter.Tendsto p Filter.atTop (𝓝 (1 / 4 : ℝ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  rw [show (fun n => ‖p n - (1 / 4 : ℝ)‖) = (fun n => |p n - (1 / 4 : ℝ)|) from by
    funext n; exact Real.norm_eq_abs _]
  exact squeeze_zero' (Filter.Eventually.of_forall (fun n => abs_nonneg _))
    (Filter.eventually_atTop.mpr ⟨16, fun n hn => p_error_bound n hn⟩)
    (tendsto_const_div_atTop_nhds_zero_nat (3 : ℝ))

theorem result : claim := ⟨succ_lt, p_tendsto⟩

end D5.S3.Quantum.FockSpace.IdealHeraldingRateMonotonicity
