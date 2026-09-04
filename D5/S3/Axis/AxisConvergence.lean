/- GID: D5/S3/Axis/AxisConvergence
   generality: I
   mirror-B: D5/B/S3/Axis/AxisConvergence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive-x axis partial sums converge with a doubly-exponential depth tail. -/

import D5.S3.Axis.AxisPartialSum
import Mathlib.Analysis.SpecificLimits.Basic

/- Library-search audit trail (2026-09-05):
   * `Summable.of_nonneg_of_le` and `summable_geometric_of_lt_one` turn the positive
     word-weight majorant into summability; no custom series criterion is introduced.
   * `HasSum.tendsto_sum_nat` gives convergence of the ordinary partial sums, and
     `Summable.sum_add_tsum_nat_add` isolates the exact tail after the Fibonacci cutoff.
   * `Real.goldenRatio_mul_fib_succ_add_fib` supplies the Fibonacci/golden-ratio comparison
     used to convert geometric decay in the word index into doubly-exponential decay in depth.
-/

namespace D5.S3.Axis.AxisConvergence

open Filter Topology BigOperators
open Nat Real
open D5.S3.Axis.AxisTraceRecurrence D5.S3.Axis.AxisPartialSum

local instance zeckendorfRelTrans : IsTrans ℕ (fun a b => b + 2 ≤ a) where
  trans _ _ _ hab hbc := hbc.trans (le_self_add.trans hab)

local instance zeckendorfRelIrrefl : Std.Irrefl (fun a b : ℕ => b + 2 ≤ a) where
  irrefl _ h := by omega

private theorem zeckendorf_nodup (n : ℕ) : (Nat.zeckendorf n).Nodup := by
  have hchain : ((Nat.zeckendorf n) ++ [0]).IsChain (fun a b : ℕ => b + 2 ≤ a) :=
    Nat.isZeckendorfRep_zeckendorf n
  have happ : ((Nat.zeckendorf n) ++ [0]).Nodup := hchain.pairwise.nodup
  exact List.Nodup.of_append_left happ

private theorem fib_le_goldenRatio_pow (j : ℕ) :
    (Nat.fib j : ℝ) ≤ Real.goldenRatio ^ (j + 1) := by
  have h := Real.goldenRatio_mul_fib_succ_add_fib j
  nlinarith [Real.goldenRatio_pos, Nat.cast_nonneg (α := ℝ) (Nat.fib (j + 1))]

private theorem zeckendorf_phi_lower (n : ℕ) :
    (n : ℝ) ≤ ((Nat.zeckendorf n).map
      (fun j => Real.goldenRatio ^ (j + 1))).sum := by
  have hcast : (((Nat.zeckendorf n).map Nat.fib).sum : ℝ) =
      ((Nat.zeckendorf n).map (fun j => (Nat.fib j : ℝ))).sum := by
    induction Nat.zeckendorf n with
    | nil => simp
    | cons j l ih => simp [ih]
  calc
    (n : ℝ) = (((Nat.zeckendorf n).map Nat.fib).sum : ℕ) := by
      exact congrArg (fun m : ℕ => (m : ℝ)) (Nat.sum_zeckendorf_fib n).symm
    _ = ((Nat.zeckendorf n).map (fun j => (Nat.fib j : ℝ))).sum := hcast
    _ ≤ ((Nat.zeckendorf n).map
        (fun j => Real.goldenRatio ^ (j + 1))).sum :=
      List.sum_le_sum fun j _ => fib_le_goldenRatio_pow j

private theorem goldenConj_abs_lt_one : |Real.goldenConj| < 1 := by
  rw [abs_of_neg Real.goldenConj_neg]
  linarith [Real.neg_one_lt_goldenConj]

private theorem goldenConj_budget :
    (∑' j : ℕ, |Real.goldenConj| ^ (j + 1)) =
      |Real.goldenConj| / (1 - |Real.goldenConj|) := by
  rw [show (fun j : ℕ => |Real.goldenConj| ^ (j + 1)) =
      fun j => |Real.goldenConj| ^ j * |Real.goldenConj| by
        funext j; rw [pow_succ]]
  rw [tsum_mul_right, tsum_geometric_of_lt_one (abs_nonneg _) goldenConj_abs_lt_one]
  simp only [div_eq_mul_inv]
  ring

private theorem zeckendorf_psi_abs_upper (n : ℕ) :
    |((Nat.zeckendorf n).map
        (fun j => Real.goldenConj ^ (j + 1))).sum| ≤
      |Real.goldenConj| / (1 - |Real.goldenConj|) := by
  let s := (Nat.zeckendorf n).toFinset
  have hsum :
      ((Nat.zeckendorf n).map (fun j => Real.goldenConj ^ (j + 1))).sum =
        ∑ j ∈ s, Real.goldenConj ^ (j + 1) := by
    simpa [s] using
      (List.sum_toFinset (fun j => Real.goldenConj ^ (j + 1))
        (zeckendorf_nodup n)).symm
  rw [hsum]
  calc
    |∑ j ∈ s, Real.goldenConj ^ (j + 1)|
        ≤ ∑ j ∈ s, |Real.goldenConj ^ (j + 1)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ s, |Real.goldenConj| ^ (j + 1) := by
          apply Finset.sum_congr rfl
          intro j _
          exact abs_pow _ _
    _ ≤ ∑' j : ℕ, |Real.goldenConj| ^ (j + 1) :=
      (summable_geometric_of_lt_one (abs_nonneg Real.goldenConj)
        goldenConj_abs_lt_one).mul_right |Real.goldenConj|
        |>.sum_le_tsum s (fun _ _ => pow_nonneg (abs_nonneg _) _)
    _ = |Real.goldenConj| / (1 - |Real.goldenConj|) := goldenConj_budget

private theorem wordWeight_eq_exp_sum (x y : ℝ) (n : ℕ) :
    wordWeight x y n = Real.exp (((Nat.zeckendorf n).map
      (fun j => -x * Real.goldenRatio ^ (j + 1) +
        y * Real.goldenConj ^ (j + 1))).sum) := by
  simp only [wordWeight]
  induction Nat.zeckendorf n with
  | nil => simp
  | cons j l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [ih]
      change Real.exp (-x * Real.goldenRatio ^ (j + 1) +
          y * Real.goldenConj ^ (j + 1)) * Real.exp _ = Real.exp _
      rw [← Real.exp_add]

private theorem wordWeight_nonneg (x y : ℝ) (n : ℕ) : 0 ≤ wordWeight x y n := by
  rw [wordWeight_eq_exp_sum]
  positivity

private theorem wordWeight_le_geometric (x y : ℝ) (hx : 0 < x) (n : ℕ) :
    wordWeight x y n ≤
      Real.exp (|y| * (|Real.goldenConj| / (1 - |Real.goldenConj|))) *
        Real.exp (-x) ^ n := by
  let p : ℝ := ((Nat.zeckendorf n).map
    (fun j => Real.goldenRatio ^ (j + 1))).sum
  let q : ℝ := ((Nat.zeckendorf n).map
    (fun j => Real.goldenConj ^ (j + 1))).sum
  have hp : (n : ℝ) ≤ p := zeckendorf_phi_lower n
  have hq : |q| ≤ |Real.goldenConj| / (1 - |Real.goldenConj|) :=
    zeckendorf_psi_abs_upper n
  have hyq : y * q ≤ |y| * (|Real.goldenConj| / (1 - |Real.goldenConj|)) := by
    calc
      y * q ≤ |y * q| := le_abs_self _
      _ = |y| * |q| := abs_mul _ _
      _ ≤ |y| * (|Real.goldenConj| / (1 - |Real.goldenConj|)) := by gcongr
  rw [wordWeight_eq_exp_sum]
  have hsum : (((Nat.zeckendorf n).map
      (fun j => -x * Real.goldenRatio ^ (j + 1) +
        y * Real.goldenConj ^ (j + 1))).sum) = -x * p + y * q := by
    simp only [p, q, List.sum_map_add, List.sum_map_mul_left]
  rw [hsum]
  calc
    Real.exp (-x * p + y * q)
        ≤ Real.exp (-x * (n : ℝ) +
          |y| * (|Real.goldenConj| / (1 - |Real.goldenConj|))) := by
            apply Real.exp_le_exp.mpr
            nlinarith
    _ = Real.exp (|y| * (|Real.goldenConj| / (1 - |Real.goldenConj|))) *
          Real.exp (-x) ^ n := by
            rw [Real.exp_add, mul_comm]
            congr 1
            rw [← Real.exp_nat_mul]
            congr 1
            ring

/-- For positive first coordinate, all legal-word weights form a summable series. -/
theorem wordWeight_summable (x y : ℝ) (hx : 0 < x) : Summable (wordWeight x y) := by
  have hr0 : 0 ≤ Real.exp (-x) := (Real.exp_pos _).le
  have hr1 : Real.exp (-x) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  exact Summable.of_nonneg_of_le
    (wordWeight_nonneg x y)
    (wordWeight_le_geometric x y hx)
    ((summable_geometric_of_lt_one hr0 hr1).mul_left
      (Real.exp (|y| * (|Real.goldenConj| / (1 - |Real.goldenConj|)))))

private theorem tendsto_fib_succ_atTop :
    Tendsto (fun K : ℕ => Nat.fib (K + 1)) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop (max b 5)] with K hK
  have hb : b ≤ K := (le_max_left b 5).trans hK
  have h5 : 5 ≤ K := (le_max_right b 5).trans hK
  exact (hb.trans (Nat.le_fib_self h5)).trans Nat.fib_le_fib_succ

/-- The depth-truncated legal-word sums converge to the full word-weight series. -/
theorem axisPartialSum_tendsto (x y : ℝ) (hx : 0 < x) :
    Tendsto (axisPartialSum x y) atTop (𝓝 (∑' n, wordWeight x y n)) := by
  have h := (wordWeight_summable x y hx).hasSum.tendsto_sum_nat.comp
    tendsto_fib_succ_atTop
  change Tendsto (fun K => ∑ n ∈ Finset.range (Nat.fib (K + 1)),
    wordWeight x y n) atTop (𝓝 (∑' n, wordWeight x y n)) at h
  change Tendsto (fun K => ∑ n ∈ Finset.range (Nat.fib (K + 1)),
    wordWeight x y n) atTop (𝓝 (∑' n, wordWeight x y n))
  exact h

private theorem axisPartialSum_tail_geometric (x y : ℝ) (hx : 0 < x) (K : ℕ) :
    |axisPartialSum x y K - ∑' n, wordWeight x y n| ≤
      Real.exp (|y| * (|Real.goldenConj| / (1 - |Real.goldenConj|))) *
        Real.exp (-x) ^ (Nat.fib (K + 1)) * (1 - Real.exp (-x))⁻¹ := by
  let A := Real.exp (|y| *
    (|Real.goldenConj| / (1 - |Real.goldenConj|)))
  let r := Real.exp (-x)
  let N := Nat.fib (K + 1)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    simp only [r, Real.exp_lt_one_iff]
    linarith
  have hword := wordWeight_summable x y hx
  have htail : Summable (fun i : ℕ => wordWeight x y (i + N)) :=
    (summable_nat_add_iff N).mpr hword
  have hmajorant : Summable (fun i : ℕ => A * r ^ (i + N)) := by
    rw [show (fun i : ℕ => A * r ^ (i + N)) =
        fun i => (A * r ^ N) * r ^ i by
      funext i
      rw [pow_add]
      ring]
    exact (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have htail_le : (∑' i : ℕ, wordWeight x y (i + N)) ≤
      ∑' i : ℕ, A * r ^ (i + N) := by
    exact htail.tsum_mono hmajorant fun i => by
      simpa only [A, r] using wordWeight_le_geometric x y hx (i + N)
  have hmajorant_sum : (∑' i : ℕ, A * r ^ (i + N)) =
      A * r ^ N * (1 - r)⁻¹ := by
    rw [show (fun i : ℕ => A * r ^ (i + N)) =
        fun i => (A * r ^ N) * r ^ i by
      funext i
      rw [pow_add]
      ring]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  have hsplit := hword.sum_add_tsum_nat_add N
  have hdiff : axisPartialSum x y K - ∑' n, wordWeight x y n =
      -(∑' i : ℕ, wordWeight x y (i + N)) := by
    simp only [axisPartialSum, N] at hsplit ⊢
    linarith
  rw [hdiff, abs_neg, abs_of_nonneg (tsum_nonneg fun i => wordWeight_nonneg x y (i + N))]
  simpa only [A, r, N] using htail_le.trans_eq hmajorant_sum

private theorem goldenRatio_pow_div_le_fib_succ (K : ℕ) :
    Real.goldenRatio ^ K / Real.goldenRatio ≤ (Nat.fib (K + 1) : ℝ) := by
  have hphi := Real.goldenRatio_pos
  rw [div_le_iff₀ hphi]
  have hrec := Real.goldenRatio_mul_fib_succ_add_fib K
  have hpow : Real.goldenRatio ^ (K + 1) =
      Real.goldenRatio ^ K * Real.goldenRatio := pow_succ _ _
  have hsq := Real.goldenRatio_sq
  have hfib : (Nat.fib K : ℝ) ≤ (Nat.fib (K + 1) : ℝ) := by
    exact_mod_cast Nat.fib_le_fib_succ
  have hpow0 : 0 ≤ Real.goldenRatio ^ K := pow_nonneg hphi.le _
  have hfib0 : 0 ≤ (Nat.fib (K + 1) : ℝ) := by positivity
  nlinarith

private theorem geometric_at_fib_le_double_exp (x : ℝ) (hx : 0 < x) (K : ℕ) :
    Real.exp (-x) ^ (Nat.fib (K + 1)) ≤
      Real.exp (-(x / Real.goldenRatio) * Real.goldenRatio ^ K) := by
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have h := goldenRatio_pow_div_le_fib_succ K
  have hphi := Real.goldenRatio_pos
  rw [div_eq_mul_inv] at h ⊢
  nlinarith [inv_pos.mpr hphi]

/-- The truncation error is doubly exponentially small in the digit depth. -/
theorem axisPartialSum_tail_bound (x y : ℝ) (hx : 0 < x) (K : ℕ) :
    |axisPartialSum x y K - ∑' n, wordWeight x y n| ≤
      (Real.exp (|y| *
          (|Real.goldenConj| / (1 - |Real.goldenConj|))) /
        (1 - Real.exp (-x))) *
          Real.exp (-(x / Real.goldenRatio) * Real.goldenRatio ^ K) := by
  have htail := axisPartialSum_tail_geometric x y hx K
  have hrate := geometric_at_fib_le_double_exp x hx K
  have hconst : 0 ≤ Real.exp (|y| *
      (|Real.goldenConj| / (1 - |Real.goldenConj|))) *
        (1 - Real.exp (-x))⁻¹ := by
    have hr : Real.exp (-x) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    positivity
  calc
    |axisPartialSum x y K - ∑' n, wordWeight x y n|
        ≤ Real.exp (|y| *
            (|Real.goldenConj| / (1 - |Real.goldenConj|))) *
          Real.exp (-x) ^ (Nat.fib (K + 1)) *
            (1 - Real.exp (-x))⁻¹ := htail
    _ = (Real.exp (|y| *
          (|Real.goldenConj| / (1 - |Real.goldenConj|))) *
            (1 - Real.exp (-x))⁻¹) *
          Real.exp (-x) ^ (Nat.fib (K + 1)) := by ring
    _ ≤ (Real.exp (|y| *
          (|Real.goldenConj| / (1 - |Real.goldenConj|))) *
            (1 - Real.exp (-x))⁻¹) *
          Real.exp (-(x / Real.goldenRatio) * Real.goldenRatio ^ K) := by
      exact mul_le_mul_of_nonneg_left hrate hconst
    _ = (Real.exp (|y| *
          (|Real.goldenConj| / (1 - |Real.goldenConj|))) /
            (1 - Real.exp (-x))) *
          Real.exp (-(x / Real.goldenRatio) * Real.goldenRatio ^ K) := by
      simp only [div_eq_mul_inv]

private theorem wordWeight_zero_zero (n : ℕ) : wordWeight 0 0 n = 1 := by
  rw [wordWeight_eq_exp_sum]
  simp

/-- At the omitted boundary point, the depth partial sum is exactly Fibonacci growth. -/
theorem axisPartialSum_zero_zero (K : ℕ) :
    axisPartialSum 0 0 K = (Nat.fib (K + 1) : ℝ) := by
  simp [axisPartialSum, wordWeight_zero_zero]

/-- The omitted boundary sequence diverges to positive infinity. -/
theorem axisPartialSum_zero_zero_tendsto_atTop :
    Tendsto (axisPartialSum 0 0) atTop atTop := by
  have hcast : Tendsto (fun K : ℕ => (Nat.fib (K + 1) : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp tendsto_fib_succ_atTop
  have heq : axisPartialSum 0 0 = (fun K : ℕ => (Nat.fib (K + 1) : ℝ)) := by
    funext K
    exact axisPartialSum_zero_zero K
  rw [heq]
  exact hcast

#print axioms wordWeight_summable
#print axioms axisPartialSum_tendsto
#print axioms axisPartialSum_tail_bound
#print axioms axisPartialSum_zero_zero
#print axioms axisPartialSum_zero_zero_tendsto_atTop

end D5.S3.Axis.AxisConvergence
