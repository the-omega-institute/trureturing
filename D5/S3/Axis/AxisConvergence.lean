/- GID: D5/S3/Axis/AxisConvergence
   generality: I
   mirror-B: D5/B/S3/Axis/AxisConvergence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Axis word sums converge with an explicit double-exponential tail bound. -/

import D5.S3.AnalyticClosure.PositiveSeriesTail
import D5.S3.Axis.AxisPartialSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/- Library-search and duplication audit (2026-09-05):
   * D5, digestion, digest, git-history, and in-flight searches for axis-word
     convergence, Zeckendorf exponential majorants, and double-exponential
     tails found no existing equivalent theorem.
   * `Nat.sum_zeckendorf_fib` identifies the represented integer;
     `Real.goldenRatio_mul_fib_succ_add_fib` compares Fibonacci numbers with
     golden powers.
   * Pinned Mathlib's `hasSum_geometric_of_lt_one`,
     `summable_geometric_of_lt_one`, `Summable.sum_add_tsum_nat_add`, and
     `Summable.tsum_le_tsum` supply the geometric-series tail calculation.
   * `PositiveSeriesTail.finite_partial_sum_lt_tsum_of_pos_outside` supplies
     the strict lower witness showing that the error estimate is nonvacuous. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Axis.AxisConvergence

open D5.S3.Axis.AxisPartialSum
open D5.S3.Axis.AxisTraceRecurrence
open D5.S3.AnalyticClosure.PositiveSeriesTail
open Real
open scoped BigOperators

noncomputable section

private def phiCoordinate (n : ℕ) : ℝ :=
  ((Nat.zeckendorf n).map fun j => goldenRatio ^ (j + 1)).sum

private def psiCoordinate (n : ℕ) : ℝ :=
  ((Nat.zeckendorf n).map fun j => goldenConj ^ (j + 1)).sum

private theorem product_axisWeight_eq (x y : ℝ) (digits : List ℕ) :
    (digits.map (axisWeight x y)).prod =
      Real.exp
        (-x * (digits.map fun j => goldenRatio ^ (j + 1)).sum +
          y * (digits.map fun j => goldenConj ^ (j + 1)).sum) := by
  induction digits with
  | nil => simp
  | cons j digits ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, axisWeight]
      rw [ih, ← Real.exp_add]
      congr 1
      ring

private theorem wordWeight_eq_exp_coordinates (x y : ℝ) (n : ℕ) :
    wordWeight x y n =
      Real.exp (-x * phiCoordinate n + y * psiCoordinate n) := by
  exact product_axisWeight_eq x y (Nat.zeckendorf n)

private theorem zeckendorf_phi_lower (n : ℕ) :
    (n : ℝ) ≤ phiCoordinate n := by
  have hpoint (j : ℕ) :
      (Nat.fib j : ℝ) ≤ goldenRatio ^ (j + 1) := by
    rw [← Real.goldenRatio_mul_fib_succ_add_fib j]
    have hnonneg : 0 ≤ goldenRatio * (Nat.fib (j + 1) : ℝ) := by positivity
    linarith
  calc
    (n : ℝ) = (((Nat.zeckendorf n).map Nat.fib).sum : ℝ) := by
      norm_cast
      exact (Nat.sum_zeckendorf_fib n).symm
    _ = ((Nat.zeckendorf n).map fun j => (Nat.fib j : ℝ)).sum := by
      induction Nat.zeckendorf n with
      | nil => simp
      | cons j digits ih =>
          simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]
    _ ≤ ((Nat.zeckendorf n).map fun j => goldenRatio ^ (j + 1)).sum := by
      exact List.sum_le_sum fun j _ => hpoint j
    _ = phiCoordinate n := rfl

private theorem zeckendorf_nodup (n : ℕ) : (Nat.zeckendorf n).Nodup := by
  letI : IsTrans ℕ (fun a b => b + 2 ≤ a) :=
    ⟨fun _ _ _ hab hbc => by omega⟩
  have hchain := Nat.isZeckendorfRep_zeckendorf n
  rw [List.IsZeckendorfRep, List.isChain_iff_pairwise] at hchain
  exact (List.pairwise_append.mp hchain).1.imp fun h => by omega

private theorem abs_list_sum_le_sum_abs (values : List ℝ) :
    |values.sum| ≤ (values.map abs).sum := by
  induction values with
  | nil => simp
  | cons value values ih =>
      simp only [List.sum_cons, List.map_cons]
      exact (abs_add_le value values.sum).trans (by
        simpa using add_le_add_left ih |value|)

private theorem goldenConj_abs_lt_one : |goldenConj| < 1 := by
  rw [abs_of_neg Real.goldenConj_neg]
  linarith [Real.neg_one_lt_goldenConj]

private theorem geometric_conjugate_hasSum :
    HasSum (fun j : ℕ => |goldenConj| ^ (j + 1))
      (|goldenConj| / (1 - |goldenConj|)) := by
  have h :=
    (hasSum_geometric_of_lt_one (abs_nonneg goldenConj)
      goldenConj_abs_lt_one).mul_left |goldenConj|
  simpa only [pow_succ', div_eq_mul_inv] using h

private theorem zeckendorf_psi_abs_upper (n : ℕ) :
    |psiCoordinate n| ≤ |goldenConj| / (1 - |goldenConj|) := by
  let digits := Nat.zeckendorf n
  have hnodup : digits.Nodup := zeckendorf_nodup n
  have hfinite :
      ((digits.map fun j => |goldenConj| ^ (j + 1)).sum) ≤
        ∑' j : ℕ, |goldenConj| ^ (j + 1) := by
    rw [← List.sum_toFinset _ hnodup]
    exact geometric_conjugate_hasSum.summable.sum_le_tsum digits.toFinset
      (fun _ _ => by positivity)
  calc
    |psiCoordinate n| ≤
        (((digits.map fun j => goldenConj ^ (j + 1)).map abs).sum) := by
      change
        |(digits.map fun j => goldenConj ^ (j + 1)).sum| ≤
          ((digits.map fun j => goldenConj ^ (j + 1)).map abs).sum
      exact abs_list_sum_le_sum_abs
        (digits.map fun j => goldenConj ^ (j + 1))
    _ = ((digits.map fun j => |goldenConj| ^ (j + 1)).sum) := by
      induction digits with
      | nil => simp
      | cons j digits ih =>
          simp only [List.map_cons, List.sum_cons, abs_pow, ih]
    _ ≤ ∑' j : ℕ, |goldenConj| ^ (j + 1) := hfinite
    _ = |goldenConj| / (1 - |goldenConj|) :=
      geometric_conjugate_hasSum.tsum_eq

private theorem wordWeight_pos (x y : ℝ) (n : ℕ) : 0 < wordWeight x y n := by
  rw [wordWeight_eq_exp_coordinates]
  exact Real.exp_pos _

private theorem wordWeight_le_geometric (x y : ℝ) (hx : 0 < x) (n : ℕ) :
    wordWeight x y n ≤
      Real.exp (|y| * (|goldenConj| / (1 - |goldenConj|))) *
        Real.exp (-x) ^ n := by
  have hphi := zeckendorf_phi_lower n
  have hpsi := zeckendorf_psi_abs_upper n
  have hmain : -x * phiCoordinate n ≤ -x * n :=
    mul_le_mul_of_nonpos_left hphi (neg_nonpos.mpr hx.le)
  have hconj :
      y * psiCoordinate n ≤
        |y| * (|goldenConj| / (1 - |goldenConj|)) := by
    calc
      y * psiCoordinate n ≤ |y * psiCoordinate n| := le_abs_self _
      _ = |y| * |psiCoordinate n| := abs_mul _ _
      _ ≤ |y| * (|goldenConj| / (1 - |goldenConj|)) :=
        mul_le_mul_of_nonneg_left hpsi (abs_nonneg y)
  rw [wordWeight_eq_exp_coordinates]
  calc
    Real.exp (-x * phiCoordinate n + y * psiCoordinate n) ≤
        Real.exp
          (|y| * (|goldenConj| / (1 - |goldenConj|)) - x * n) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = Real.exp (|y| * (|goldenConj| / (1 - |goldenConj|))) *
          Real.exp (-x) ^ n := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

/-- In the window `0 < x`, all axis word weights are summable. -/
theorem wordWeight_summable (x y : ℝ) (hx : 0 < x) :
    Summable (wordWeight x y) := by
  have hr_nonneg : 0 ≤ Real.exp (-x) := (Real.exp_pos _).le
  have hr_lt : Real.exp (-x) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hmajor : Summable (fun n : ℕ =>
      Real.exp (|y| * (|goldenConj| / (1 - |goldenConj|))) *
        Real.exp (-x) ^ n) :=
    (summable_geometric_of_lt_one hr_nonneg hr_lt).mul_left _
  exact Summable.of_nonneg_of_le (fun n => (wordWeight_pos x y n).le)
    (wordWeight_le_geometric x y hx) hmajor

private theorem geometric_tail_bound (x y : ℝ) (hx : 0 < x) (N : ℕ) :
    |(∑ n ∈ Finset.range N, wordWeight x y n) -
        ∑' n, wordWeight x y n| ≤
      Real.exp (|y| * (|goldenConj| / (1 - |goldenConj|))) *
          Real.exp (-x) ^ N /
        (1 - Real.exp (-x)) := by
  let amplitude :=
    Real.exp (|y| * (|goldenConj| / (1 - |goldenConj|)))
  let ratio := Real.exp (-x)
  have hratio_nonneg : 0 ≤ ratio := (Real.exp_pos _).le
  have hratio_lt : ratio < 1 := by
    dsimp only [ratio]
    rw [Real.exp_lt_one_iff]
    linarith
  have hsum := wordWeight_summable x y hx
  have hpartial_le :
      (∑ n ∈ Finset.range N, wordWeight x y n) ≤
        ∑' n, wordWeight x y n :=
    hsum.sum_le_tsum (Finset.range N) fun n _ => (wordWeight_pos x y n).le
  have hsplit := hsum.sum_add_tsum_nat_add N
  have habs :
      |(∑ n ∈ Finset.range N, wordWeight x y n) -
          ∑' n, wordWeight x y n| =
        ∑' n, wordWeight x y (n + N) := by
    rw [abs_of_nonpos (sub_nonpos.mpr hpartial_le)]
    linarith [hsplit]
  have hmajorShift :
      HasSum (fun n : ℕ => amplitude * ratio ^ (n + N))
        (amplitude * ratio ^ N / (1 - ratio)) := by
    have h :=
      (hasSum_geometric_of_lt_one hratio_nonneg hratio_lt).mul_left
        (amplitude * ratio ^ N)
    rw [div_eq_mul_inv]
    refine HasSum.congr_fun h ?_
    intro n
    rw [pow_add]
    ring
  have htail :
      (∑' n, wordWeight x y (n + N)) ≤
        amplitude * ratio ^ N / (1 - ratio) := by
    calc
      (∑' n, wordWeight x y (n + N)) ≤
          ∑' n, amplitude * ratio ^ (n + N) := by
        exact ((summable_nat_add_iff N).mpr hsum).tsum_le_tsum
          (fun n => by
            simpa only [amplitude, ratio] using
              wordWeight_le_geometric x y hx (n + N))
          hmajorShift.summable
      _ = amplitude * ratio ^ N / (1 - ratio) := hmajorShift.tsum_eq
  rw [habs]
  simpa only [amplitude, ratio] using htail

private theorem goldenRatio_pow_div_le_fib_succ (K : ℕ) :
    goldenRatio ^ K / goldenRatio ≤ (Nat.fib (K + 1) : ℝ) := by
  have hfib : (Nat.fib K : ℝ) ≤ Nat.fib (K + 1) := by
    exact_mod_cast Nat.fib_mono (Nat.le_succ K)
  have hscaled :
      goldenRatio ^ K * goldenRatio ≤
        ((Nat.fib (K + 1) : ℝ) * goldenRatio) * goldenRatio := by
    calc
      goldenRatio ^ K * goldenRatio = goldenRatio ^ (K + 1) := by
        rw [pow_succ]
      _ = goldenRatio * Nat.fib (K + 1) + Nat.fib K :=
        (Real.goldenRatio_mul_fib_succ_add_fib K).symm
      _ ≤ goldenRatio * Nat.fib (K + 1) + Nat.fib (K + 1) := by
        linarith
      _ = ((Nat.fib (K + 1) : ℝ) * goldenRatio) * goldenRatio := by
        calc
          goldenRatio * Nat.fib (K + 1) + Nat.fib (K + 1) =
              (Nat.fib (K + 1) : ℝ) * (goldenRatio + 1) := by ring
          _ = (Nat.fib (K + 1) : ℝ) * goldenRatio ^ 2 := by
            rw [Real.goldenRatio_sq]
          _ = ((Nat.fib (K + 1) : ℝ) * goldenRatio) * goldenRatio := by ring
  have hbase : goldenRatio ^ K ≤ (Nat.fib (K + 1) : ℝ) * goldenRatio :=
    le_of_mul_le_mul_right hscaled Real.goldenRatio_pos
  exact (div_le_iff₀ Real.goldenRatio_pos).mpr (by simpa [mul_comm] using hbase)

/-- The truncation error has the explicit double-exponential bound from the
positive-axis convergence window. -/
theorem axisPartialSum_tsum_double_exponential_tail
    (x y : ℝ) (hx : 0 < x) (K : ℕ) :
    |axisPartialSum x y K - ∑' n, wordWeight x y n| ≤
      (Real.exp (|y| * (|goldenConj| / (1 - |goldenConj|))) /
          (1 - Real.exp (-x))) *
        Real.exp (-(x / goldenRatio) * goldenRatio ^ K) := by
  let amplitude :=
    Real.exp (|y| * (|goldenConj| / (1 - |goldenConj|)))
  let ratio := Real.exp (-x)
  let cutoff := Nat.fib (K + 1)
  have htail := geometric_tail_bound x y hx cutoff
  have hdenom : 0 < 1 - ratio := by
    dsimp only [ratio]
    rw [sub_pos, Real.exp_lt_one_iff]
    linarith
  have hconstant : 0 ≤ amplitude / (1 - ratio) := by positivity
  have hcutoff : goldenRatio ^ K / goldenRatio ≤ (cutoff : ℝ) :=
    goldenRatio_pow_div_le_fib_succ K
  have hexponent :
      -x * (cutoff : ℝ) ≤ -(x / goldenRatio) * goldenRatio ^ K := by
    have hmul := mul_le_mul_of_nonneg_left hcutoff hx.le
    calc
      -x * (cutoff : ℝ) = -(x * (cutoff : ℝ)) := by ring
      _ ≤ -(x * (goldenRatio ^ K / goldenRatio)) := neg_le_neg hmul
      _ = -(x / goldenRatio) * goldenRatio ^ K := by ring
  have hexp : ratio ^ cutoff ≤
      Real.exp (-(x / goldenRatio) * goldenRatio ^ K) := by
    rw [show ratio ^ cutoff = Real.exp (-x * (cutoff : ℝ)) by
      dsimp only [ratio]
      rw [← Real.exp_nat_mul]
      congr 1
      ring]
    exact Real.exp_le_exp.mpr hexponent
  change
    |(∑ n ∈ Finset.range cutoff, wordWeight x y n) -
        ∑' n, wordWeight x y n| ≤ _
  calc
    |(∑ n ∈ Finset.range cutoff, wordWeight x y n) -
          ∑' n, wordWeight x y n| ≤
        amplitude * ratio ^ cutoff / (1 - ratio) := by
      simpa only [amplitude, ratio] using htail
    _ = (amplitude / (1 - ratio)) * ratio ^ cutoff := by ring
    _ ≤ (amplitude / (1 - ratio)) *
        Real.exp (-(x / goldenRatio) * goldenRatio ^ K) :=
      mul_le_mul_of_nonneg_left hexp hconstant
    _ = (Real.exp (|y| * (|goldenConj| / (1 - |goldenConj|))) /
          (1 - Real.exp (-x))) *
        Real.exp (-(x / goldenRatio) * goldenRatio ^ K) := rfl

/-- Every finite truncation misses a positive word, so the upper tail bound
controls a genuinely nonzero error. -/
theorem axisPartialSum_lt_tsum (x y : ℝ) (hx : 0 < x) (K : ℕ) :
    axisPartialSum x y K < ∑' n, wordWeight x y n := by
  apply finite_partial_sum_lt_tsum_of_pos_outside
  · exact fun n => (wordWeight_pos x y n).le
  · exact wordWeight_summable x y hx
  · refine ⟨Nat.fib (K + 1), ?_, wordWeight_pos x y _⟩
    simp

#print axioms wordWeight_summable
#print axioms axisPartialSum_tsum_double_exponential_tail
#print axioms axisPartialSum_lt_tsum

end

end D5.S3.Axis.AxisConvergence
