/- GID: D5/S3/ArithSums/WolfordBinomialBiroot
   generality: G
   mirror-B: D5/B/S3/ArithSums/WolfordBinomialBiroot
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Positive weighted binomial multisections and the original generalized biroot quotient. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteStochasticMixing
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ArithSums.WolfordBinomialBiroot

open scoped BigOperators Topology
open Filter Matrix

variable {n : ℕ} [NeZero n]

private def shift : Matrix (ZMod n) (ZMod n) ℝ :=
  fun i j => if i + 1 = j then 1 else 0

private theorem shift_pow (m : ℕ) (i j : ZMod n) :
    (shift ^ m) i j = if i + (m : ZMod n) = j then 1 else 0 := by
  induction m generalizing i j with
  | zero => simp [Matrix.one_apply]
  | succ m ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp only [shift, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true, ih]
    congr 1
    push_cast
    ring_nf

private def walk (a b : ℝ) : Matrix (ZMod n) (ZMod n) ℝ :=
  a • 1 + b • shift

private theorem walk_nonneg (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (i j : ZMod n) : 0 ≤ walk a b i j := by
  simp only [walk, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  apply add_nonneg
  · exact mul_nonneg ha (by simp [Matrix.one_apply]; split_ifs <;> norm_num)
  · exact mul_nonneg hb (by simp [shift]; split_ifs <;> norm_num)

private theorem walk_stochastic (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : walk (n := n) a b ∈ Matrix.rowStochastic ℝ (ZMod n) := by
  apply Matrix.mem_rowStochastic_iff_sum.mpr
  refine ⟨walk_nonneg a b ha hb, ?_⟩
  intro i
  simpa [walk, shift, Matrix.one_apply, Finset.sum_add_distrib,
    Finset.mul_sum] using hab

end D5.S3.ArithSums.WolfordBinomialBiroot
