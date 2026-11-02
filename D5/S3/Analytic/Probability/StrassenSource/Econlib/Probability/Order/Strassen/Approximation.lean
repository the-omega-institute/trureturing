/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Probability.Order.Strassen.CondMeanAtom.Convergence

/-!
# Discrete approximation of real-valued probability laws in convex order

To prove the hard direction of **Strassen's theorem**, a pair of laws `μ ≼cx[a,b] ν` is
approximated by a sequence of finitely-supported pairs `μₙ ≼cx νₙ` whose embedded laws converge
weakly to `μ` and `ν`. The approximating construction is **conditional-mean atomization**:
Partition the unit interval of quantile levels into `n` equal bins, place the `k`-th atom at the
bin-conditional mean of the quantile function, and weight each atom by `1/n`. This preserves means
exactly and preserves convex order via the Hardy–Littlewood–Pólya integrated-quantile
characterization.

## Main statements

* `exists_discrete_approximation` — given `μ ≼cx[a,b] ν`, there is a sequence
  `(pₙ, qₙ) : ℕ → DiscreteLaw × DiscreteLaw` with `pₙ.ConvexOrder qₙ`, both supported on `Icc a b`,
  and `pₙ.toProbDist → μ`, `qₙ.toProbDist → ν` weakly.

## Notes

The conditional-mean atomization and its convex-order and convergence properties are developed in
`Strassen/CondMeanAtom/`; the discrete case `DiscreteLaw.exists_martingaleCoupling_uniform` is in
`Strassen/Discrete.lean`.

## References

* Strassen, V. 1965. “The Existence of Probability Measures with Given Marginals.” *The Annals of
  Mathematical Statistics* 36 (2): 423–39. [https://doi.org/10.1214/aoms/1177700153](https://doi.org/10.1214/aoms/1177700153).

## Tags

strassen, convex order, discrete approximation, conditional-mean atomization
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace Econlib.Probability

/-- **Discrete approximation in convex order.** A pair `μ ≼cx[a,b] ν` of real-valued laws supported
on `[a, b]` admits a sequence of finitely-supported pairs `(pₙ, qₙ)` in convex order, with weak
convergence of the embedded laws to `μ` and `ν` respectively. -/
theorem exists_discrete_approximation {a b : ℝ} {μ ν : ProbDist ℝ}
    (h : ConvexOrderOnIcc a b μ ν) :
    ∃ p q : ℕ → DiscreteLaw,
      (∀ n, DiscreteLaw.ConvexOrder (p n) (q n)) ∧
      (∀ n, 0 < (p n).n) ∧
      (∀ n, (p n).n = (q n).n) ∧
      (∀ n i, (p n).weight i = (1 : ℝ) / (p n).n) ∧
      (∀ n j, (q n).weight j = (1 : ℝ) / (q n).n) ∧
      (∀ n i, (p n).atom i ∈ Icc a b) ∧
      (∀ n j, (q n).atom j ∈ Icc a b) ∧
      Tendsto (fun n => (p n).toProbDist : ℕ → ProbabilityMeasure ℝ) atTop (𝓝 μ) ∧
      Tendsto (fun n => (q n).toProbDist : ℕ → ProbabilityMeasure ℝ) atTop (𝓝 ν) := by
  refine ⟨fun n => DiscreteLaw.condMeanAtomize μ (n + 1) (Nat.succ_pos n),
          fun n => DiscreteLaw.condMeanAtomize ν (n + 1) (Nat.succ_pos n),
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun n =>
      DiscreteLaw.condMeanAtomize_convexOrder h (n + 1) (Nat.succ_pos n)
  · intro n
    simp [DiscreteLaw.condMeanAtomize_n]
  · intro n
    simp [DiscreteLaw.condMeanAtomize_n]
  · intro n i
    simp [DiscreteLaw.condMeanAtomize_weight, DiscreteLaw.condMeanAtomize_n]
  · intro n j
    simp [DiscreteLaw.condMeanAtomize_weight, DiscreteLaw.condMeanAtomize_n]
  · exact fun n i =>
      DiscreteLaw.condMeanAtom_mem_Icc h.support_left (n + 1) (Nat.succ_pos n) i
  · exact fun n j =>
      DiscreteLaw.condMeanAtom_mem_Icc h.support_right (n + 1) (Nat.succ_pos n) j
  · exact DiscreteLaw.condMeanAtomize_tendsto h.support_left
  · exact DiscreteLaw.condMeanAtomize_tendsto h.support_right

end Econlib.Probability
