/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Math.Probability.QuantileIntegral
public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Probability.Order.Convex.StopLoss
public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Probability.Order.Strassen.Discrete
import Mathlib.MeasureTheory.Function.Floor

/-!
# Conditional-mean atomization: Definitions

The **conditional-mean atomization** of a probability law `μ` on `ℝ` replaces `μ` by the
uniform-weight discrete law whose `k`-th atom is the average of the quantile function of `μ` over
the `k`-th equal bin `(k/n, (k+1)/n]`. This discretization preserves the mean of each quantile bin
and produces the uniform finite laws used in Strassen approximation.

## Main definitions

* `DiscreteLaw.condMeanAtom` — the `k`-th conditional-mean atom of `μ`.
* `DiscreteLaw.condMeanAtomize` — the uniform discrete law with atoms at the conditional means.

## Notes

Properties of these definitions are proved in `CondMeanAtom.Properties`.

## Tags

quantile, conditional mean, atomization, discretization, convex order
-/

open MeasureTheory Set Filter Topology

@[expose] public noncomputable section

namespace Econlib.Probability
namespace DiscreteLaw

/-- The `k`-th conditional-mean atom of `μ`: The average of `quantile μ` over the bin
`(k/n, (k+1)/n]`. -/
noncomputable def condMeanAtom (μ : ProbDist ℝ) (n : ℕ) (_hn : 0 < n) (k : Fin n) : ℝ :=
  (n : ℝ) * ∫ u in Set.Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n),
    MeasureTheory.Measure.quantile μ.toMeasure u

/-- Uniform discrete law with atoms at conditional means of each equal bin. -/
noncomputable def condMeanAtomize (μ : ProbDist ℝ) (n : ℕ) (hn : 0 < n) : DiscreteLaw :=
  DiscreteLaw.uniform n hn (fun k => DiscreteLaw.condMeanAtom μ n hn k)

@[simp] lemma condMeanAtomize_n {μ : ProbDist ℝ} {n : ℕ} {hn : 0 < n} :
    (condMeanAtomize μ n hn).n = n := rfl

@[simp] lemma condMeanAtomize_atom {μ : ProbDist ℝ} {n : ℕ} {hn : 0 < n} {k : Fin n} :
    (condMeanAtomize μ n hn).atom k = condMeanAtom μ n hn k := rfl

@[simp] lemma condMeanAtomize_weight {μ : ProbDist ℝ} {n : ℕ} {hn : 0 < n} {k : Fin n} :
    (condMeanAtomize μ n hn).weight k = (1 : ℝ) / n := rfl

end DiscreteLaw
end Econlib.Probability

end
