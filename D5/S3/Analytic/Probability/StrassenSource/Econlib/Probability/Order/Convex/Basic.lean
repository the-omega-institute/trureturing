/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Probability.Distributions.Bernoulli
public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Probability.ProbDist.Support

/-!
# Convex order for real-valued probability laws

The **convex order** on `ProbDist ℝ` compares two laws with equal mean by their expectations under
convex test functions. This file states the relation on a compact interval `[a, b]`, so that
compact-support applications can exploit boundedness on `[a, b]` without a larger support calculus,
and records the basic order structure (reflexivity, transitivity, and the Dirac lower bound).

## Main definitions

* `ConvexOrderOnIcc a b` — `μ` is below `ν` when they share a mean and every convex function with
  continuous restriction to `[a, b]` has weakly larger expectation under `ν`.
* `ConvexOrder` — the unit-interval case `[0, 1]`, with notation `μ ≼cx ν`.

## Main statements

* `ConvexOrderOnIcc.refl`, `ConvexOrderOnIcc.trans` — the convex order is reflexive and transitive.
* `ConvexOrderOnIcc.dirac_left` — the Dirac mass at the mean of `μ` is below `μ`.

## References

* Rothschild, Michael, and Joseph E. Stiglitz. 1970. “Increasing Risk: I. A Definition.” *Journal
  of Economic Theory* 2 (3): 225–43. [https://doi.org/10.1016/0022-0531(70)90038-4](https://doi.org/10.1016/0022-0531(70)90038-4).

## Tags

convex order, mean-preserving spread, second-order stochastic dominance, dirac
-/

@[expose] public section

open MeasureTheory Set

namespace Econlib.Probability

/-- Binary Bernoulli mixtures preserve common support. -/
lemma ProbDist.supportsOn_binaryMixture (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (d₁ d₂ : ProbDist ℝ) {s : Set ℝ} (hs : MeasurableSet s)
    (hd₁ : d₁.supportsOn s) (hd₂ : d₂.supportsOn s) :
    (ProbDist.finMixture (FinDist.bernoulli q hq0 hq1)
      (fun i : Fin 2 => if i = 0 then d₁ else d₂)).supportsOn s := by
  refine ProbDist.supportsOn_finMixture (w := FinDist.bernoulli q hq0 hq1)
    (ds := fun i : Fin 2 => if i = 0 then d₁ else d₂) hs ?_
  intro i
  fin_cases i <;> simp [hd₁, hd₂]

/-- **Convex order** on the compact interval `[a, b]`. `μ` is below `ν` if both are supported on
`[a, b]`, they have the same mean, and every convex function on `[a, b]` with continuous
restriction to `[a, b]` has weakly larger expectation under `ν`. The equal-mean and
convex-inequality clauses are defining conjuncts; `mean_eq` and `convex_expect_le` are their
accessors. -/
structure ConvexOrderOnIcc (a b : ℝ) (μ ν : ProbDist ℝ) : Prop where
  /-- The lower law is supported on `[a, b]`. -/
  support_left : μ.supportsOn (Set.Icc a b)
  /-- The upper law is supported on `[a, b]`. -/
  support_right : ν.supportsOn (Set.Icc a b)
  /-- Convex-ordered laws have equal mean. -/
  mean_eq : μ.expect id = ν.expect id
  /-- Every convex function with continuous restriction to `[a, b]` has weakly larger expectation
  under the upper law. -/
  convex_expect_le : ∀ φ : ℝ → ℝ, ConvexOn ℝ (Set.Icc a b) φ → ContinuousOn φ (Set.Icc a b) →
    μ.expect φ ≤ ν.expect φ

/-- The unit-interval convex order used by the CrossSubsidy application. -/
abbrev ConvexOrder (μ ν : ProbDist ℝ) : Prop :=
  ConvexOrderOnIcc 0 1 μ ν

notation:50 μ " ≼cx[" a "," b "] " ν => ConvexOrderOnIcc a b μ ν
notation:50 μ " ≼cx " ν => ConvexOrder μ ν

/-- The convex order is reflexive on laws supported on `[a, b]`. -/
lemma ConvexOrderOnIcc.refl {a b : ℝ} {μ : ProbDist ℝ}
    (hμ : μ.supportsOn (Set.Icc a b)) : ConvexOrderOnIcc a b μ μ :=
  ⟨hμ, hμ, rfl, fun _ _ _ => le_rfl⟩

/-- Equal laws supported on `[a, b]` are convex-ordered. -/
lemma ConvexOrderOnIcc.of_eq {a b : ℝ} {μ ν : ProbDist ℝ}
    (hμ : μ.supportsOn (Set.Icc a b)) (h : μ = ν) : ConvexOrderOnIcc a b μ ν := by
  subst h
  exact ConvexOrderOnIcc.refl hμ

/-- The convex order is transitive. -/
lemma ConvexOrderOnIcc.trans {a b : ℝ} {μ ν ξ : ProbDist ℝ}
    (hμν : ConvexOrderOnIcc a b μ ν) (hνξ : ConvexOrderOnIcc a b ν ξ) :
    ConvexOrderOnIcc a b μ ξ :=
  ⟨hμν.support_left, hνξ.support_right, hμν.mean_eq.trans hνξ.mean_eq,
    fun φ hφ hφ_cont => le_trans (hμν.convex_expect_le φ hφ hφ_cont)
      (hνξ.convex_expect_le φ hφ hφ_cont)⟩

/-- **Dirac lower bound.** The point mass at the mean of `μ` is below `μ` in the convex order: The
least dispersed law with that mean. -/
lemma ConvexOrderOnIcc.dirac_left {a b : ℝ} {μ : ProbDist ℝ}
    (hμ : μ.supportsOn (Set.Icc a b)) :
    ConvexOrderOnIcc a b (ProbDist.dirac (μ.expect id)) μ := by
  have hm : μ.expect id ∈ Set.Icc a b := ProbDist.expect_mem_Icc (d := μ) hμ
  refine ⟨ProbDist.supportsOn_dirac measurableSet_Icc hm, hμ, ?_, ?_⟩
  · simp [ProbDist.expect_dirac]
  · intro φ hφ hφ_cont
    have hmem : ∀ᵐ x ∂μ.toMeasure, id x ∈ Set.Icc a b :=
      μ.ae_mem_of_supportsOn measurableSet_Icc hμ
    have hid_int : Integrable id μ.toMeasure :=
      ProbDist.integrable_id_of_supportsOn_Icc (d := μ) hμ
    have hφ_int : Integrable φ μ.toMeasure :=
      ProbDist.integrable_of_supportsOn_Icc (d := μ) hμ hφ_cont
    calc
      (ProbDist.dirac (μ.expect id)).expect φ = φ (μ.expect id) := ProbDist.expect_dirac _ _
      _ ≤ μ.expect φ := by
        simpa [ProbDist.expect, Function.comp] using
          hφ.map_integral_le hφ_cont isClosed_Icc hmem hid_int
            (by simpa [Function.comp] using hφ_int)

/-- **Dirac lower bound** on the unit interval: The point mass at the mean of `μ` is below `μ`. -/
lemma ConvexOrder.dirac_left {μ : ProbDist ℝ}
    (hμ : μ.supportsOn (Set.Icc 0 1)) :
    ConvexOrder (ProbDist.dirac (μ.expect id)) μ :=
  ConvexOrderOnIcc.dirac_left hμ

end Econlib.Probability
