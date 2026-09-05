# Finite Product Absolute Continuity

## Abstract

Nondegenerate Boolean marginals have positive atoms, and their finite coordinatewise product dominates every measure on Boolean transcripts.

The law marginal p is the Boolean coordinate law with success probability p. It is defined in the frozen module InfiniteIdentificationFiniteInexactness and is used here through an import.

When every reference coordinate law is nondegenerate, its finite product charges every singleton transcript. A set that is null for the reference product must therefore be empty. Consequently any measure at all on the transcript space is absolutely continuous with respect to that product; the dominated measure's only role is to vanish on the empty set.

An earlier draft stated only the identically distributed case and asserted in its own prose that no strengthening was available. A review seat showed that claim was false: the same proof permits an arbitrary dominated measure and a coordinatewise family of reference laws. The theorem absolutelyContinuous_pi_marginal is the correction. The identically distributed form remains as a corollary because that is the shape the repository re-derives.

ConceptDynamics/ExperimentBoundary/FinitePrefixInfiniteCompletionSeparation and ConceptDynamics/ExperimentDesign/FinitePrefixInfiniteCompletionSeparation each carry a private copy of the identically distributed theorem and a private copy of the two-bound singleton-positivity theorem: four private declarations in total. Both modules are frozen, so they cannot import this module, and this change removes none of the four declarations.

This module has zero consumers today. The two single-outcome lemmas and the general domination theorem are strictly stronger than anything the repository currently states; the combined singleton lemma and the identically distributed corollary are API.

No claim of novel mathematics is made. The atomic proofs evaluate one Boolean outcome, the combined result is a case split, the general theorem applies singleton positivity coordinatewise, and the corollary is a one-step instantiation.

Pinned Mathlib has Measure.AbsolutelyContinuous.prod for binary products and Measure.pi_singleton for a singleton of a finite indexed product; the latter is used in the proof. The search found no upstream statement of this domination. That is a report of the search result, not a claim that no upstream form can exist.

**Theorem 1.1 (Positive success probability gives positive mass to true).**

$$\forall p \in unitInterval,\; 0 < (p: \mathbb{R}) \Rightarrow 0 < marginal\left(p\right)\left(\left\{true\right\}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiment/FiniteProductAbsoluteContinuity.marginal_true_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a point p of the unit interval, the sole hypothesis is that its real value is positive. Then marginal p assigns positive mass to true. No upper bound on p is assumed or needed.

**Theorem 1.2 (Success probability below one gives positive mass to false).**

$$\forall p \in unitInterval,\; (p: \mathbb{R}) < 1 \Rightarrow 0 < marginal\left(p\right)\left(\left\{false\right\}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiment/FiniteProductAbsoluteContinuity.marginal_false_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a point p of the unit interval, the sole hypothesis is that its real value is below one. Then marginal p assigns positive mass to false. No lower bound on p is assumed or needed.

**Theorem 1.3 (Every outcome of a nondegenerate Boolean marginal has positive mass).**

$$\forall p \in unitInterval,\; \left(0 < (p: \mathbb{R}) \land (p: \mathbb{R}) < 1\right) \Rightarrow \left(\forall outcome \in Bool,\; 0 < marginal\left(p\right)\left(\left\{outcome\right\}\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiment/FiniteProductAbsoluteContinuity.marginal_singleton_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the real value of p is strictly between zero and one, every Boolean outcome has positive singleton mass under marginal p. Both bounds are present because the quantified outcome may be either false or true.

**Theorem 1.4 (A finite nondegenerate marginal product dominates every measure).**

$$\begin{aligned}\forall Index: Type, [Fintype\left(Index\right)],\\\forall mu: Measure\left(Index \to Bool\right), q: Index \to unitInterval,\\\left(\forall i \in Index,\; 0 < (q\left(i\right): \mathbb{R})\right) \land \left(\forall i \in Index,\; (q\left(i\right): \mathbb{R}) < 1\right) \Rightarrow\\AbsolutelyContinuous\left(mu, MeasurePi\left(i: Index \mapsto marginal\left(q\left(i\right)\right)\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiment/FiniteProductAbsoluteContinuity.absolutelyContinuous_pi_marginal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Index be finite, let mu be an arbitrary measure on Boolean transcripts, and let q assign a unit-interval point to every coordinate. There is no hypothesis on mu. If every real value q i is positive and below one, then mu is absolutely continuous with respect to the product whose ith coordinate law is marginal of q i.

**Theorem 1.5 (One finite Boolean product law is dominated by a nondegenerate one).**

$$\begin{aligned}\forall Index: Type, [Fintype\left(Index\right)],\\\forall p, q: unitInterval,\\0 < (q: \mathbb{R}) \land (q: \mathbb{R}) < 1 \Rightarrow\\AbsolutelyContinuous\left(MeasurePi\left(i: Index \mapsto marginal\left(p\right)\right), MeasurePi\left(i: Index \mapsto marginal\left(q\right)\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiment/FiniteProductAbsoluteContinuity.finite_product_absolutelyContinuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite index type and unit-interval points p and q, only the two strict bounds on the real value of q are assumed. The product of copies of marginal p is absolutely continuous with respect to the product of copies of marginal q; no bound on p is required.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Experiment/FiniteProductAbsoluteContinuity.absolutelyContinuous_pi_marginal`
- Truth anchor: `D5/S3/ConceptDynamics/Experiment/FiniteProductAbsoluteContinuity.finite_product_absolutelyContinuous`
- Truth anchor: `D5/S3/ConceptDynamics/Experiment/FiniteProductAbsoluteContinuity.marginal_false_pos`
- Truth anchor: `D5/S3/ConceptDynamics/Experiment/FiniteProductAbsoluteContinuity.marginal_singleton_pos`
- Truth anchor: `D5/S3/ConceptDynamics/Experiment/FiniteProductAbsoluteContinuity.marginal_true_pos`
- Dependency: [D5/S3/ConceptDynamics/Experiment/InfiniteIdentificationFiniteInexactness](InfiniteIdentificationFiniteInexactness.md)
