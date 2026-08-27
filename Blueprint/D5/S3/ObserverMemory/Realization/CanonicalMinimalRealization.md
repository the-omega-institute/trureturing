# Canonical Minimal Realization

## Abstract

Exact realizations map canonically onto the realized complete itineraries.

**Theorem 1.1 (The realization image is update invariant).**

$$\forall X, S: \operatorname{Type},\\{}F: X \to X, R: X \to S, nu: S \to S,\\{}(\forall x, R\left(F\left(x\right)\right) = nu\left(R\left(x\right)\right)) \Rightarrow\\{}\forall s \in \operatorname{range}\left(R\right), nu\left(\operatorname{val}\left(s\right)\right) \in \operatorname{range}\left(R\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Realization/CanonicalMinimalRealization.realization_range_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let R intertwine a source update F with a realized update nu. Every point of range(R) has the form R(x), and applying nu produces R(F(x)), which lies in the same range.

This closure result defines the reachable update used by the main minimal-realization theorem. No global surjectivity of R onto its ambient carrier is assumed.

**Theorem 1.2 (Exact realizations factor onto causal itineraries).**

$$\forall X, S, B: \operatorname{Type},\\{}F: X \to X, q: X \to B, R: X \to S,\\{}nu: S \to S, o: S \to B,\\{}hcommute: \forall x: X, R\left(F\left(x\right)\right) = nu\left(R\left(x\right)\right),\\{}hreadout: \forall x: X, q\left(x\right) = o\left(R\left(x\right)\right),\\{}b_{q} = \operatorname{completeItinerary}\left(F, q\right), Z_{q} = \operatorname{range}\left(b_{q}\right),\\{}\exists! pi: \operatorname{range}\left(R\right) \to Z_{q}, \operatorname{Surjective}\left(pi\right) \land\\{}b_{q} = pi \circ \operatorname{rangeFactorization}\left(R\right) \land\\{}pi \circ \operatorname{reachableUpdate}\left(F, R, nu, hcommute\right) = shift \circ pi.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Realization/CanonicalMinimalRealization.canonical_minimal_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a source update F and readout q, bq is the complete infinite itinerary and Zq is its realized range. An exact realization R commutes with update and factors the current readout through a realized readout o.

There is a unique surjection pi from range(R) onto Zq. It sends R(x) to bq(x), so the displayed factorization is independent of the chosen source representative.

The reachable update is induced by nu using the preceding range invariance theorem. The existing itinerary update is literal left shift, and pi intertwines these two updates.

The proof reuses the repository's complete-itinerary universality and causal-state image factorization theorems. Pinned Mathlib supplies surjective range factorization and cancellation for the uniqueness step.

**Theorem 1.3 (Exact readout factorization has a finite witness).**

$$X = B = \operatorname{Bool}, S = \operatorname{Unit},\\{}F = id, nu = id, R(x) = star, q = id, o\left(star\right) = 0\\\Rightarrow (\forall x, R\left(F\left(x\right)\right) = nu\left(R\left(x\right)\right)) \land \neg \forall x, q\left(x\right) = o\left(R\left(x\right)\right) \land\\{}\neg \exists pi: \operatorname{range}\left(R\right) \to Z_{q}, \forall x, pi\left(\operatorname{rangeFactorization}\left(R, x\right)\right) = \operatorname{rangeFactorization}\left(b_{q}, x\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Realization/CanonicalMinimalRealization.readout_exactness_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take Boolean source and output carriers, a one-point realization carrier, identity dynamics, and Boolean identity readout. The realization collapses false and true while their constant future itineraries remain distinct.

Thus update commutation still holds, but the proposed realized readout is not exact and no map on range(R) can agree with both source itineraries. This finite witness prevents deletion of the readout-factorization hypothesis.

**Theorem 1.4 (Update commutation has a finite witness).**

$$X = B = \operatorname{Unit}, S = \operatorname{Bool},\\{}F = id, R(x) = 0, nu = \operatorname{not},\\{}(\forall x, q\left(x\right) = o\left(R\left(x\right)\right)) \land \neg \forall x, R\left(F\left(x\right)\right) = nu\left(R\left(x\right)\right) \land\\{}\neg \forall s \in \operatorname{range}\left(R\right), nu\left(\operatorname{val}\left(s\right)\right) \in \operatorname{range}\left(R\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Realization/CanonicalMinimalRealization.update_commutation_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a one-point source with exact one-point readout, embed it as false in a Boolean realization carrier, and let the proposed realized update be Boolean negation.

The readout condition holds, but negation sends the only reachable realization state outside range(R). Hence the realized update does not induce an update on the reachable part, witnessing the need for update commutation.

## References

- Truth anchor: `D5/S3/ObserverMemory/Realization/CanonicalMinimalRealization.canonical_minimal_realization`
- Truth anchor: `D5/S3/ObserverMemory/Realization/CanonicalMinimalRealization.readout_exactness_is_necessary`
- Truth anchor: `D5/S3/ObserverMemory/Realization/CanonicalMinimalRealization.realization_range_invariant`
- Truth anchor: `D5/S3/ObserverMemory/Realization/CanonicalMinimalRealization.update_commutation_is_necessary`
- Dependency: [D5/S3/ObserverMemory/PredictionFactors/CausalStateFactorization](../PredictionFactors/CausalStateFactorization.md)
- Dependency: [D5/S3/ObserverMemory/PredictionFactors/PredictionCompletionUniversality](../PredictionFactors/PredictionCompletionUniversality.md)
