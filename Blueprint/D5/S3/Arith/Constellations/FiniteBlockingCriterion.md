# Finite Blocking Criterion

## Abstract

A finite integer constellation cannot be completely blocked by primes larger than the constellation itself.

**Theorem 1.1 (Finite blocking criterion).**

$$\forall H: \operatorname{Finset}(\mathbb{Z}), k \in \mathbb{N},\ \operatorname{card}\left(H\right) = k \Rightarrow ((\forall p \in \mathbb{P},\ k < p \Rightarrow (\nu_{p}(H) \leq k \land k < p)) \land (\operatorname{IsAdmissible}\left(H\right) \iff \forall q \in \mathbb{P},\ q \leq k \Rightarrow \nu_{q}(H) < q)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Constellations/FiniteBlockingCriterion.finite_blocking_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite set H of integer offsets and a natural number k equal to its cardinality, let p range over primes larger than k. The forbidden residue set is the image of H under reduction of -h modulo p, and nu_p(H) is its cardinality.

The conclusion has exactly three leaves: nu_p(H) is at most k, k is strictly less than p, and admissibility is equivalent to checking nu_q(H) < q only for primes q at most k. The equivalence states in both directions that primes above k cannot give complete residue coverage.

ASSUMED-UNVERIFIED: source lines 626-635 use the indexed offset h_1 and normalize h_1 to zero, but neither those lines nor Theorem 10.1 explicitly state k > 0 or that H is nonempty. The Lean statement therefore remains a valid generalized claim whose empty case is trivial.

## References

- Truth anchor: `D5/S3/Arith/Constellations/FiniteBlockingCriterion.finite_blocking_criterion`
