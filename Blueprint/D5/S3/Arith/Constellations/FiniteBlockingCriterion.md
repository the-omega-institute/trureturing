# Finite Blocking Criterion

## Abstract

A finite integer constellation cannot cover a prime residue space larger than the constellation itself.

**Theorem 1.1 (Finite blocking criterion).**

$$\forall H: \operatorname{Finset}(\mathbb{Z}), k \in \mathbb{N},\ \operatorname{card}\left(H\right) = k \Rightarrow \forall p \in \mathbb{P},\ k < p \Rightarrow (\nu_{p}(H) \leq k \land k < p).$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Constellations/FiniteBlockingCriterion.finite_blocking_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite set H of integer offsets and a natural number k equal to its cardinality, let p range over primes larger than k. The forbidden residue set is the image of H under reduction of -h modulo p, and nu_p(H) is its cardinality.

The conclusion has exactly two leaves: nu_p(H) is at most k, and k is strictly less than p. The first is the cardinality bound for a finite image; the second retains the stated size premise.

## References

- Truth anchor: `D5/S3/Arith/Constellations/FiniteBlockingCriterion.finite_blocking_criterion`
