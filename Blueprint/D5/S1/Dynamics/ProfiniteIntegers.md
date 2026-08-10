# Natural Numbers in the Profinite Integers

## Abstract

Natural numbers embed injectively and densely in the compatible-residue model of the profinite integers.

**Definition 1.1 (Profinite integers are compatible residue readings).**

Lean statement: `D5/S1/Dynamics/ProfiniteIntegers.ProfiniteIntegers`

*Formalization.* `D5/S1/Dynamics/ProfiniteIntegers.ProfiniteIntegers` (`✓ std3`).

*Citation.* Luis Ribes; Pavel Zalesskii (2010). *Profinite Groups*. DOI: [10.1007/978-3-642-01642-4](https://doi.org/10.1007/978-3-642-01642-4).

*Commentary.*

A point assigns a residue modulo every positive integer. Whenever one modulus divides another, reduction of the finer reading equals the coarser reading. Positive moduli are indexed canonically by m + 1, so the formal product contains no zero-modulus coordinate.

**Theorem 1.2 (Natural numbers embed injectively and densely).**

$$\operatorname{Injective}\left(\mathit{natEmbedding}\right) \land \operatorname{DenseRange}\left(\mathit{natEmbedding}\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/ProfiniteIntegers.nat_embedding_injective_and_dense` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Distinct natural numbers are separated by the coordinate whose modulus is one larger than their maximum. For density, a basic product neighborhood constrains only finitely many moduli. Their product is a common multiple, and the compatible reading at that modulus has a natural representative that realizes every constrained coordinate simultaneously.

Pinned Mathlib was searched before proving. It provides density of the canonical image of an arbitrary group in its abstract profinite completion, but no theorem that the natural numbers are dense in the profinite completion of the integers. The repository therefore proves the finite-window representative directly rather than restating the upstream integer-image theorem.

## References

- Truth anchor: `D5/S1/Dynamics/ProfiniteIntegers.ProfiniteIntegers`
- Truth anchor: `D5/S1/Dynamics/ProfiniteIntegers.nat_embedding_injective_and_dense`
