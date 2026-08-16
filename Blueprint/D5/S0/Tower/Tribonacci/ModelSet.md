# Tribonacci Bounded Internal Window

## Abstract

Tribonacci names have bounded internal coordinates at every secondary root.

The scope is the bounded-window core of a cut-and-project argument. The formalization does not construct an ambient lattice or a complete cut-and-project scheme, and it does not claim that the physical set is Delone, Meyer, uniformly discrete, or relatively dense.

**Definition 1.1 (Conjugate coordinate).**

$$\operatorname{conjugateCoordinate}\left(z, \mathit{name}\right) = \operatorname{digitPolynomialEvaluation}\left(\mathit{name}, z\right)$$

*Formalization.* `D5/S0/Tower/Tribonacci/ModelSet.conjugateCoordinate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite admissible name is evaluated as a zero-one digit polynomial at the chosen complex root.

**Theorem 1.2 (Fixed-layer decoded-internal coordinates are injective).**

$$\forall Q \in N,\; \forall z \in C,\; \operatorname{Injective}\left(\operatorname{conjugateEmbeddingAtLength}\left(Q, z\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Tribonacci/ModelSet.conjugate_embedding_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first component is the frozen integer decoder. Its fixed-layer injectivity therefore makes the paired decoded-internal map injective.

**Theorem 1.3 (Contracting coordinates have a geometric-series bound).**

$$\forall Q \in N,\; \forall name \in \operatorname{TribonacciName}\left(Q\right),\; \forall z \in C,\; \operatorname{Implies}\left(\operatorname{LessThan}\left(\operatorname{abs}\left(z\right), 1\right), \operatorname{LessEqual}\left(\operatorname{abs}\left(\operatorname{conjugateCoordinate}\left(z, \mathit{name}\right)\right), \operatorname{inverseOneMinusAbs}\left(z\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Tribonacci/ModelSet.conjugate_coordinate_norm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The triangle inequality bounds every zero-one digit sum by a finite geometric sum, which is bounded by the full convergent series.

**Theorem 1.4 (The Tribonacci internal window is bounded).**

$$\forall z \in C,\; \operatorname{Implies}\left(\operatorname{SecondaryTribonacciRoot}\left(z\right), \operatorname{Bounded}\left(\operatorname{tribonacciInternalWindow}\left(z\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Tribonacci/ModelSet.tribonacci_internal_window_is_bounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen Pisot-root theorem supplies absolute value below one for every non-Perron root. The geometric estimate is uniform in the name length, so all finite internal coordinates lie in one bounded window.

## References

- Truth anchor: `D5/S0/Tower/Tribonacci/ModelSet.conjugateCoordinate`
- Truth anchor: `D5/S0/Tower/Tribonacci/ModelSet.conjugate_coordinate_norm_le`
- Truth anchor: `D5/S0/Tower/Tribonacci/ModelSet.conjugate_embedding_injective`
- Truth anchor: `D5/S0/Tower/Tribonacci/ModelSet.tribonacci_internal_window_is_bounded`
- Dependency: [D5/S0/Tower/Tribonacci/Binet](Binet.md)
- Dependency: [D5/S0/Tower/Tribonacci/Representation](Representation.md)
