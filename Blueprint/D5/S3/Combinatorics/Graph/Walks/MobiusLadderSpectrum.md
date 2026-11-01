# Native Mobius ladders and their complete spectra

## Abstract

Rung coordinates give a graph isomorphism to the actual antipodal circulant at every size.

Write M(m) for the circulant on ZMod(2(m+2)) with jumps 1 and m+2. Both orientations of each jump are used and loops are excluded. The explicit coordinate (i,b) maps to i+(m+2)b. This is a bijection of the actual vertex types; it sends the rung flip to the antipodal jump and twisted forward transport to addition by one.

**Definition 1.1 (The native graph correspondence).**

$$\forall m \in \mathrm{Nat},\; \operatorname{GraphIso}\left(\operatorname{graph}\left(\operatorname{closing}\left(m, 1\right)\right), \operatorname{mobius}\left(m\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/MobiusLadderSpectrum.mobiusIso` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The map preserves each of the three kinds of adjacency in both directions. At the closing rung it changes the binary label, exactly accounting for wraparound in the cyclic vertex set. Injectivity and looplessness handle the four-vertex boundary.

**Theorem 1.2 (Necessity and attainability).**

$$\forall m \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \operatorname{mem}\left(k, \operatorname{spectrum}\left(\operatorname{mobius}\left(m\right)\right)\right) \Leftrightarrow \left(\operatorname{add}\left(m, 2\right) \le \operatorname{mul}\left(2, k\right) \land \left(k \le \operatorname{add}\left(m, 2\right) \land \operatorname{Odd}\left(k\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/MobiusLadderSpectrum.mobius_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The graph isomorphism transports actual maximal independent Finsets and preserves their cardinalities. The complete binary closing spectrum then gives every odd cardinality in the stated interval and rules out every other cardinality.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/MobiusLadderSpectrum.mobiusIso`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/MobiusLadderSpectrum.mobius_spectrum`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/BinaryRungSpectrum](BinaryRungSpectrum.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/FiniteDistancePower](FiniteDistancePower.md)
