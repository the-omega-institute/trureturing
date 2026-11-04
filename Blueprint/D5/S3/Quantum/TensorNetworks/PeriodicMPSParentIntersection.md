# Periodic MPS parent-space gluing

## Abstract

Adjacent three-site parent constraints glue on every actual periodic competitor at a rank-four target.

**Definition 1.1 (Ordered matrix words).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection.wordMatrix`

*Formalization.* `D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection.wordMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A word of length n is a function from Fin n to Fin 2. wordMatrix multiplies the shared complex two by two matrices in increasing site order; the empty product is the identity.

**Definition 1.2 (Virtual boundary amplitudes).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection.gamma`

*Formalization.* `D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection.gamma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a complex two by two matrix X, gamma A n X at the word w is the trace of X times wordMatrix A w. Its image is the length-n parent space.

**Definition 1.3 (Length-two injectivity).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection.TwoSiteSpanning`

*Formalization.* `D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection.TwoSiteSpanning` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

TwoSiteSpanning means that the complex linear span of all four ordered products A(i)A(j) is the full two by two matrix space. Neither individual symbol matrix is required to be invertible.

**Definition 1.4 (The actual target flattening).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection.twoFlattening`

*Formalization.* `D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection.twoFlattening` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For r natural, the target has length r+4. A row is the ordered pair of its first two bits, and a column is a word of length r+2. The entry is the existing native traceWord amplitude at the concatenation of these words. Thus rank four is the intrinsic amplitude-flattening condition of Definition 1.3.

**Definition 1.5 (Actual conditional four-site amplitudes).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection.competitorSlice`

*Formalization.* `D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection.competitorSlice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary complex shared matrices B and a fixed complement word b of length r, competitorSlice is the native periodic traceWord amplitude at the concatenation of a four-bit word with b. The ring has length 4+r. At r=0 the complement word is empty.

**Theorem 1.6 (Gluing adjacent three-site constraints).**

$$\forall (A: \operatorname{Fin}\left(2\right) \to \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Bond}), (\forall (B: \operatorname{Fin}\left(2\right) \to \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Bond}), (\forall (r: \mathbb{N}), ((\operatorname{Matrix.rank}\left(\operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.twoFlattening}\left(A, r\right)\right) = 4) \to (\forall (b: \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Word}\left(r\right)), ((\exists (X: \operatorname{Fin}\left(2\right) \to \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Bond}), (\forall (w: \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Word}\left(3\right)), (\forall (j: \operatorname{Fin}\left(2\right)), (\operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.competitorSlice}\left(B, b, \operatorname{Fin.snoc}\left(w, j\right)\right) = \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.gamma}\left(A, 3, X\left(j\right), w\right))))) \to ((\exists (Y: \operatorname{Fin}\left(2\right) \to \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Bond}), (\forall (i: \operatorname{Fin}\left(2\right)), (\forall (w: \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Word}\left(3\right)), (\operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.competitorSlice}\left(B, b, \operatorname{Fin.cons}\left(i, w\right)\right) = \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.gamma}\left(A, 3, Y\left(i\right), w\right))))) \to (\exists (Z: \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Bond}), (\operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.competitorSlice}\left(B, b\right) = \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.gamma}\left(A, 4, Z\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection.actual_competitor_gluing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The matrices A and B are arbitrary complex shared two by two matrices. Only the target flattening for A has rank four. No injectivity, rank or nondegeneracy condition is imposed on B; repeated and zero competitor matrices remain in the domain.

Assume the two adjacent three-site conditional vectors of the fixed four-site slice lie in the target three-site parent space. The left condition supplies one boundary X(j) for each last bit; the right condition supplies one boundary Y(i) for each first bit. The conclusion supplies a single matrix Z representing the entire four-site slice.

Rank four forces the two-letter target products to span the matrix algebra. Trace separation on the two middle sites then gives X(j)A(i)=A(j)Y(i). Expanding the identity in the two-letter products constructs a common boundary with X(j)=A(j)Z and Y(i)=ZA(i). Cyclicity of the trace gives the asserted four-site representation.

This is the adjacent-parent overlap bridge in Section 2 of Periodic binary matrix product states: three-site phase recovery. It includes the four-site ring without identifying the range of its three-site marginal with the full three-site parent space. Equality of raw marginals, all-window propagation, finite-ring scalar uniqueness, the unit-modulus conclusion and genericity require their separate arguments; none is asserted by this theorem.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection.TwoSiteSpanning`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection.actual_competitor_gluing`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection.competitorSlice`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection.gamma`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection.twoFlattening`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection.wordMatrix`
- Dependency: [D5/S3/Quantum/TensorNetworks/UniformMPSExpectedDimensionRefutation](UniformMPSExpectedDimensionRefutation.md)
