# Periodic MPS parent-space gluing

## Abstract

The rank-four target locus is inhabited at every length at least four, and raw three-site marginals recover every actual periodic competitor up to phase on that locus.

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

**Definition 1.6 (Three-site amplitude columns).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection.threeColumns`

*Formalization.* `D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection.threeColumns` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a ring of length r+4, rows are words w of length three and columns are complement words b of length r+1. The entry is trace(wordMatrix A b times wordMatrix A w). Trace cyclicity identifies this entry with the actual native traceWord amplitude at the concatenation of w and b.

**Definition 1.7 (Raw three-site marginal).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection.rawThree`

*Formalization.* `D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection.rawThree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

rawThree A r is threeColumns A r times its conjugate transpose. Its entry at u,v is the sum over complement words b of the actual amplitude at ub times the complex conjugate of the amplitude at vb. This is the unnormalized marginal of Definition 1.2; no division by the state norm occurs.

**Theorem 1.8 (Gluing adjacent three-site constraints).**

$$\forall (A: \operatorname{Fin}\left(2\right) \to \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Bond}), (\forall (B: \operatorname{Fin}\left(2\right) \to \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Bond}), (\forall (r: \mathbb{N}), ((\operatorname{Matrix.rank}\left(\operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.twoFlattening}\left(A, r\right)\right) = 4) \to (\forall (b: \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Word}\left(r\right)), ((\exists (X: \operatorname{Fin}\left(2\right) \to \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Bond}), (\forall (w: \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Word}\left(3\right)), (\forall (j: \operatorname{Fin}\left(2\right)), (\operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.competitorSlice}\left(B, b, \operatorname{Fin.snoc}\left(w, j\right)\right) = \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.gamma}\left(A, 3, X\left(j\right), w\right))))) \to ((\exists (Y: \operatorname{Fin}\left(2\right) \to \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Bond}), (\forall (i: \operatorname{Fin}\left(2\right)), (\forall (w: \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Word}\left(3\right)), (\operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.competitorSlice}\left(B, b, \operatorname{Fin.cons}\left(i, w\right)\right) = \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.gamma}\left(A, 3, Y\left(i\right), w\right))))) \to (\exists (Z: \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Bond}), (\operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.competitorSlice}\left(B, b\right) = \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.gamma}\left(A, 4, Z\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection.actual_competitor_gluing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The matrices A and B are arbitrary complex shared two by two matrices. Only the target flattening for A has rank four. No injectivity, rank or nondegeneracy condition is imposed on B; repeated and zero competitor matrices remain in the domain.

Assume the two adjacent three-site conditional vectors of the fixed four-site slice lie in the target three-site parent space. The left condition supplies one boundary X(j) for each last bit; the right condition supplies one boundary Y(i) for each first bit. The conclusion supplies a single matrix Z representing the entire four-site slice.

Rank four forces the two-letter target products to span the matrix algebra. Trace separation on the two middle sites then gives X(j)A(i)=A(j)Y(i). Expanding the identity in the two-letter products constructs a common boundary with X(j)=A(j)Z and Y(i)=ZA(i). Cyclicity of the trace gives the asserted four-site representation.

This is the adjacent-parent overlap bridge in Section 2 of Periodic binary matrix product states: three-site phase recovery. It includes the four-site ring without identifying the range of its three-site marginal with the full three-site parent space. Equality of raw marginals, all-window propagation, finite-ring scalar uniqueness, the unit-modulus conclusion and genericity require their separate arguments; none is asserted by this theorem.

**Theorem 1.9 (Inhabited rank locus and finite-ring phase recovery).**

$$\forall (r: \mathbb{N}), ((\exists (A: \operatorname{Fin}\left(2\right) \to \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Bond}), (\operatorname{Matrix.rank}\left(\operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.twoFlattening}\left(A, r\right)\right) = 4)) \land (\forall (A: \operatorname{Fin}\left(2\right) \to \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Bond}), (\forall (B: \operatorname{Fin}\left(2\right) \to \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Bond}), ((\operatorname{Matrix.rank}\left(\operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.twoFlattening}\left(A, r\right)\right) = 4) \to ((\operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.rawThree}\left(B, r\right) = \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.rawThree}\left(A, r\right)) \Leftrightarrow (\exists (c: \mathbb{C}), ((\operatorname{norm}\left(c\right) = 1) \land (\operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.gamma}\left(B, r + 4, 1\right) = \operatorname{HSMul.hSMul}\left(c, \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.gamma}\left(A, r + 4, 1\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection.rank_locus_inhabited_and_phase_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural r the ring length is r+4. The first conjunct exhibits a shared matrix pair whose actual two-site flattening has rank four. The second quantifies over every target pair A and every competitor pair B, imposing rank four only on A. It states both directions of equality of raw three-site marginals versus equality of the actual periodic amplitude functions up to a complex scalar of norm one. gamma A n 1 is definitionally the existing traceWord amplitude function.

The witness uses the diagonal matrix with entries 1 and 2 and the matrix exchanging the two coordinates. Their four length-two products span the full matrix algebra. Trace separation at every longer length gives rank four for every r, including zero.

Equality of raw marginals identifies the ranges of the two amplitude-column matrices, because a complex matrix and its product with its conjugate transpose have the same range. Every competitor three-site slice therefore lies in the target parent space. The adjacent-parent intersection propagates these constraints by induction to one virtual boundary for the whole ring. Both induction branches compare coefficients of the same actual competitor using trace cyclicity.

The competitor's cyclic invariance forces the resulting boundary to commute with both target symbol matrices. Length-two spanning then makes it commute with every two by two matrix, hence it is scalar. The nonzero raw target marginal and its scalar multiplication law force the scalar to have norm one. At r=0 the propagation reaches the four-site ring with an empty complement; no equality between the marginal range and the entire three-site parent space is required.

This establishes the inhabited-locus and actual-competitor phase-equivalence clauses of Section 2, Theorem 2.1. Relative Zariski openness and density, ordinary density, the observable determinant and partial-trace criterion, and Corollary 3.1 are separate obligations. They are not conclusions of this declaration.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection.TwoSiteSpanning`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection.actual_competitor_gluing`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection.competitorSlice`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection.gamma`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection.rank_locus_inhabited_and_phase_recovery`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection.rawThree`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection.threeColumns`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection.twoFlattening`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection.wordMatrix`
- Dependency: [D5/S3/Quantum/TensorNetworks/UniformMPSExpectedDimensionRefutation](UniformMPSExpectedDimensionRefutation.md)
