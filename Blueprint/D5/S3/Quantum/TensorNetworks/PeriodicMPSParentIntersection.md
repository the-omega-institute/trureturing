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

This declaration establishes the inhabited-locus and actual-competitor phase-equivalence clauses of Section 2, Theorem 2.1 of PERIODIC_BINARY_MPS_LOCAL_PHASE_RECOVERY.md. The following genericity argument is an application of existing results, separate from the declaration's Lean statement.

Fix any integer N at least four and put r=N-4. Write W(k) for the binary words of length k and H(N) for the complex functions on W(N). The native map f from the eight complex entries of a shared matrix pair A to H(N) is f(A)(w)=trace(A(w(0)) times ... times A(w(N-1))). This is UniformMPSExpectedDimensionRefutation.traceWord 2 2 N, and P(N) is exactly its range, UniformMPSExpectedDimensionRefutation.uMPS 2 2 N. No closure, quotient of representations, normalization or restriction on A is taken. The source's amplitude flattening F(ψ) has four rows u in W(2), columns b in W(N-2), and entry ψ(ub). At ψ=f(A), it is PeriodicMPSParentIntersection.twoFlattening A r, up to the displayed word-length identifications. Thus U(N)={ψ in P(N): rank F(ψ)=4} is intrinsic to the actual state.

For every constant complex matrix G with rows W(N-2) and four columns, let q(G) be the coordinate polynomial ψ ↦ det(F(ψ)G). The exact rank-four condition is that q(G)(ψ) is nonzero for at least one G. Indeed, Matrix.mulVec_surjective_iff_rank_eq_card gives a right inverse when F has rank four: choose a preimage of each standard basis vector to obtain G with FG=I. Conversely, det(FG) nonzero gives rank(FG)=4 by Matrix.rank_of_det_ne_zero; Matrix.rank_mul_le_left and Matrix.rank_le_card_height then force rank F=4. These are declarations of the pinned Mathlib, revision 56a005855ea17e0b0958f73ec801ae140b0a1679. Taking the union over all G gives the entire intrinsic locus; a single chosen G gives only a principal-open subset of it.

Use the full complex affine Zariski topology on H(N): its principal opens are the nonvanishing sets of every complex multivariate polynomial in all amplitude coordinates, and arbitrary unions of these sets are open. Equip the literal image P(N) with the induced topology. Each q(G) is such a polynomial, since flattening only selects coordinates and multiplication by constant G and the determinant are polynomial operations. The union over all G therefore proves that the exact U(N) is relatively Zariski open. This topology is neither a topology generated by one determinant nor a topology on raw marginal observables; P(N) need not be Zariski closed.

The first conjunct of PeriodicMPSParentIntersection.rank_locus_inhabited_and_phase_recovery r supplies an actual rank-four state for every r, including zero. Explicitly A*(0)=diag(1,2) and A*(1) is the coordinate-exchange matrix. Choose a right inverse G* at f(A*), so q(G*)(f(A*))=1. In particular U(N) is nonempty. The same fixed G* will suffice for density, without replacing the definition of U(N) by that one determinant test.

Index the eight parameter coordinates by triples (i,a,b) of bits. For w in W(N), let a(w) be the polynomial trace of the ordered product of the two formal matrices whose entries are those coordinates. Evaluation at any parameter assignment x gives a(w)(x)=f(x)(w). Substitute all a(w) into q(G*) to obtain a polynomial p on the eight entries. MvPolynomial.eval_assoc identifies p(x) with q(G*)(f(x)); this is coordinate substitution along the original map. Since p(A*)=1, p is nonzero.

Apply MvPolynomial.dense_setOf_eval_ne_zero from TauCetiProject/TauCeti, revision 00deee4410cf1ae1f96695b1ab13f148cea83bc7, file TauCeti/Topology/Algebra/MvPolynomial/Nonvanishing.lean. Its coefficient domain may be any commutative integral domain with a perfect T1 topology; ordinary complex numbers satisfy these hypotheses. It says that D={x: p(x)≠0} is dense in the ordinary product topology. Its algebraic input is MvPolynomial.funext_set: a polynomial vanishing on a product of infinite subsets is zero. Every nonempty complex open box has infinite sides, so it cannot be contained in the zero set of nonzero p.

This is a reference to the established external theorem, not an imported dependency of this module. That revision of TauCeti uses Lean 4.36.0-rc2 and Mathlib 1b1ccf4b088b32fa3f23f2de1127433254a81e1e; this project's pin is Lean 4.35.0 and the Mathlib revision specified above. The reference does not assert toolchain compatibility, a retained transplant, or a Lean declaration of genericity in this module. The existing TauCeti Apache 2.0 license is at docs/reports/licenses/TauCeti-LICENSE.txt.

The native map into the ordinary image subtype is continuous: each of its finitely many coordinates is a polynomial evaluation, using pinned Mathlib's MvPolynomial.continuous_eval. Every ψ in P(N) has a parameter preimage x. Since x lies in the closure of D, mem_closure_image places ψ=f(x) in the closure, inside P(N), of f(D). For every y in D the substitution identity gives q(G*)(f(y))≠0, hence f(D) is contained in U(N). Closure monotonicity proves ordinary density of the exact U(N). This transport uses neither injectivity nor openness of f, and does not replace the actual image by its closure.

Every complex coordinate polynomial is continuous in the ordinary topology. Consequently the identity from P(N) with its ordinary induced topology to P(N) with the full induced complex Zariski topology is continuous and surjective. DenseRange.dense_image transports the ordinary density of U(N) to its relative Zariski density. Together with the all-G openness argument and the actual witness, this supplies the source's nonempty, relatively complex-Zariski-open dense genericity clause and its proof's ordinary-density subclause for every N at least four. It is a mathematical consequence of the cited results, with no additional physical realization, resource bound or literature-novelty claim.

The existing Lean declaration and its recovery equivalence remain the formalized result above; the genericity argument is the application explained here. The literal phase-orbit set equality, cone membership, observable determinant and partial-trace criterion, the remaining proof clauses, and Corollary 3.1 are not established here. In particular this application does not close all of Theorem 2.1, and gives no conclusion about two-site recovery.

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
