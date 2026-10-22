# Critical Algebraic BRST Nilpotence

## Abstract

Creation cyclicity propagates the original critical algebraic BRST square to every tensor state.

**Theorem 1.1 (The original charge squares to zero at rank 26).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostBrstNilpotence.nilpotent`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostBrstNilpotence.nilpotent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let D be an original finite-rank even integral symmetric lattice of rank 26. Let H be a complex matrix on Fin(D.rank), and assume both H times gramComplex(D) equals the identity and gramComplex(D) times H equals the identity. On the entire original algebraic tensor module State(D)=Carrier(D) tensor over Complex with Fock(Complex), the original endomorphism Q(D,H) satisfies Q(D,H) times Q(D,H)=0. The zero here is the zero endomorphism, so the conclusion includes every algebraic tensor superposition, not only a vacuum sector.

The charge is the original statewise finite charge sum, with the original matter modes, ghost modes and normal-order branches. No replacement charge, fixed finite mode domain, additional intercept, nilpotence premise or operator-commutant premise is introduced. Products of endomorphisms act rightmost first.

Write B(m) and C(p) for the original lifted ghost modes, and M(m)+G(m) for total matter-plus-ghost stress. Associativity gives [Q squared,B(m)]=[Q,Q B(m)+B(m) Q]. The actual all-state Ward identity identifies the anticommutator with M(m)+G(m). The supplied total covariance law identifies this last commutator with minus ((rank(D)-26)/12) times (m cubed minus m) times C(m). Both Gram inverse hypotheses are passed to that law. At rank 26 its scalar is zero, so Q squared commutes with every B(m). The exact supplied square-C commutator law gives commutation with every C(p), without inverse-Gram, rank or Virasoro hypotheses of its own.

Fix any original matter vector u. The canonical bilinear tensor map and composition with Q squared define a complex-linear map from ghost Fock space to State(D), sending g to Q squared applied to u tensor g. Its kernel W is a submodule of ghost Fock space. The original vacuum-square theorem, with both Gram inverses, puts the actual ghost vacuum in W for every u.

Evaluate the actual endomorphism commutators at u tensor g. Since B(m) and C(p) act as the identity on matter tensored with b(m) and c(p), respectively, these equalities make W stable under every b creator with m<=-2 and every c creator with p<=1. The original creation_cyclic theorem therefore gives W equal to the whole ghost Fock module. This uses a ghost-to-tensor linear map, not a scalar commutant theorem about a ghost endomorphism.

Thus Q squared kills u tensor g for all original matter u and ghost g. Tensor-product extensionality upgrades these pure-tensor equalities to the zero endomorphism on all State(D). The propagated kernel is the integration step; Ward, total covariance, square-C commutation, vacuum-square vanishing and creation cyclicity are reused from their original supplying declarations.

This is algebraic critical BRST nilpotence in the specified model at rank 26 under both Gram inverse identities. It does not assert a physical realization, literature novelty, completed string theory, a BRST cohomology computation, or an AdS/CFT result.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostBrstNilpotence.nilpotent`
- Dependency: [D5/S3/VertexAlgebra/LatticeBcGhostBrstSquareCCommutator](LatticeBcGhostBrstSquareCCommutator.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeBcGhostBrstTotalCovariance](LatticeBcGhostBrstTotalCovariance.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeBcGhostBrstVacuumSquare](LatticeBcGhostBrstVacuumSquare.md)
