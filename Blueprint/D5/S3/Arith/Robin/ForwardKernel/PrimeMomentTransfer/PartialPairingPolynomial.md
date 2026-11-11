# Partial pairing polynomial

## Abstract

Finite perfect pairing polynomials and their expansion over partial pairings.

Let alpha be a finite label type with decidable equality and let U be a finite set of labels. Edges are finite label sets, so no orientation, ordering, or repeated edge is introduced. This is the arbitrary-order combinatorial form of the pairing expansion underlying the four-label perfectPairingSum.

**Definition 1.1 (Labels covered by edges).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartialPairingPolynomial.pairingSupport`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartialPairingPolynomial.pairingSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite set P of finite label sets, pairingSupport(P) is the union of its members.

**Definition 1.2 (Partial pairing).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartialPairingPolynomial.IsPartialPairing`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartialPairingPolynomial.IsPartialPairing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

IsPartialPairing(U,P) means that every edge of P has exactly two labels, distinct edges in P are disjoint, and the union of the edges is a subset of U.

**Definition 1.3 (Perfect pairing).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartialPairingPolynomial.IsPerfectPairing`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartialPairingPolynomial.IsPerfectPairing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

IsPerfectPairing(U,P) means that P is a partial pairing of U and the union of its edges equals U. In particular, the empty pairing is a perfect pairing of the empty label set.

**Definition 1.4 (Perfect pairing polynomial).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartialPairingPolynomial.finitePairingPolynomial`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartialPairingPolynomial.finitePairingPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an edge weight c valued in the reals, finitePairingPolynomial(U,c) is the sum over all perfect pairings P of U of the product over edges e in P of c(e). The empty product equals one.

**Theorem 1.5 (Expansion over a partial pairing).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartialPairingPolynomial.finitePairingPolynomial_add`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartialPairingPolynomial.finitePairingPolynomial_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite label type alpha, finite label set U, and real edge weights c,d, finitePairingPolynomial(U,e mapped to c(e)+d(e)) equals the sum over partial pairings P of U of the product of c(e) over e in P, multiplied by finitePairingPolynomial(U minus pairingSupport(P),d). Expand the product on each perfect pairing M by its edge subsets P. The map (M,P) to (P,M minus P) is a bijection onto a partial pairing and a perfect pairing of its uncovered labels. The inverse takes (P,Q) to (P union Q,P); the disjoint label supports imply disjoint edge sets. Thus each contribution occurs exactly once, with no factorial factor.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartialPairingPolynomial.IsPartialPairing`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartialPairingPolynomial.IsPerfectPairing`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartialPairingPolynomial.finitePairingPolynomial`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartialPairingPolynomial.finitePairingPolynomial_add`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartialPairingPolynomial.pairingSupport`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs](QuadraticMomentDefs.md)
