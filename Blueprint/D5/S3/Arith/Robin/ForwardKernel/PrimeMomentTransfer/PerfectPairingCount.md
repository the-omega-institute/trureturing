# Perfect pairing count

## Abstract

Cardinalities and evaluations of perfect and partial pairings on finite label sets.

Let alpha be a finite type with decidable equality. A perfect pairing of a finite label set U is a finite set P of pairwise disjoint two-element label sets whose union is U. Write p(U) for the number of these perfect pairings. The empty set has one perfect pairing.

**Theorem 1.1 (Number of edges in a perfect pairing).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PerfectPairingCount.card`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PerfectPairingCount.card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Lean declaration IsPerfectPairing.card states that if P is a perfect pairing of U, then the cardinality of U equals twice the cardinality of P.

**Theorem 1.2 (Rank-one edge evaluation).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PerfectPairingCount.finitePairingPolynomial_rankOne`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PerfectPairingCount.finitePairingPolynomial_rankOne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let x be a real weight on labels and let c be a real weight on finite label sets. Assume c(e) is the product of x(i) over labels i in e whenever e has cardinality two. Then finitePairingPolynomial(U,c) equals p(U) times the product of x(i) over all labels i in U. Each perfect pairing partitions U, so each label occurs exactly once in its product.

**Theorem 1.3 (Constant edge evaluation).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PerfectPairingCount.finitePairingPolynomial_const`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PerfectPairingCount.finitePairingPolynomial_const` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let kappa be real and assume c(e) equals kappa whenever e has cardinality two. Then finitePairingPolynomial(U,c) equals p(U) times kappa to the power floor(cardinality(U)/2). Every perfect pairing has exactly cardinality(U)/2 edges; for odd cardinality the sum is empty.

**Theorem 1.4 (Double-factorial count).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PerfectPairingCount.perfectPairingCount`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PerfectPairingCount.perfectPairingCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the cardinality of U is even, p(U) equals the double factorial of (cardinality(U) minus one), where natural subtraction gives zero in the empty case. If the cardinality is odd, p(U) equals zero. A perfect pairing corresponds bijectively to the fixed-point-free involution on U that exchanges the endpoints of each edge. The inverse sends an involution sigma to its set of two-cycles {x,sigma(x)}. The even formula applies the existing cycle-type count card_fixedPointFreeInvolution and simplifies its factorial quotient by the even double-factorial identity. The odd case follows because every perfect pairing covers twice its number of edges. In particular, a four-element label set has three perfect pairings and a six-element label set has fifteen.

**Theorem 1.5 (Counting partial pairings).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PerfectPairingCount.partialPairingCount`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PerfectPairingCount.partialPairingCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite label set U and natural p, the number of partial pairings of U with p edges equals choose(cardinality(U),2p) times (2p-1)!!. The empty pairing is included. The support of such a pairing has cardinality 2p, and its edges form a perfect pairing of the support. Conversely, a perfect pairing of a 2p-element subset of U is a partial pairing of U with p edges. Summing the perfect-pairing count over all possible supports gives the formula.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PerfectPairingCount.card`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PerfectPairingCount.finitePairingPolynomial_const`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PerfectPairingCount.finitePairingPolynomial_rankOne`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PerfectPairingCount.partialPairingCount`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PerfectPairingCount.perfectPairingCount`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartialPairingPolynomial](PartialPairingPolynomial.md)
- Dependency: [D5/S3/Zeros/Convolution/PerfectMatchingCount](../../../../Zeros/Convolution/PerfectMatchingCount.md)
