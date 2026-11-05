# Three-row cyclic source family at half-modulus capacity

## Abstract

An explicit infinite three-row centered source family admits complete physical-label orders at the original half-modulus strip.

**Theorem 1.1 (A complete order for every J,m,d and cyclic shift).**

Lean statement: `D5/S3/Combinatorics/Circle/ThreeRowSource.exists_order`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/ThreeRowSource.exists_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every J>=2, m>=1, d>=1 and natural cyclic shift s, let r=2^J, H=2r-1, L=J+m(J+1), q=2^L, k0=3L+J+4 and k=d*k0. Put N0=2^k0-1, M=8rq^3-2Hq^2-q-1, lambda=(2^k-1)/N0, t=lambda*M.toNat modulo 2^k-1 and ts=2^s*t modulo 2^k-1. The theorem constructs a List(Fin(k)) permutation of every original physical label. Its actualSource(k,ts) total is zero and every natural take, including empty, full and overlength takes, has sum in [0,(2^k-2)/2]. No unit, least-period, d=1 or rotation hypothesis is added.

The row itinerary is source-specific. Its first three large values are M, -D and the two attained row masks V1,V2; the long and short affine maps fill the intervening dyadic ladders with the exact centered representatives. The polynomial identities prove the literal displayed M is positive and below the half-modulus strip, and the source equality N0=16rq^3-1 transports the row arithmetic to the original modulus.

Multiplication by two modulo the odd modulus is the cyclic group action on source labels. The physical map i -> (i+s) mod k is a Fin(k) equivalence, so the shift is a relabeling of occurrences rather than a re-identification of equal values. The repeated construction uses d physical buckets, each retaining its own Fin(k0) labels; the multiplier sum transports the base residue to modulus 2^(d*k0)-1. Repeated periods and nonunits therefore remain in the statement.

The centered representative is a coboundary: the unsigned potential changes by the actual source value along one doubling step. Telescoping that potential around every physical cycle proves the integer total zero. Concatenating the d buckets at height zero preserves every intermediate prefix bound; it does not replace the full physical row by a quotient of values.

The attained-mask invariant supplies the second packet. The first attained mask fixes the initial height, and the second disjoint mask is extracted from the untouched complement by the long/short affine maps. The proof checks the complete SMALL complement and the two seam inequalities, so the resulting list is a permutation of all labels. The construction retains repeated values as distinct physical positions.

The final cyclic relabeling applies the same group action to every physical label and leaves the strip and total conclusions unchanged. This is a sufficient family construction at the original half-modulus capacity. It does not claim the universal C3.1 statement, universal j0, a fixed-prefix certificate, or any global optimality result; C3.1 remains open.

The motivating source problem is Damasdi, Frankl, Pach and Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2, Conjecture 3.1, DOI 10.5070/C6.68671. The present family and its physical source correspondence are repository-derived, while the paper is cited only for the surrounding open problem.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/ThreeRowSource.exists_order`
- Dependency: [D5/S3/Combinatorics/Circle/SourceWidth](SourceWidth.md)
- Dependency: [D5/S3/Combinatorics/Circle/ThreeParentFamily](ThreeParentFamily.md)
- Dependency: [D5/S3/Combinatorics/Circle/ThreeRowParameters](ThreeRowParameters.md)
- Dependency: [D5/S3/Combinatorics/Circle/ThreeRowScheduler](ThreeRowScheduler.md)
- Dependency: [D5/S3/Combinatorics/Circle/TwoRunSource](TwoRunSource.md)
