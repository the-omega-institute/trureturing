# Uniform covers above the S and J Heawood lifts

## Abstract

Both optional matching lines give the stronger density and gap bounds for uniform covers.

**Theorem 1.1 (The bound with both optional lines).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodCoverDensity.both_lines_cover_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodCoverDensity.both_lines_cover_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Q be any graph isomorphic to a binary Heawood lift whose gain, up to conjugacy, has u=0 and v=1 in HeawoodMatching.gain. In any finite uniform neighborhood cover H of Q, four times the order of H is at most seven times beta(H,2). Also, forty-nine times the gap SF(H,2) minus beta(H,2) is at most the order of H. The uniform fiber size can be zero. Both optional lines give a dissociation set of order sixteen. The quotient has order twenty-eight, is cubic and is bipartite. The certificate density uses sixteen of twenty-eight vertices, and the cubic gap coefficient uses three times twenty-eight minus five times sixteen, which is four.

The original S signing has nonzero flags (3,3), (1,2) and (2,1). The J signing has nonzero flags (3,3) and (2,1). Changing to basis (1,4,2) gives u=0 and v=1 for both. The triples (a,b,c) are (0,0,0) for S and (0,1,0) for J. Both beta and SF equal sixteen in each of the two actual lifts. The uniform-cover inequalities therefore hold above either original lift, in its original labeling.

The two sixteen-vertex certificates come from HEAWOOD_HIGHER_COVER_BOUNDS.md, with their point and line selection lists as in HeawoodCertificates.lean. The six fifteen-vertex certificates come from HEAWOOD_DOUBLE_COVER_GAIN.md. All are from the subquorum-colorings contributors, revision 48728b42d39ab3de5de251c61da5a404ec418a69, under Apache-2.0. The entries of U and Q are matched point and line endpoints in corresponding order. W and Z give isolated points and lines. The Points and Lines lists give the full selections in their Lean list order.

A code 10p+s means Fano label p on sheet s in the indicated part. The base vertex index is p−1 for a point and 7+(p−1) for a line. HeawoodCoverParameters.pack sends a base vertex of index i on sheet s to 2i+s in Fin 28. In these coordinates a point and line are adjacent when their binary dot product is zero and their sheet sum in F2 equals the signing on their flag. Thus pack identifies the signed lift with the graph in the certificate coordinates for the same twists.

S (sixteen). U=[60, 20, 50, 10, 70, 30], Q=[10, 11, 20, 21, 30, 31], W=[], Z=[41, 51, 61, 71]. Points [10, 20, 30, 50, 60, 70]. Lines [10, 11, 20, 21, 30, 31, 41, 51, 61, 71].

J (sixteen). U=[40, 41, 20, 31, 51, 70, 61, 50], Q=[10, 31, 40, 41, 51, 60, 61, 70], W=[], Z=[]. Points [20, 31, 40, 41, 50, 51, 61, 70]. Lines [10, 31, 40, 41, 51, 60, 61, 70].

N1. U=[10, 20, 21, 30, 40, 41, 51], Q=[60, 50, 41, 70, 20, 31, 71], W=[], Z=[61]. Points [10, 20, 21, 30, 40, 41, 51]. Lines [60, 50, 41, 70, 20, 31, 71, 61].

N2. U=[10, 11, 20, 31, 40, 41, 60], Q=[40, 61, 50, 71, 30, 11, 70], W=[], Z=[51]. Points [10, 11, 20, 31, 40, 41, 60]. Lines [40, 61, 50, 71, 30, 11, 70, 51].

S (fifteen). U=[60, 20, 50, 10, 70, 30], Q=[10, 11, 20, 21, 30, 31], W=[], Z=[41, 51, 61]. Points [60, 20, 50, 10, 70, 30]. Lines [10, 11, 20, 21, 30, 31, 41, 51, 61].

J (fifteen). U=[60, 20, 70, 30], Q=[10, 11, 30, 31], W=[10, 50], Z=[21, 41, 51, 61, 71]. Points [60, 20, 70, 30, 10, 50]. Lines [10, 11, 30, 31, 21, 41, 51, 61, 71].

C. U=[10, 20, 41, 60, 70], Q=[41, 40, 31, 10, 30], W=[50], Z=[21, 51, 61, 71]. Points [10, 20, 41, 60, 70, 50]. Lines [41, 40, 31, 10, 30, 21, 51, 61, 71].

K. U=[20, 30, 31, 40, 50, 51, 70], Q=[11, 40, 31, 10, 20, 51, 60], W=[], Z=[61]. Points [20, 30, 31, 40, 50, 51, 70]. Lines [11, 40, 31, 10, 20, 51, 60, 61].

The nonzero flags for N1 are (1,2), for N2 are (1,2) and (2,4), for C are (1,4), (2,1) and (4,2), and for K are (1,4), (2,1), (4,2) and (2,4). The fifteen-vertex S and J selections use the same signing as their respective sixteen-vertex selections.

The published S and J certificates establish the respective sixteen-vertex selections and give the same density and gap bounds for covers above those two types. https://github.com/the-omega-institute/subquorum-colorings/blob/48728b42d39ab3de5de251c61da5a404ec418a69/docs/HEAWOOD_HIGHER_COVER_BOUNDS.md#L68-L101

Original fifteen-vertex selections. https://github.com/the-omega-institute/subquorum-colorings/blob/48728b42d39ab3de5de251c61da5a404ec418a69/docs/HEAWOOD_DOUBLE_COVER_GAIN.md#L110-L151

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodCoverDensity.both_lines_cover_bound`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodMatching](HeawoodMatching.md)
