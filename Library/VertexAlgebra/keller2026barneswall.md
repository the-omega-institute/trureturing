---
bibkey: keller2026barneswall
authors: Christoph A. Keller, Ashley Winter Roberts, and Jeremy Roberts
year: 2026
title: CFTs with Large Gap from Barnes-Wall Lattice Orbifolds
doi: 10.48550/arXiv.2411.13646
url: https://arxiv.org/abs/2411.13646v2
claim: Theorem 3.5 constructs the extraspecial lift and Conjecture 5.2 proposes a holomorphic rank-128 Barnes–Wall orbifold of gap four.
strata_touched:
  - D5/S3/VertexAlgebra/TwistedGround/BarnesWall/Q8TraceSign
  - D5/S3/VertexAlgebra/TwistedGround/BarnesWall/Rank128Lattice
  - D5/S3/VertexAlgebra/TwistedGround/BarnesWall/Q8GroundTrace
  - D5/S3/HomologicalAlgebra/BarnesWallQ8CohomologyDetector
license: citation-only
triage: anchor
---

<!-- GID: D5/L/VertexAlgebra/keller2026barneswall -->

# The rank-128 Barnes–Wall holomorphic orbifold

## Verified locator

DOI 10.48550/arXiv.2411.13646

Primary version https://arxiv.org/abs/2411.13646v2

Sections 2.2, 3.3 and 4.4 specify the lift phase and twisted-ground action.
Appendix A.1 gives the tensor lattice basis. Section 5.3 states Conjecture 5.2.

## Detecting the chiral anomaly

The generator lifts in §§2.2 and 3.3, the tensor lattice basis in Appendix A.1,
and the twisted-ground representation in §4.4 determine the finite trace
calculation for the specified $E(7)$ action. Conjecture 5.2 concerns the
vanishing chiral anomaly and the existence of a central charge 128
holomorphic orbifold of Virasoro gap four.

Ji and Tian's Theorem 6.1 proves that the chiral anomaly is inflated from
the elementary abelian quotient of $E(7)$. In their full CFT the two
pullbacks of the chiral classes coincide and cancel. In the holomorphic
problem the cyclic restrictions leave the split quadratic class as the
only possible nonzero inflation. An embedded quaternion group detects
that candidate via a seven-term bar cycle.
[Ji and Tian, arXiv:2611.23231v1](https://arxiv.org/abs/2611.23231v1)

The finite Lean calculation uses the stated half-Gram lift phases on the
actual common displacement image. Splitting by the third tensor bit
reduces its sign sum to a perfect cross pairing of dimension $32+32$ and
gives $+2^{32}$. The separate bar-complex calculation shows that the
candidate restricted to $Q_8$ pairs to $1/2$ modulo the integers and is
nonzero in degree-three circle-valued group cohomology.

The even unimodular tensor Gram realizes the stated lower-triangular
cocycle on the rank-128 reflection quotient. Its two prescribed lift
phases define covariant Weyl operators with individual traces `2^64`
and product trace `2^96`.

In the VOA argument, the order-four cyclic trivializations determine the
relative phases of the three centralizer actions through the cyclic modular
$S$ transform. Their physical trace product has positive sign, which
selects the zero class. This identification uses the cyclic trace and
equivariantization theorems in the literature. The Lean statements cover
the finite Gauss sum, the covariant ground-space operators, and the
cohomological detector.
[van Ekeren–Möller–Scheithauer, Theorem 5.13](https://arxiv.org/abs/1507.08142v3) ·
[McRae, Theorem 4.17](https://arxiv.org/abs/1910.13226v2) ·
[Gelaki–Naidu–Nikshych, Theorem 3.5](https://arxiv.org/abs/0905.3117)
