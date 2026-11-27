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
  - D5/S3/VertexAlgebra/TwistedGround/BarnesWall/OddGaussSum
  - D5/S3/VertexAlgebra/TwistedGround/BarnesWall/TensorIntertwiners
  - D5/S3/VertexAlgebra/TwistedGround/BarnesWall/OddCoherentTraceSign
  - D5/S3/VertexAlgebra/TwistedGround/BarnesWall/Rank32CommutingTrace
  - D5/S3/VertexAlgebra/TwistedGround/BarnesWall/TensorDefectDet
  - D5/S3/Fourier/CyclicFluxChargeExchange
  - D5/S3/VertexAlgebra/TwistedGround/BarnesWall/Rank128Lattice
  - D5/S3/VertexAlgebra/TwistedGround/BarnesWall/Q8GroundTrace
  - D5/S3/VertexAlgebra/TwistedGround/BarnesWall/PauliRows
  - D5/S3/VertexAlgebra/TwistedGround/BarnesWall/CyclicEtaTrace
  - D5/S3/VertexAlgebra/TwistedGround/BarnesWall/CoherentTraceSign
  - D5/S3/VertexAlgebra/TwistedGround/BarnesWall/FixedWordPhase
  - D5/S3/HomologicalAlgebra/BarnesWallQ8CohomologyDetector
  - D5/S3/HomologicalAlgebra/BarnesWallQ8CyclicGauge
  - D5/S3/HomologicalAlgebra/CentralCocycleTransport
  - D5/S3/HomologicalAlgebra/InflatedCubicCandidate
  - D5/S3/HomologicalAlgebra/QuaternionCandidateRestriction
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

Roberts's 2025 dissertation supplies the lift to the twisted group algebra
and the linearization of the defect representation at ranks 8, 32, and 128.
Chapters 7 and 8 concern these results in twisted group algebras and
projective representations. Conjecture 5.2 concerns the degree-three
chiral anomaly of the VOA action.
[Roberts, pp. 4–5 and Chs. 7–8](https://hdl.handle.net/10150/677567)

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
equivariantization theorems in the literature. The Lean development also
computes the three rank-128 Pauli defect determinants and checks the cyclic
cochain and its transport signs. The Dedekind eta calculation extracts the
coefficient $2^{32}$ from the modularly transformed quotient. The resulting
Lean theorem forces the zero candidate given the physical modular identity,
the ground coefficient limit for that character, and transport of its cyclic
action to the covariant ground-space operators.
[van Ekeren–Möller–Scheithauer, Theorem 5.13](https://arxiv.org/abs/1507.08142v3) ·
[McRae, Theorem 4.17](https://arxiv.org/abs/1910.13226v2) ·
[Gelaki–Naidu–Nikshych, Theorem 3.5](https://arxiv.org/abs/0905.3117)

## Reduction to two inflated classes

For a split elementary abelian two-group in any rank with at least two
hyperbolic pairs, the cyclic diagonal of a normalized three-cocycle
has degree at most three. Triviality on the lifted involution subgroups
makes the diagonal vanish on the quadratic zero cone. Its polynomial
then factors as the split quadratic form times an affine linear
function. The central coordinate of the sign extension provides an
explicit primitive for the inflated linear term. Over circle
coefficients this leaves two possible representatives, indexed by a bit.
[Ji–Tian, Theorem 6.1](https://arxiv.org/abs/2611.23231v1)

In the standard split extension, two coordinate slots support a
quaternion subgroup. Restricting the trilinear representative to this
subgroup gives the quaternion detector above. Its bar-cycle evaluation
separates the two candidates, so the bit is unique.

## Fixed-vector phases of the Pauli involutions

For the odd-rank tensor construction, separate the first tensor slot.
The two tail quotients carry complementary mod-two pairings. A Pauli word
pulls back each quadratic form by the sign of its square. For a fixed
integral vector this either kills one exceptional half-Gram correction,
or makes the two corrections equal so that their sum is zero. The Lean
theorem uses the two-block half-Gram hypotheses of Appendix A.1 and the
actual signed ambient involution. It applies to words containing both X
and Z factors in the same slot.
[Keller–Roberts–Roberts, Appendix A.1](https://arxiv.org/abs/2411.13646v2)

## Uniform quaternion Gauss sum

For any odd tensor slot count $m\geq 5$, the normalized Gram of the
subset rows has the complement pairing against every even-weight row.
The lower-triangular half Gram, including its halved diagonal, vanishes
on each block with the two active slots free. The integral Pauli
matrices act by the literal signed permutations on the scaled rows and
preserve their Gram. Their triangular lift defect gives the polarization
of the composed lift exponents.

On the even-row displacement coordinates the quaternion trace exponent
has zero basis values. Splitting by a spectator slot makes the cross
pairing a complement permutation and a square-zero shear. The resulting
finite Gauss sum is $+2^{2^{m-2}}$. The rank-128 value is $+2^{32}$.
[Keller–Roberts–Roberts, §2.2 and Appendix A](https://arxiv.org/abs/2411.13646v2)

## The rank-32 boundary

For the specified $E(5)$ action the order-four twisted ground has weight
$3/2$. Cyclic type is zero since four times the weight is integral. Its
normalized squared action has phase $+1$ on the ground, and the
reflection ground has weight $2$. These are the phases used in the
quaternion modular comparison, so the same comparison gives zero chiral
anomaly at rank 32. At rank eight the order-four weight is $3/8$ and its
cyclic type is $2$ modulo $4$, which detects a nonzero anomaly.
[Ji–Tian, equations (109)–(113)](https://arxiv.org/abs/2611.23231v1)

The rank-32 Lean calculation concerns a different pair of Pauli words.
The two rotations in distinct slots commute, and their lift exponent
has four independent blocks of character sum eight. The resulting
reflection-ground trace is $4096$. The abelian modular transform gives
trace $16$ for the reflection on the weight-one ground of the twisted
sector for the product involution. A character line in its even sector
can be selected by the slant of an inflated two-cocycle. The corresponding
holomorphic extension contains a weight-one Virasoro primary and has gap
one. Every choice has gap at most two. The all-ones tensor lattice row
has norm four and its pure translation stabilizer fixes the associated
primary with phase one, so the invariant orbit sum gives a weight-two
primary. For fixed trivial torsion the coherent centralizer projection
on the noncentral involution grounds still determines which gap occurs.
[Evans–Gannon, equation (2.7) and Corollary 2](https://arxiv.org/abs/1804.11145) ·
[Huang–Kirillov–Lepowsky, VOA extensions](https://arxiv.org/abs/1406.3420)

The complement bijection balances the row exponents and makes the
normalized tensor Gram unimodular. The same lower cocycle on the actual
reflection quotient therefore has a Weyl ground representation in every
such rank. Its even-row displacement subspace is the common image and
kernel of the two quaternion deviations. The literal lift exponent
vanishes on that subspace. This supplies nonzero covariant intertwiners
and identifies their normalized product trace with the Gauss sum above.

## The modular comparison in every odd tensor rank

For each order-four quaternion word, its square is negative identity on the
tensor lattice. Its defect transforms the unimodular Gram into twice that
Gram, so the defect has absolute determinant $2^{2^{m-1}}$. The square-root
defect rule gives multiplicity $2^{2^{m-2}}$.

The phase-free cyclic modular matrix becomes the exchange $(r,h)\mapsto
(h,-r)$ after summing over charges with the insertion character. This sends
the order-four character with central insertion to the reflection character
with inverse insertion. The paired reflection oscillators contribute a
factor tending to one at the cusp, and the transformed eta quotient gives
the stated multiplicity as the reflection ground trace.

A normalized inflated cocycle has trivial centralizer multiplier at the
reflection, which maps to the identity in the quotient. The two-cochain
used to change gauge supplies the explicit scalar correction in any
cohomologous representative. Scalar-related linear actions differ by
one global character, which the normalized tensor trace ratio cancels
by multiplicativity on $ij=k$. The extracted coefficient fixes the
remaining sign and forces the anomaly bit to vanish. The Lean comparison
takes the modular character matrix, the lattice twisted-character
formulas, and transport from the physical centralizer action as inputs.
In the VOA argument, the last transport is fixed by the trivial
self-monodromy of the charge-zero generator flux and its trivial mutual
monodromy with the charge-zero reflection flux.
[van Ekeren–Möller–Scheithauer, Theorem 5.13](https://arxiv.org/abs/1507.08142v3) ·
[McRae, Theorem 4.17](https://arxiv.org/abs/1910.13226v2)
