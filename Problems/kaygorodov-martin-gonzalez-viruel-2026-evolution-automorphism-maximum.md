---
slug: kaygorodov-martin-gonzalez-viruel-2026-evolution-automorphism-maximum
bibkey: kaygorodov2026evolution
doi: 10.48550/arXiv.2610.22248
url: https://arxiv.org/abs/2610.22248v1
triage: theorem
motivation_gids:
  - D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl
  - D5/S3/Combinatorics/Partitions/EvolutionAutomorphismWeight
---

# The largest automorphism groups of perfect evolution algebras

## Problem

Kaygorodov, Martín González and Viruel, *Evolution algebras: a survey of
results and a list of open problems*, arXiv:2610.22248v1, section 2.3,
Conjecture 3, pages 27–28, state:

> Over C, the maximal order of the automorphism group of a perfect
> n-dimensional evolution algebra is
> max { product_l (l(2^l−1))^(m_l) m_l! : sum_l l m_l=n },
> that is 1, 6, 21, 72, 155, 1296 for n=1,...,6 and n! for n>=7.

The dimensions are positive. Multiplication is bilinear and need not be
associative. A natural basis has zero mixed products. Perfectness means
that the span of all pair products is the whole algebra. Automorphisms
are all multiplication-preserving complex linear equivalences.

## Motivation

The source isolates the unresolved interaction between the diagonal
kernel and the permutation image. Bounding these two parts separately
by their independent maxima loses their shared support structure.
EvolutionAutomorphismControl and EvolutionBasisTransport supply joint
control for the full source family; EvolutionAutomorphismWeight supplies
the exact positive-partition maximum and its shifted factorial absorption.

## Gap

The source asserts attainment by direct sums of coefficient-one cyclic
algebras and reports the upper bound checked by enumeration only through
dimension four. The general joint kernel/image bound and the sharp
universal inequality are separate from that reported computation.
The source is the origin of the conjecture and of the attaining-family
observation; the universal proof does not treat a conjectural assertion
as a supporting theorem.

## Route

Let P be the least successor-compatible quotient of the support relation,
let beta be its successor permutation, and let k(B) be the size of an
actual original fiber. Every k(B) is positive, their sum is n, and
1<=s=card(P)<=n. The actual diagonal kernel has the independent cycle-root
cardinality. The permutation image is controlled jointly by the full
centralizer of beta and the internal permutations of all fibers.

The root factor times the centralizer cardinality is exactly the weight
of beta's full partition of s, including singleton multiplicities.
Ascending-factorial monotonicity gives
product_B k(B)! <= (n−s+1)!, and shifted absorption gives
maximumWeight(s)(n−s+1)! <= maximumWeight(n). Conjugacy along an arbitrary
finite natural basis transfers the resulting full-group bound to every
complex module of finrank n.

For attainment, the product P_sigma(x*y) on Fin(n) to C has squares
e_i squared=e_(sigma(i)). Its invertible structure map makes it perfect.
Its actual permutation image is exactly the centralizer of sigma:
preservation implies commutation, and every commuting permutation has
an explicit multiplication-preserving linear lift. The actual kernel
is exactly the squaring assignments along sigma. The exact full-group
order is therefore the full partition weight.

Only the maximizing cycle types are needed: identity in dimension one
and in every dimension at least seven; single cycles of lengths two,
three and five; two 2-cycles in dimension four; three 2-cycles in
dimension six. The existing arithmetic identities supply all six
small values and the factorial tail.

## Falsifier

A perfect positive-dimensional complex evolution algebra whose full
finite automorphism order exceeds the stated maximum would contradict
the universal bound. Failure of an attaining witness to have the stated
dimension, natural basis, perfection, or exact full-group order would
invalidate attainment. A coordinate subgroup alone would not establish
the assertion about the full group.

## Evidence

The mathematical endpoint is
`D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismMaximum.result`.
Its first conjunct quantifies over arbitrary complex carriers, arbitrary
finite basis index types, finrank equality, the natural-basis law and
pair-product perfection. Its second conjunct constructs an actual
n-dimensional commutative perfect evolution product with the same
full-group cardinality bound as an equality.

The exact witness-group theorem is
`D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionPermutationFamily.permutation_aut_card`;
the universal inequality is
`D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionSharpBound.finite_and_bound`.
Lean kernel verification, scoped axiom closure and source binding determine
their formal status. Publication and literature priority are separate
from those mathematical statements.

## Triage

### What the settlement shows

Proved by
`D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismMaximum.result`:
the shared quotient size connects the diagonal root count to the permutation image. The positive fiber sizes account for
all original vertices, and their shifted factorial budget absorbs the
internal block-action kernel. This proves the source's all-dimensional
maximum without assuming a faithful quotient action or a graph lift.
The source's cyclic attainment observation is realized with actual
products and full groups by
`D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionPermutationFamily.permutation_aut_card`.
Open here: Conjecture 4, which restricts to simple algebras, and the other
conjectures in the survey. No claim about them follows from this settlement.

## ASSUMED-UNVERIFIED

The source's conjectural status refers to arXiv:2610.22248v1. Priority over
later literature is not established here. The formal theorem does not
assert originality of the cyclic attaining examples or a classification
of every algebra attaining the maximum.
