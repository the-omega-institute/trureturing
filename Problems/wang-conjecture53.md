---
slug: wang-conjecture53
bibkey: wang2025semigrouprings
doi: null
url: https://arxiv.org/abs/2509.18724v1
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Algebra/WangConjecture53Refutation.result
---

# Wang's Conjecture 5.3

## Problem

Wang, arXiv:2509.18724v1, Conjecture 5.3, asks whether every finite
commutative semigroup S and field K satisfying either the splitting
condition or the characteristic-p / p-power-exponent condition obey

$$d(S,K)=\max_{a\in S}\{\epsilon_a D_{\bar a}(S/\mathcal H)
+d(\Gamma(H_a),K)\}.$$

Here epsilon is zero exactly when the positive cyclic subsemigroup is a
group with its own identity. The algebra is the ordinary semigroup algebra,
the scalar quantifier is universal over individually nonzero scalars,
D is the relative irreducible-length constant at the canonical quotient
image, and Gamma consists of the actual stabilizer translation maps.

| Source clause | Lean counterpart |
| --- | --- |
| every finite commutative semigroup | `S : Type`, `AddCommSemigroup S`, `Finite S` in `claim` |
| arbitrary field and both alternatives | `Field K`, `Admissible S K` |
| ordinary basis and convolution | upstream `AddMonoidAlgebra K S` and its `single` |
| positive cyclic semigroup and idempotent | `positiveMultiple`, `cyclic`, `IsCyclicIdempotent`, `cyclicIdempotent` |
| period, exponent, splitting | `period`, `semigroupExponent`, `Splitting` |
| group property in epsilon | `CyclicIsGroup`, `epsilon` |
| every independently nonzero coefficient | `GoodSequence` quantifies all nonzero scalar functions of position |
| supremum, including unboundedness | `algebraicD : ENat`, supremum over every finite list |
| actual principal ideals and congruence quotient | `Below`, `Green`, `greenCon`, `GreenQuotient` |
| relative Davenport constant and empty subsequences | `SequenceSum`, `IrreducibleAt`, `relativeD` |
| actual stabilizer translations, equality of maps | `HClass`, `Gamma`, composition addition |
| maximum of the exact summands | `rightSide`, an ENat supremum over the finite carrier |
| whole universal equality and its negation | `claim : Prop`, `result : Not claim` |

The source's infinite-length notation is interpreted as unbounded admissible
finite lengths, without inventing an infinite product. For a general
nonunital semigroup algebra only positive products are used; a bottom length
zero does not affect the supremum. The empty sequence sums to an identity
only if the semigroup already has one. The model lies in a monoid over Q,
where the usual nonzero empty product is available. No zero-ring claim is
needed for the field-valued conjecture.

## Route

Use all six labels `(b,n)` in `{0,1} x {0,1,2}`, with maximum and addition
truncated at two. Q meets splitting branch (i), since all cyclic periods
and the exponent are one. Cyclic-idempotent existence for every finite
semigroup is obtained from the upstream compact-semigroup theorem with the
discrete topology; uniqueness follows from positive multiples.

A transient singleton has a coefficient that is always one. The all-ones
assignment kills every product of length at least two, without a finite
search cutoff. Hence d(S,Q)=1. Principal ideals distinguish the six labels.
The quotient sequence `[(0,1),(1,0)]` is irreducible at `(1,1)` and gives
relative D at least two. The cyclic semigroup of `(1,1)` has no identity,
so epsilon is one. Therefore the source right side is at least two, which
contradicts equality. No exact-right-side computation is claimed.

The claim uses the full finite-semigroup domain. Substituting one admissible
monoid into that universal claim is a logical counterexample to it; it is
not a conjecture restricted to monoids or to a bounded sequence length.

## Admission and boundaries

[Issue 23871](https://github.com/the-omega-institute/trureturing/issues/23871)
is the pre-probe Tier 1 named-problem admission basis. The externally named
final result uses `admission_basis: open-problem-resolution`. Its proof
contains the finite semigroup certificate, arbitrary-length algebraic
annihilation, quotient irreducibility, and the separation of constants.
Private helpers serve that live proof. The only public theorem is the
designated literal `result : Not claim`, exempt from the four-slot audit.
Definitions and instances introduce no additional public theorem audit.

The Library note gives source locators, source hashes, semantic conventions,
the mathematical derivation, and the bounded literature status. Existing
contracted-algebra refutations do not implement this question. The ordinary
algebra and congruence infrastructure are reused from pinned Mathlib;
no third-party code is transplanted. No independent mathematical novelty,
minimality, Conjecture 3.26 settlement, freeze, CI, or publication follows
from the local certificate alone.

## Falsifier

A contracted basis, coefficient choice shared by repeated positions, a
monoid restriction in the universal claim, an identity-adjoined Gamma,
incorrect cyclic periods, or a global Davenport constant substituted for
the relative one invalidates this refutation. Every such distinction is
kept in the source definitions. The numerical inequalities must follow
from the actual algebra and quotient, not from supplied number placeholders.
