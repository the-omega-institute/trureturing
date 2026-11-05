---
slug: kaygorodov-martin-gonzalez-viruel-2026-finite-aut-infinite-natural-bases
bibkey: kaygorodov2026evolution
doi: 10.48550/arXiv.2610.22248
url: https://arxiv.org/abs/2610.22248v1
triage: theorem
motivation_gids:
  - D5/S3/QuadraticForms/EvolutionAlgebras/FiniteAutomorphismsInfiniteNaturalBases
---

# Infinite natural-basis quotient with finite full automorphisms

## Problem

Kaygorodov, Martin Gonzalez and Viruel, *Evolution algebras: a survey of
results and a list of open problems*, arXiv:2610.22248v1, section 2.2.2,
Question 14 asks:

> Describe the set of natural bases (up to permutation and scaling) of a
> non-degenerate evolution algebra. When is it finite? Can it be infinite
> for an algebra whose automorphism group is finite?

The endpoint is the entire final interrogative only. Its positive answer
requires a permitted field and a finite-dimensional commutative bilinear,
possibly nonassociative evolution algebra with zero annihilator, finite
full linear multiplication-automorphism group, and infinitely many natural
bases modulo all permutations and independent nonzero scalings. It does
not ask for every field, a group-scheme classification, or algebra-automorphism
orbits of bases.

## Motivation

A rank-one square can admit many orthogonal coordinate decompositions while
its distinguished nonzero idempotent restricts multiplication automorphisms.
These are different constraints on changes of natural basis.

## Gap

The algebra $A_{8,1}$, arbitrary-natural-basis equations and finite full
automorphism group are already in arXiv:1807.02362v1, Lemma 3.15 and
section 5.1. The same full-group ingredient occurs in arXiv:2303.00862v1,
Theorem 26 and Remark 29. The basis structure results of arXiv:2006.14460v1,
Corollary 2.13 and Proposition 2.16, are also credited. The infinite quotient
example in arXiv:2505.14584v1, Example 6.3, instead has nonzero annihilator
and infinite full group. The application separates infinitely
many classes in the exact quotient for the finite-group algebra.

## Route

Use $A=\mathbb C^2$ and
$\mu((x,y),(z,w))=(xz+yw,0)$, a complex-bilinear product without conjugation.
The standard basis is natural. Testing products against its two vectors
shows $\operatorname{Ann}(A)=0$. The square is the first coordinate line,
so this algebra is non-perfect as in the question's focus.

An arbitrary invertible complex-linear multiplication-preserving map fixes
$(1,0)$, since its image is a nonzero idempotent. Its image of $(0,1)$ has
first coordinate zero and second coordinate $d$ with $d^2=1$. Linearity
therefore determines the whole map from $d\in\{1,-1\}$, giving an injection
of the full group into Bool. No monomiality hypothesis is assumed.

For $t=n+1$, the vectors $(1,t),(-t,1)$ have zero mixed product and determinant
$1+t^2\ne0$. An explicit inverse constructs their basis. If the first
vectors for $t=n+1$ and $s=m+1$ are proportional without a swap, the scalar
is one and $n=m$. With a swap, proportionality forces $ts=-1$, contradicting
the positive natural integer $ts+1$ embedded in $\mathbb C$. This covers
arbitrary complex nonzero scalars. The resulting map from the natural
numbers into the exact quotient is injective.

Every basis in dimension two has two elements. Reindexing by Fin 2 uses
`Module.finrank_eq_card_basis` and `Module.Basis.reindex`; changing that choice
is exactly a permutation. The formal endpoint uses the canonical quotient
of all natural Fin 2-indexed bases. No separate arbitrary-index equivalence
is asserted to have been compiled.

## Falsifier

A failure of bilinearity, finite dimension, zero annihilator, actual basis
independence and spanning, full-group finiteness, or separation under any
allowed permutation and independent nonzero scaling invalidates the result.
Infinitely many ordered representatives or a finite monomial subgroup alone
would not answer the question. Quotienting further by algebra
automorphisms would change the target.

## Evidence

The source endpoint is
`D5/S3/QuadraticForms/EvolutionAlgebras/FiniteAutomorphismsInfiniteNaturalBases.result`.
Its exact type existentially quantifies a bilinear product on $\mathbb C^2$
and conjoins dimension two, commutativity, zero annihilator, an actual natural
basis, finite full automorphisms and an infinite exact quotient.

## Triage

### What the result shows

- The complete final interrogative has an affirmative answer over $\mathbb C$.
- The mechanism is the distinction between orthogonal natural-basis changes
  and multiplication automorphisms fixing the distinguished idempotent.
- No finite enumeration or numerical experiment supports the conclusion;
  its infinite family and all automorphisms are handled symbolically.
- The first two sentences' general description and finiteness classification
  remain outside this result.

## ASSUMED-UNVERIFIED

The bounded searches found no prior published whole answer. This
is not a worldwide absence or priority claim. Authenticated code search
was unavailable, and no search-complete status is claimed. The old algebra,
classification and basis ingredients retain their source credit.
