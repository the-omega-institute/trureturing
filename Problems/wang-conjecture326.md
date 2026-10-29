---
slug: wang-conjecture326
bibkey: wang2025semigrouprings
doi: null
url: https://arxiv.org/abs/2509.18724v1
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Algebra/WangConjecture326Refutation.result
---

# Wang Conjecture 3.26: finite algebraic constant does not bound the relative constants

## Problem

Guoqing Wang, *Semigroup rings and algebraically independent sequences with
respect to idempotents in commutative semigroups*, arXiv:2509.18724v1,
Conjecture 3.26, states:

> Let S be a commutative periodic semigroup, and let R be a commutative
> unitary ring. If d(S,R) < infinity then
> sup {D_bar(a)(S/H): a in S and <a> is not a group} < infinity.

The source is preregistered in [issue 23896](https://github.com/the-omega-institute/trureturing/issues/23896).
Conjecture 5.3 is a separate finite-semigroup assertion and is not a second
settlement of this question.

| Source clause | Formal counterpart |
| --- | --- |
| every commutative semigroup, including infinite and nonunital ones | `S : Type`, `[AddCommSemigroup S]` |
| periodic | `Periodic S`: each native `AddSubsemigroup.closure {a}` is finite |
| positive cyclic generation | `cyclic a`, without adjoining a zeroth multiple |
| actual cyclic idempotent | `IsCyclicIdempotent` and `cyclicIdempotent`; pointwise existence uses finite cyclic closure |
| every commutative unitary ring | `R : Type`, `[CommRing R]`; no field hypothesis |
| ordinary semigroup algebra | upstream `AddMonoidAlgebra R S`, retaining all labels |
| all independently nonzero positional coefficients | `GoodSequence`: every `c : N -> R`, with `c i != 0` for each occupied position |
| finite algebraic constant | `algebraicD S R < top`, supremum of finite good lengths |
| actual principal ideals | `principalIdeal a = {a} union {a+c : c in S}` |
| Green quotient | native quotient of `greenCon S`, whose relation is equality of those ideals |
| cyclic nongroup, with its own possible identity | negation of `CyclicIsGroup a`, quantifying identity and inverses inside `cyclic a` |
| relative constant at the canonical image | `relativeD ((greenCon S).toQuotient a)` |
| relative irreducibility | no shorter sublist, including empty, has the same sum |
| one uniform bound over all filtered elements | `nongroupSup S < top` |
| whole implication and exact negation | closed `claim : Prop`; designated `result : Not claim` |

All supremums are in ENat. Infinity means unbounded finite lengths; no
infinite product or finite truncation substitutes for the source assertion.
Nonempty products require no algebra unit. Length zero contributes only
zero to the length supremum. The empty sequence sums only to an existing
two-sided identity. In a monoid this is exactly the usual list sum, so the
empty proper subsequence is included in the counterexample's irreducibility.
Lists enumerate the source's unordered sequences and their submultisets;
commutativity makes enumeration irrelevant.

## Motivation

The algebraic constant measures cancellation of products, while relative
irreducibility can also detect independent semilattice coordinates. The
counterexample separates these two effects inside one semigroup.

## Gap

The proposed implication requires one bound uniform over all nongroup
cyclic elements. Pointwise finite cyclic closures give no uniform bound on
the number of independent union coordinates.

## Route

The carrier is one fixed infinite commutative monoid

$$S=\operatorname{Finset}(\mathbb N)\times\{0,1,2\},\qquad
(A,k)+(B,l)=(A\cup B,\min(2,k+l)).$$

The injection i maps to ({i},0) proves infinitude. If E(A,k)=(A,0) for k=0
and E(A,k)=(A,2) otherwise, every positive cyclic subsemigroup is exactly
{x,E(x)}. Thus S is pointwise periodic. The proof never instantiates an
interface requiring globally finite S. The level operation is min-capped
addition, not the modular addition of `Fin 3`.

For R=Q choose every positional coefficient to be one. An idempotent term
has zero factor. Otherwise two level-one terms have all four convolution
labels equal and their coefficients cancel. Every product of length at
least two therefore vanishes for an allowed assignment. The sufficient
bound is d(S,Q)<=1. An exact value is not required or asserted by this unit.

The principal ideal of (A,k) consists exactly of (B,l) with A subset B and
k<=l. Equality of principal ideals forces both coordinates equal, so the
actual quotient map is injective on the entire infinite carrier.

For each n, put a_n=({0,...,n-1},1). The sequence T_n has one marked term
(empty,1) and all singleton terms ({i},0) for i<n. Its length is n+1 and its
sum is a_n. The weight

$$w(A,k)=|A|+\mathbf 1_{k\ne0}$$

is subadditive. Each term of T_n has weight one, and w(a_n)=n+1. A sublist
with sum a_n must therefore have at least n+1 terms. This proves full
relative irreducibility and passes through the injective actual Green
quotient. Consequently D_bar(a_n)(S/H)>=n+1 for every n within the same S.
The positive cyclic subsemigroup at a_n has no identity even of its own:
neither its level-one nor its level-two element fixes a_n. Every a_n belongs
to the source's nongroup filter. The filtered supremum is therefore top.

## Falsifier

A globally finite carrier, modular level addition, contracted convolution,
a shared coefficient for equal labels, or a family of different finite
semigroups would fail to match the source. Failure to preserve proper
subsequences or the actual principal-ideal quotient would also invalidate
the refutation. An earlier exact settlement would affect the named
open-problem admission basis, without changing the mathematical negation.

## Evidence

The formal owner is `WangConjecture326Refutation`, with closed `claim : Prop`
and designated `result : Not claim`. Pointwise periodicity,
the convolution upper bound, principal-ideal coordinates, quotient
injectivity and the unbounded irreducible family form its proof path.
The primary versioned HTML supplies the whole source statement. The
related source note records the versioned author-source hashes and the
separate 5.3 statement.

All authored theorems have `proof_shape: bind-only`. The named external
Tier1 admission basis is `open-problem-resolution` under issue 23896.
The private theorems are consumed in the result's derivation and are not
escape witnesses. The `Infinite Model` instance is a separate certificate
of the fixed witness's infinitude, not a consumed result helper or escape
witness. The only public authored theorem is the designated literal
refutation `result`, exempt from the four-slot escape audit.

## Triage

The mechanism separates pairwise cancellation in the ordinary algebra from
the arbitrarily many independent union coordinates needed by relative sums.
No exact formula for individual relative constants, minimality assertion,
or classification of repairs to the conjecture is supplied.

Proved by the displayed construction: finite algebraic constant alone does
not control the number of independent union coordinates in relative sums.
The finite-semigroup restriction makes the filtered set of elements finite,
but a separate bound on each relative constant would still be needed;
this unit supplies no theorem classifying that restriction. The source's
Remark 3.27 invokes Conjecture 3.26 to infer an equivalence; this derivation
cannot use the refuted implication. The converse direction and other
hypotheses of Theorem 3.25 remain separate source statements.

Unresolved here: which additional uniform structural hypotheses restore
the implication, exact individual relative constants, and the independent
status of Conjecture 5.3. No new successor is preregistered by this unit.

Ordinary convolution and congruence quotients are reused from pinned
Mathlib. The positive cyclic closure is the native subsemigroup closure,
allowing pointwise finite cyclic sets inside infinite S. The proof uses
neither globally finite cyclic-idempotent interfaces nor field-only
definitions in its universal claim. The shared paper note retains the
separate Conjecture 5.3 statement and six-label mathematical argument.

## ASSUMED-UNVERIFIED

The bounded literature context is the source and preregistration. Novelty,
priority and exhaustive later-literature absence are not established.
The formal theorem concerns Conjecture 3.26 only. The shared note's
separate six-label argument about Conjecture 5.3 is not an additional
formal conclusion of this theorem.
