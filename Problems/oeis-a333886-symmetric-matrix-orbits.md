---
slug: oeis-a333886-symmetric-matrix-orbits
bibkey: jovovic2026a333886
doi: null
url: https://oeis.org/A333886
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/MatrixOrbits/SymmetricRepresentativeSeries
---

# Generating function for symmetric-representative matrix orbits

## Problem

OEIS A333886 FORMULA, literal at commit `976b0c73e00453b1c1e6f16d83108cb9bb744c3b`

> Conjecture: G.f.: (1 - 2*x + 4*x^2 - x^3 + 9*x^4 + x^5 + 12*x^6 + 6*x^8 - x^9 + x^10)/((1-x)^3*(1-x^2)*(1-x^3)^2*(1-x^4)). - _Vladeta Jovovic_, Nov 25 2026

For every natural number n, including zero, take all 4 × 4 matrices with
natural entries whose row and column sums are each n. Quotient under
independent row and column permutations. The number of classes containing
at least one symmetric representative is the coefficient of degree n of
the displayed series in the rational formal power series ring.
[Literal formula](https://raw.githubusercontent.com/oeis/oeisdata/976b0c73e00453b1c1e6f16d83108cb9bb744c3b/seq/A333/A333886.seq)
[Representative convention](https://raw.githubusercontent.com/oeis/oeisdata/976b0c73e00453b1c1e6f16d83108cb9bb744c3b/seq/A052/A052281.seq)

## Motivation

Transpose acts on the full quotient by interchanging the two permutation
factors. The generating function counts classes visible through a
symmetric representative and relates these classes to twisted fixed
matrices.

## Gap

Lim's Theorem 3.5 counts transpose-fixed classes. Remark 3.6 distinguishes
that property from containing a symmetric representative in higher
dimensions. Here the size-four criterion holds. The five twisted
fixed-matrix counts must also be evaluated in all degrees to derive the
specific rational function.
[Lim, arXiv:2503.21108v1, Theorem 3.5 and Remark 3.6](https://arxiv.org/html/2503.21108v1#S3)

## Route

A finite certificate chooses one symmetrizing permutation per twist and
proves the needed position equalities by iteration. Twisted orbit–stabilizer
and grouping by cycle type give weights 1, 6, 3, 8 and 6. Graded fiber
equivalences count the five twists. The weighted sum yields the identity
after canceling units in the rational formal power series ring.

## Falsifier

A single natural degree whose full symmetric-representative quotient
cardinality differs from the stated coefficient would falsify the literal
formula.

## Evidence

The Lean theorem `A333886.source_identity_literal` gives the coefficient
identity for arbitrary n. Both sides are one at degree zero. The pinned
source asserts the formula and the preregistration records the bounded
literature screen, including no exact identifier hit in its arXiv API
query. Lim's orbit count supplies the closest located route.
[Preregistration #34467](https://github.com/the-omega-institute/trureturing/issues/34467)

## Triage

Theorem.

### What the settlement shows

**Proved.** The dimension-four transpose bridge identifies the transpose-fixed
classes in the full row and column permutation quotient with the classes
that contain a symmetric representative. Twisted orbit–stabilizer then
reduces their count to five graded fiber counts, one per permutation cycle
type with weights 1, 6, 3, 8, and 6. These counts hold in every degree.
Combining their series gives the published rational coefficient identity
for every natural margin in dimension four, including zero.
GID `D5/S3/Combinatorics/MatrixOrbits/SymmetricRepresentativeSeries.source_identity_literal`.

**Separate source questions.** A052281 describes its representative convention
using a lexicographic choice. The theorem counts each eligible class once
by existence of a symmetric member and makes no assertion about which
member the lexicographic rule selects. For Lim's higher-dimensional question,
the dimension-four bridge settles the implication from transpose-fixed
class to symmetric representative in size four. The corresponding
classification in higher dimensions remains open here.

## ASSUMED-UNVERIFIED

Exhaustive discovery of prior proofs and publication priority remain
unverified. The reported literature search is bounded by its stated queries
and sources.
