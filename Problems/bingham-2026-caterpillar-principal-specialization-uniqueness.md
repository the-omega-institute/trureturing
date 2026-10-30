---
slug: bingham-2026-caterpillar-principal-specialization-uniqueness
bibkey: bingham2026principalspecializations
doi: 10.48550/arXiv.2610.31785
url: https://arxiv.org/html/2610.31785v1#S3.Thmtheorem11
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarUniquenessRefutation.result
---

# The exhaustive-pairs question for caterpillar principal specializations

## Problem

Bingham, Celano, Commins, Orellana, Pan and Simone, *Principal specializations of the
t-chromatic symmetric function*, arXiv:2610.31785v1, Remark 3.11, second question:

> And if so, do they continue to be the only pairs of compositions which do?

The assertion is that for every n at least one and every two source-admissible positive
compositions of n, unequal ordinary second and identical ordinary third principal
specializations imply that their unordered graph-isomorphism pair is the displayed base
pair {(5,4,3),(4,5,3)} or {(5,j,j,4,3),(4,j,j,5,3)} for some positive integer j.
All graph relabelings, reversals and pair exchanges are included. There is no size cutoff.
The first all-j question is a separate result and is not counted again here.

Definition 2.1 admits (1), and every nonempty positive composition whose two endpoint
parts are at least two, including length-one stars. The actual graph has one spine
vertex per part and a_i−1 pendant leaves at the ith spine vertex. Definitions 2.4,
2.7 and 2.9 and equation (2.1) give the ordinary specialization as the sum over all
proper colorings into {0,...,k−1} of X raised to the sum of vertex colors. Surjectivity,
weights, the t refinement and numerical evaluation of X are absent.

## Motivation

The source found only its listed pairs through total size sixteen. A pair outside
the full listed graph-isomorphism closure refutes the unrestricted assertion, without
requiring a classification of all other pairs.

## Gap

The listed pairs do not exhaust the phenomenon. The counterexample is

$$A=(2,2,2,2,2,1,4,3),\qquad B=(2,2,3,2,3,4,2).$$

Both compositions have total size eighteen and admissible endpoints. The formal claim
retains the full universal domain and is negated by its designated result.

## Route

Use the original `Vertex`, `edgeRel`, `caterpillar`, `ps`, `alpha` and `beta` definitions
from `BinghamCaterpillarPs3Family`. Its coloring factorization accounts for every actual
proper coloring exactly once. For spine color c, a part m contributes

$$X^c\left(\sum_{0\le d<k,\ d\ne c}X^d\right)^{m-1}.$$

Sum products of these weights over all consecutive unequal spine colors. Finite
polynomial normalization gives

$$P_2(A)=X^8+X^{10},\qquad P_2(B)=2X^9,\qquad P_3(A)=P_3(B).$$

The coefficient of degree eight separates the second polynomials. The source's complex
coefficient polynomials are defined as the same actual coloring sums over C[X]. A compiled
map-of-sums identity and injectivity of the coefficient map Z[X] to C[X] transfer both
comparisons; no coefficient-ring equivalence is merely assumed.

A vertex with two distinct neighbors must be on the spine, since a pendant vertex has
only its incident spine vertex as a neighbor. All eight spine vertices of A have two
distinct neighbors, including the internal vertex whose part is one. An isomorphism
from A to a listed member would induce an injection from eight indices into its spine
indices. The base members have three indices; every positive-j member has five, including
j=1. Cardinality therefore excludes all such graph isomorphisms. Since either order of
a listed pair would require A to be isomorphic to a listed member, the full unordered
pair closure is excluded. Lemma 2.2 and its length hypotheses are not used.

## Falsifier

A discrepancy in any coefficient of the actual third coloring polynomials, equality of
the second polynomials, or an actual graph isomorphism placing the witness pair in any
listed class would invalidate this counterexample. Agreement only at finitely many
values of X would not establish the needed identity.

## Evidence

The designated declaration is
`D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarUniquenessRefutation.result`.
Its source-declared type is literally the negation of the module's full `claim : Prop`. All polynomial,
coefficient-extension and isomorphism-exclusion helpers are on that result's proof path.
The claim includes the base pair, every positive j, and both pair orders through actual
graph isomorphisms. A finite witness negates this universal assertion for all sizes.

## Triage

- Compiled proof target (axiom closure outstanding) of the designated result: the whole exhaustive-pairs assertion is false.
- Compiled proof target (axiom closure outstanding) on its source proof path: the witness polynomials have unequal second and equal
  third ordinary specializations over the source's complex coefficient ring.
- Compiled proof target (axiom closure outstanding) on its source proof path: A is not isomorphic to any base or positive-j family
  member, so no listed unordered pair can represent this witness.
- The earlier first-question result, that every positive-j listed pair exhibits the
  phenomenon, is compatible with this refutation and remains a separate theorem.
- Unresolved: a classification of all pairs, the smallest counterexample size, other
  infinite families, four-color questions and t-refined analogues. No such consequence
  follows from the finite counterexample alone.
- A possible successor is a classification incorporating further collision mechanisms;
  this is a research direction, not a proved replacement assertion.

## ASSUMED-UNVERIFIED

The second-question proof source passes a guarded Lean build. Its accepted-axiom closure
and compiled utility evidence remain unchecked. No fully verified or published settlement
of the second question is asserted.

The bounded source and literature screen supporting the named external question did
not locate an earlier settlement. Citation and third-party code searches were incomplete.
No exhaustive absence, originality, priority or minimality claim is made.
