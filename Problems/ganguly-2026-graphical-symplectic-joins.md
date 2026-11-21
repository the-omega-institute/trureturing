---
slug: ganguly-2026-graphical-symplectic-joins
bibkey: ganguly2026graphicalsymplectic
doi: 10.48550/arXiv.2611.01241
url: https://arxiv.org/abs/2611.01241v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo.result
---

# Ganguly Question 9.2 on graphical symplectic matroids

## Problem

Sayantan Ganguly, *Representability of Graphical Symplectic Matroids*,
arXiv:2611.01241v2, §9, printed p. 39, asks:

> Over fields of characteristic 2 with at least 4 elements, is representability of 𝒮(G) preserved under 1-sums and under joining two graphs by a bridge?

The factors are finite multigraphs with one designated vertex each. The
source allows loops and parallel edges. A 1-sum identifies the two roots
and retains both sets of edge IDs. A bridge join keeps the vertices of
the two factors disjoint and adds one fresh edge between the roots.

## Motivation

Example 6.8 supplies positive examples and describes a 1-sum obstruction
over the two-element field. Question 9.2 asks whether fields with at least
four elements suffice for either closure law.

## Gap

The source and both operation clauses are registered in issue #32367.
The bounded literature screen recorded there found no settlement of
either clause in the accessed literature. The source's contraction and
unstarred-forest lemmas apply to the bridge mechanism. They supply no
representation of the two input factors or contradiction from the
triangle's marked edge columns.

## Route

Use the repository's directed incidence multigraph with independent
edge IDs and with connectivity ignoring orientation. An admissible
selection uses each ID at most once. The Chow test requires every
spanning component to be a tree or to have exactly one cycle with odd
star parity. A representation has the maximum Chow rank as its row
number, independent and isotropic rows, and exactly the Chow selections
as its nonzero admissible basis minors.

The first factor is a triangle with loops at vertices 0 and 1. The
second is one vertex with one loop. The roots are vertex 2 of the first
factor and vertex 0 of the second. For the first factor, two finite
determinant samples and affine dependence certify the basis test for a
field element distinct from zero and one. For the second, the rank-one
matrix is the pair of columns zero and one.

In the 1-sum, the three starred loops form a basis. Endpoint basis tests
force both endpoint coefficients of each marked triangle column to be
nonzero. The even-star tests force the three gain ratios to coincide
and square to one. In characteristic two this forces the common ratio
to equal one, contradicting the one-star determinant condition. In the
bridge join the nonzero unstarred bridge column can be quotiented out.
The finite Chow correspondence transfers the basis conditions to the
same triangle obstruction.

## Falsifier

A source mismatch in the two joins, a failed factor basis or isotropy
check, a valid gain assignment satisfying all the parity tests, or a
failure of the unstarred bridge correspondence would invalidate the
corresponding step. The field-uniform proof establishes the factor,
1-sum and bridge obligations from the concrete graphs and matrices.

## Evidence

The declaration `question_nine_two` proves both factor representations
and the two nonrepresentability conclusions over each qualifying field
in an arbitrary Lean universe. The closed `claim` asserts existence of
a qualifying field in Lean's `Type` universe over which either closure
law holds for all finite rooted graph pairs. The literal `result : Not claim`
uses the factor witnesses and the corresponding obstruction in each
case. Both statements use the same two graphs.

The §3.9 escape registration for `question_nine_two` is pending under
the [linked-issue exception in issue #32367](https://github.com/the-omega-institute/trureturing/issues/32367#issuecomment-7047172861). The utility-designated
`result` has the §3.9 refutation exemption.

## Triage

**Proved.** Both closure laws fail over every field in the question.
The admission basis is `open-problem-resolution`. The utility
classification is `bounded-enumeration` with a typed `refutes` edge.
The finite basis, determinant and contraction checks feed the
field-uniform proof.

### What the settlement shows

**Proved in this module.** The three starred loops in the 1-sum force
incompatible triangle basis tests in characteristic two. Quotienting
out the unstarred bridge column recovers those same tests for the
bridge join.

**Positive instances from the source.** Example 6.8 gives the
bridge-joined dumbbell X₁ over 𝔽₂ and the 1-sum chain X₅ over 𝔽₄.
These are instances where the respective joins are representable.
The same example exhibits a 1-sum failure over 𝔽₂ using X₅.

**Open here.** The looped witnesses leave closure for narrower classes
such as loopless graphs unresolved. Question 9.1 still asks for a
characterization over fields of characteristic two with at least eight
elements, including whether nonrepresentability implies a rigidly
linked pair after forest contraction. Question 9.3's NP-hardness
question for deciding 𝔽₄-representability also remains open.

## ASSUMED-UNVERIFIED

The literature search was bounded. Exhaustive literature status and
priority are unverified.
