---
slug: bingham-2026-caterpillar-principal-specialization-family
bibkey: bingham2026principalspecializations
doi: 10.48550/arXiv.2610.31785
url: https://arxiv.org/abs/2610.31785v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarPs3Family.result
---

# Equal third and unequal second principal specializations for a caterpillar family

## Problem

Aram Bingham, Kyle Celano, Patricia Commins, Rosa Orellana, Jianping Pan, and Mary Claire Simone,
*Principal specializations of the t-chromatic symmetric function*, arXiv:2610.31785v1,
Remark 3.11, first question:

> Do (5,j,j,4,3) and (4,j,j,5,3) exhibit this phenomenon for all j?

The single target is the conjunction, for every positive integer j, that the actual caterpillars
of Definition 2.1 associated with these two compositions have unequal ordinary second principal
specializations and equal ordinary third principal specializations. Equality and inequality are
those of formal integer polynomials in X. Equation (2.1) uses colors 0 through k−1 and sums
over all proper colorings; every color need not occur. The coefficient inclusion into the source's
complex polynomial ring is injective. The t refinement is outside this question.

## Motivation

The source reports verification through j = 7. The family theorem replaces that finite range
by every positive j, including j = 1, for the source graphs themselves. The two specialization
comparisons form one question and one resolution.

## Gap

The source's finite verification does not establish an unbounded family. The missing uniform
step is supplied by an identity in arbitrary repeated middle weights, after expressing the
actual coloring sum as a sum over spine colors. The separate uniqueness question in Remark 3.11
is not part of this target.

## Route

Restrict a proper coloring to the spine and its leaves. This gives a bijection with a proper
spine coloring and independent leaf color choices different from the incident spine color.
For a positive part m and spine color c, write

$$B_m(c)=X^c\left(\sum_{\substack{0\le d<k\\d\ne c}}X^d\right)^{m-1}.$$

The coloring polynomial is the sum, over consecutive unequal spine colors, of the product of
these block weights. A part equal to one has no leaves and contributes the zeroth power one.

For k = 3, let F(A,B,C,D,E) be the sum of
A(c₀)B(c₁)C(c₂)D(c₃)E(c₄) over c₀,…,c₄ in {0,1,2} with consecutive colors unequal.
The identity `diagonal_identity` states

$$F(B_5,w,w,B_4,B_3)=F(B_4,w,w,B_5,B_3)$$

for every function w from {0,1,2} to Z[X]. Substituting w = B_j proves the third-specialization
equality without enumerating j. For k = 2, the two alternating spine colorings give exactly

$$\operatorname{ps}_2(5,j,j,4,3)=X^{j+5}+X^{j+7},\qquad
\operatorname{ps}_2(4,j,j,5,3)=X^{j+6}+X^{j+6}.$$

Their coefficients at degree j+5 are respectively one and zero.

## Falsifier

A positive j for which the ordinary third coloring polynomials differ, or for which the second
coloring polynomials agree, would contradict the target. Numerical agreement at a chosen X
does not establish formal polynomial equality.

## Result and scope

`D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarPs3Family.result`
establishes the displayed conjunction for every positive j. The dependent vertex carrier,
symmetrized edge relation and proper-coloring sum represent the source graphs and polynomials.
The coloring factorization includes empty leaf sets. The repeated-weight identity keeps the
outside blocks 5 and 4 and the final block 3 fixed; it does not assert arbitrary endpoint
replacement. The two-color formulas separate the coefficients at degree j+5.

The separate `BinghamCaterpillarUniquenessRefutation.result` refutes the exhaustive-pairs
assertion using an eighteen-vertex witness. The family theorem supplies no classification.
The source's four-color questions and analogous t-refined statements remain unresolved here.

## Literature limits

The bounded literature screen described in the Library note found no earlier settlement;
citation and third-party code searches were incomplete. This does not establish exhaustive
absence, originality or priority.
