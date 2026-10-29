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
The private helper `diagonal_identity` proves

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

## Evidence

`D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarPs3Family.result` proves
the exact conjunction for all positive j. Its public definitions retain the dependent vertex
carrier, symmetrized source edge relation, actual proper-coloring sum, and the two five-part
compositions. The coloring bijection, leaf factorization, repeated-weight identity, and
coefficient separation are compiled helpers on its proof path. The proof uses no finite cutoff
on j and no numerical specialization of X.

## Triage

`theorem`; the anchor is only the first question of Remark 3.11.

### What the settlement shows

- Proved: the whole positive-j conjunction, by
  `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarPs3Family.result`.
- Proved on that result's live proof path: `coloring_factorization` expresses actual colorings
  as independent leaf choices over proper spine colorings. It includes empty leaf sets.
- Proved on that result's live proof path: `diagonal_identity` allows any repeated three-entry
  polynomial middle-weight vector. The fixed outside blocks are 5 and 4, with final block 3.
  This is the uniform mechanism for all positive j; it asserts no general endpoint replacement.
- Proved on that result's live proof path: `ps2_alpha` and `ps2_beta` give the displayed exact
  two-color monomials, and `ps2_ne` separates their coefficients at degree j+5.
- Separate result: the exhaustive-pairs assertion in the second question is refuted by
  `BinghamCaterpillarUniquenessRefutation.result`; its distinct problem dossier gives the
  eighteen-vertex witness. The first-question family proof supplies no classification.
- Open here: the source's four-color questions and any analogous t-refined statement. This
  resolution supplies no settlement of those questions or additional source results.

## ASSUMED-UNVERIFIED

The bounded literature screen described in the Library note found no earlier settlement;
citation and third-party code searches were incomplete. No exhaustive absence or originality
claim is made. No conclusion about uniqueness, arbitrary end blocks, four colors, or the
t refinement is asserted.
