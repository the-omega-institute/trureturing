---
slug: zhang-li-2026-rank-one-hadamard-product-variational
bibkey: zhangli2026eigenvalueperturbation
doi: 10.48550/arXiv.2609.25552
url: https://arxiv.org/abs/2609.25552
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Schatten/ZhangLiRankOneProblemThree.result
---

# Zhang–Li rank-one Hadamard product variational problem

## Problem

Lei-Hong Zhang and Ren-Cang Li, *On a Conjecture Related to Eigenvalue
Perturbations*, arXiv:2609.25552v1, §1 Problem 3 and §5:

> Problem 3: Relate min_{W nonsingular} ‖W∘G‖_ui ‖W^{-1}∘G^T‖_ui to min_{P permutation} ‖P∘G‖_ui^2.

> In fact, for rank-one G, Romeo and Tilli [23, Theorem 1.2] proved (1.1) with c1=1 and the unitary restriction (2.3) with c2=1. They explicitly left the corresponding nonsingular version of Problem 3 unresolved; see [23, Remark 3.1].

For every natural $n$, every complex $n\times n$ matrix $G$ with
$\operatorname{rank}(G)\le1$, and every unitarily invariant norm $N$, the
precise conclusion is

$$
\inf_{W\in\mathrm{GL}_n(\mathbb C)}
 N(W\circ G)N(W^{-1}\circ G^{\mathsf T})
 =\min_{P\text{ permutation}}N(P\circ G)^2.
$$

A permutation minimizing $N(P\circ G)$ attains the infimum. The transpose
of $G$ is plain transpose. The zero matrix, zero weights, and $n=0$ are
included.

## Motivation

The question compares arbitrary changes of basis with discrete permutation
matchings in a norm expression associated with eigenvalue perturbations.
Equality with constant one would show that nonsingular matrices cannot
improve the rank-one permutation minimum, extending the cited unitary case.
Zhang–Li Theorem 1.1 already proves Conjecture 1.1 with $c=1$ for the
Frobenius norm for every $G$, without a rank restriction. The rank-one
question here concerns every unitarily invariant norm.

## Gap

The cited Romeo–Tilli unitary result does not cover arbitrary nonsingular
$W$. Singular values of such a $W$ can lie on either side of one. A common
lower bound must therefore connect the two factors involving $W$ and
$W^{-1}$ without imposing a unitary restriction. The classical background
is the lower Gelfand–Naimark inequality and symmetric-gauge norm comparison;
the required link is an expanding middle factor and its balanced average.
Zhang–Li Theorem 1.1 settles the Frobenius-norm case for every $G$ with
$c=1$; the missing case is the rank-one assertion for general unitarily
invariant norms. The source identifies this rank-one gap in §5. It is a
first-tier recent published question in the sense of the repository's problem classification;
the absence of later solutions is not independently established here.

## Route

**E1: expanding average.** For invertible $W$ and $t>0$, set

$$
T_t=\frac{tW+t^{-1}W^{-*}}2,\qquad W^{-*}=(W^{-1})^*.
$$

Writing $S_t=tW-t^{-1}W^{-*}$ gives
$T_t^*T_t-I=S_t^*S_t/4\succeq0$. This identity supplies expansion for every
positive scale. R. Bhatia, F. Kittaneh, R.-C. Li, “Some inequalities for
commutators and an application to spectral variation. II”, *Linear and Multilinear Algebra*
**43** (1997), no. 1–3, 207–219,
https://doi.org/10.1080/03081089708818526, §4, provides the related diagonal
matrix-and-inverse averaging precedent.

**E2: expanding diagonal minimum.** For nonnegative real diagonal weights
$a,b$, a single permutation $P_0$ satisfies

$$
N(\operatorname{diag}(a)P_0\operatorname{diag}(b))
\le N(\operatorname{diag}(a)T\operatorname{diag}(b))
\quad(T^*T\succeq I).
$$

For positive weights, put $C=\operatorname{diag}(a)T\operatorname{diag}(b)$
and $D=\operatorname{diag}(1/b)$. The lower Gelfand–Naimark inequality on
arbitrary index subsets bounds products of $s_i(CD)/s_i(D)$ by initial
products of $s(C)$. Expansion gives
$s_i(CD)=s_i(\operatorname{diag}(a)T)\ge a_i^\downarrow$ and
$s_i(D)=1/b_i^\uparrow$. Consequently the opposite matching
$x_i=a_i^\downarrow b_i^\uparrow$ satisfies, for every index subset $I$,

$$
\prod_{i\in I}x_i\le\prod_{j=1}^{|I|}s_j(C).
$$

Sort $x$ decreasingly. Its initial products now satisfy weak
log-majorization, which implies weak majorization through the initial
sum inequalities. The symmetric gauge representation $N(X)=\gamma(s(X))$
and Fan dominance give the norm comparison. A permutation realizing this
opposite matching gives $P_0$. Replacing both weights by $a+\varepsilon$
and $b+\varepsilon$ preserves their sorting permutations. Continuity as
$\varepsilon\downarrow0$ extends the same permutation to zero weights.

**E3: optimization in t.** Put $A=\operatorname{diag}(a)$,
$B=\operatorname{diag}(b)$ and $m=N(AP_0B)$. E1 and E2, the triangle
inequality, and homogeneity give, for every $t>0$,

$$
2m\le tN(AWB)+t^{-1}N(AW^{-*}B).
$$

For nonnegative $m,f,g$, these bounds imply $m^2\le fg$ with
$f=N(AWB)$ and $g=N(AW^{-*}B)$. If $m,f>0$, take $t=m/f$;
if $f=0<m$, take $t=(g+1)/m$ to obtain a contradiction. Thus the product
bound includes vanishing factors.

**E4: phases and attainment.** Factor $G=xy^{\mathsf T}$ and set
$a_i=|x_i|$, $b_i=|y_i|$. Removing diagonal unitary phases gives,
simultaneously for all $W$,

$$
N(W\circ G)=N(AWB),\qquad
N(W^{-1}\circ G^{\mathsf T})=N(AW^{-*}B).
$$

Transpose and adjoint invariance give the second identity; choose phase one
at zero entries. Every permutation matrix is expanding, so E2 also proves
that $P_0$ minimizes the permutation norm. Finally,
$P_0^{-1}\circ G^{\mathsf T}=(P_0\circ G)^{\mathsf T}$, giving equality of
the two factors at $P_0$ and hence attainment.

## Falsifier

A violation would consist of a dimension, rank-at-most-one complex $G$, a
unitarily invariant norm, and an invertible $W$ for which the product is
strictly below every squared permutation norm. A failure of attainment at
a minimizing permutation would also contradict the statement. Correctness
of this quantified assertion is separate from bibliographic priority.

## Evidence

The settling declaration is `result : claim` in
`D5/S3/Quantum/Schatten/ZhangLiRankOneProblemThree.lean`. Its claim provides
one permutation, the comparison with every permutation, the product lower
bound for every invertible matrix, and equality at that permutation.

| Mathematical step | Declaration |
| --- | --- |
| Balanced expansion | `inverseAdjointAverage_expanding` |
| Arbitrary-subset ratio bound | `lower_gelfand_naimark_ratio` |
| Singular-value growth under expansion | `expanding_right_singularValuesSorted` |
| Subset products to diagonal gauges | `UINorm.N_diagonal_subsetProducts_le` |
| Common expanding minimum | `UINorm.exists_permutation_expanding_lower_bound` |
| Balanced product bound | `UINorm.sq_le_product_of_expanding_lower_bound` |
| Rank-one phase reduction | `UINorm.rank_one_hadamard_reduction` |

These declarations express E1–E4. This dossier does not assert an additional
formalized transfer theorem or a solution in higher rank.

## Triage

The rank-at-most-one statement is **PROVED** by `result : claim`, including
the exact constant one and attainment. The decisive mechanism is a common
permutation lower bound on expanding matrices, coupled to an inverse-adjoint
average which is expanding at every positive scale. Allowing zero weights
requires continuity, and adds the zero matrix without weakening the result.

The following transfer principle is **proved at paper level, not
formalized**. Fix a real matrix $H$, a unitarily invariant norm $N$, and
$c\ge0$, and let $m_H=\min_P N(P\circ H)$. If, for every invertible complex
$Z$, the one-sided estimate

$$
m_H\le c\|Z^{-1}\|_{\mathrm{op}}N(Z\circ H)
$$

holds, then every invertible complex $W$ satisfies

$$
m_H^2\le c^2 N(W\circ H)N(W^{-1}\circ H^{\mathsf T}).
$$

To prove it, apply the hypothesis to the expanding matrix $T_t$ of E1.
Expansion gives $\|T_t^{-1}\|_{\mathrm{op}}\le1$. Since $H$ is real,
$W^{-*}\circ H=(W^{-1}\circ H^{\mathsf T})^*$, so adjoint invariance and
the triangle inequality give
$2m_H\le c(tN(W\circ H)+t^{-1}N(W^{-1}\circ H^{\mathsf T}))$ for every
$t>0$. The scalar argument of E3, with factors multiplied by $c$, proves
the assertion, including $c=0$ and zero factors. This consequence does not
supply the one-sided estimate for any additional $H$.

The rank-at-least-two question in Zhang–Li §5 remains **OPEN for general
unitarily invariant norms**. For the Frobenius norm it is **solved by
Zhang–Li Theorem 1.1**, which proves Conjecture 1.1 with $c=1$ for every
$G$. The common diagonal reduction here uses rank at most one; the result
does not extend that reduction to higher rank. No other conjecture or
downstream result is claimed as settled.

## ASSUMED-UNVERIFIED

The exact remark number for the Bhatia–Kittaneh–Li §4 averaging precedent
is ASSUMED-UNVERIFIED: “Remark 2” was reported through a secondary reading
and has not been independently inspected.

Romeo–Tilli Remark 3.1 wording has been read only through Zhang–Li's
citation. The original remark has not been independently inspected.
Citation indexes and subsequent literature have not been exhaustively
checked, and the absence of a later solution is not established. The
source quotations and metadata are supplied material; no online
verification is included. The transfer principle in Triage is a paper-level
consequence and has no corresponding formalized declaration in this delivery.
