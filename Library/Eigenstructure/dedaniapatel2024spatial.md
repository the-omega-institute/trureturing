---
bibkey: dedaniapatel2024spatial
authors: H. V. Dedania and A. B. Patel
year: 2024
title: "Spatial numerical range in non-unital, normed algebras and their unitizations"
doi: null
url: https://arxiv.org/abs/2306.16172v1
claim: "Section 1, page 2, asks whether the spatial numerical range of an element of a non-unital normed algebra is always convex."
strata_touched:
  - D5/S3/Analytic/NumericalRange/SpatialNumericalRangeNonconvex
license: citation-only
triage: anchor
---

## Locator

Author text: <https://arxiv.org/abs/2306.16172v1>.
H. V. Dedania and A. B. Patel, *Spatial numerical range in non-unital, normed algebras and their unitizations*, arXiv:2306.16172v1, §1, p. 2; *Sarajevo Journal of Mathematics* 20(2) (2024).

## Spatial numerical range and convexity question

For a complex normed algebra $A$, put

$$
S(A)=\{x\in A:\|x\|=1\},\qquad
D_A(x)=\{\varphi\in A^*:\|\varphi\|=1=\varphi(x)\},
$$

$$
V_A(a;x)=\{\varphi(ax):\varphi\in D_A(x)\},\qquad
V_A(a)=\bigcup_{x\in S(A)}V_A(a;x).
$$

The authors ask verbatim: “It is still open problem wether $V_A(a)$ is always convex? This problem is discussed in [5].” Their reference [5] is the companion arXiv:2306.16141, *On the convexity of the spatial numerical range in non-unital normed algebras*. Its abstract says that the authors believe the problem is still open and that the answer seems to be negative; it proves convexity in several specific non-unital Banach algebras. These are statements about the authors' description of the literature, not an exhaustive assertion of priority.

## Repository-derived counterexample

Let

$$
P=\frac15\begin{pmatrix}1&2\\2&4\end{pmatrix},\qquad P^2=P,
$$

and give $A=\mathbb C\oplus\mathbb C^2$ the multiplication and norm

$$
(\alpha,x)(\beta,y)=(\alpha\beta,\alpha Py+\beta x),\qquad
\|(\alpha,x)\|=\max(3|\alpha|,\|x\|_\infty).
$$

For $e=(1,0)$, the norming pairs $((0,(1,i)),x\mapsto x_0)$ and $((0,(i,1)),x\mapsto x_1)$ give

$$
z_1=\frac15+\frac25i,\qquad z_2=\frac45+\frac25i\quad\text{in }V_A(e).
$$

Their midpoint $m=\frac12+\frac25i$ is absent. In the rescaled coordinates $u_0=3\alpha$, a norm-one functional has coefficients satisfying $|c_0|+|c_1|+|c_2|\le1$. Its norming condition makes each diagonal product real and nonnegative. Attaining imaginary height $2/5$ forces $c_0=0$, $|c_1|+|c_2|=1$, and purely imaginary cross products. At the proposed midpoint the diagonal and cross products would have real parts of opposite signs after multiplication, contradicting their common product identity.

## Evidence and boundary

The public declarations in `D5/S3/Analytic/NumericalRange/SpatialNumericalRangeNonconvex.lean` are `spatialNumericalRange`, `claim`, and `result`. The normed-algebra structure, endpoint memberships, midpoint exclusion and nonconvexity are established by the private instance declarations and lemmas. The theorem `D5.S3.Analytic.NumericalRange.SpatialNumericalRangeNonconvex.result` has type `¬ claim`. The axiom closure is $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

**ASSUMED-UNVERIFIED — literature boundary.** Bonsall–Duncan, *Numerical Ranges I/II*, have not been read for the question of whether they contain an element of a non-unital normed algebra with nonconvex spatial numerical range. The source authors cite the books and still describe the question as open. The general Banach-space-operator literature on nonconvex spatial numerical ranges has not been read either. The classical convexity of algebra numerical ranges in unital normed algebras does not by itself identify the spatial range in a non-unital algebra.
