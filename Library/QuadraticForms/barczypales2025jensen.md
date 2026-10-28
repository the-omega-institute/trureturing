---
bibkey: barczypales2025jensen
authors: Mátyás Barczy; Zsolt Páles
year: 2025
title: "Jensen convex functions and doubly stochastic matrices"
doi: null
url: https://arxiv.org/abs/2510.03715v1
claim: "Remark 2.2(i) asks whether the all-input comparison in equation (2.1) forces midpoint convexity for every real doubly stochastic matrix of rank at least two."
strata_touched:
  - D5/S3/QuadraticForms/BarczyPalesJensenConverse
license: citation-only
triage: anchor
---

# Jensen convex functions and doubly stochastic matrices

## Verified locator

- URL: https://arxiv.org/abs/2510.03715v1
- Primary text: https://arxiv.org/html/2510.03715v1#S2
- Exact anchors: Definition 1.1, Theorem 2.1(i), equation (2.1), Remark 2.2(i).
- Original TeX SHA-256: `e1fc8837e6a539035540c729f237a359f2dcb72b5500bc3a42173cbe16bacdc1`.

## Original question and scope

Remark 2.2(i) states:

> However, we do not know whether the assertion in part (i) of Theorem 2.1 holds for every doubly stochastic matrix having rank at least 2. We leave this question as an open problem.

The complete question quantifies over every positive integer $n$, every nonempty open interval $I\subseteq\mathbb R$, every arbitrary function $f:I\to\mathbb R$, and every actual nonnegative real doubly stochastic $n\times n$ matrix $P$ with real rank at least two. Its antecedent is

$$
f\left(\frac{1}{n}\sum_{j=1}^{n}x_j\right)
\leq \frac{1}{n}\sum_{i=1}^{n}f\left(\sum_{j=1}^{n}p_{ij}x_j\right)
\quad\text{for every }x\in I^n.
$$

The conclusion is midpoint convexity, the source's Definition 1.1:

$$
f((u+v)/2)\leq(f(u)+f(v))/2\quad\text{for every }u,v\in I.
$$

The rank condition replaces the original special normalized disjoint-support column-span condition; it does not retain that condition. No continuity, measurability, local boundedness, rational-matrix or rational-input assumption is present. Convexity of the interval makes every mean and matrix row image legal. The Lean claim uses arbitrary functions on the original interval subtype, with these membership obligations discharged by convex combinations. It does not require an ambient extension of the given function.

## Quadratic-field model

The companion module's closed proposition is `D5.S3.QuadraticForms.BarczyPalesJensenConverse.claim`; its theorem `D5.S3.QuadraticForms.BarczyPalesJensenConverse.result : ¬ D5.S3.QuadraticForms.BarczyPalesJensenConverse.claim` uses $n=3$ and $I=\mathbb R$. Put $s=\sqrt3$ and present $K=\mathbb Q(s)$ as `QuadraticAlgebra ℚ 3 0`. Its field structure uses the existing rational nonsquare transfer and prime nonsquare result. The injective quadratic lift sends $a+b\omega$ to $a+bs$, so the scalar action on $\mathbb R$ is multiplication through this actual embedding.

The existing vector-space linear splitting supplies a total $K$-linear retraction $L:\mathbb R\to K$ of that embedding. No finite-dimensionality of $\mathbb R$ over $K$ is assumed. Define

$$
F(x)=\bigl(N(L(x)):\mathbb R\bigr),\qquad N(a+b\omega)=a^2-3b^2.
$$

The norm is signed, and $L$ is linear rather than a field homomorphism. Classical choice supplies the splitting; an assumed retraction or a merely rational-linear surrogate is not used.

The actual matrix is

$$
P=\frac1{12}\begin{pmatrix}
5&3&4\\
s+2&6-s&4\\
5-s&3+s&4
\end{pmatrix}.
$$

The bounds $1<s<2$ give nonnegative entries. Every row and column sum is one. The top-left minor is $(3-s)/18>0$, so the actual real rank is at least two.

For every real triple $x$, let $m=(x_1+x_2+x_3)/3$ and $t=(x_1-x_2)/12$. Then

$$
Px=(m+t,\ m+(s-2)t,\ m+(1-s)t).
$$

Writing $A=L(m)$ and $B=L(t)$, genuine $K$-linearity and the quadratic coordinate formulas give

$$
N(A+B)+N(A+(\omega-2)B)+N(A+(1-\omega)B)=3N(A).
$$

Consequently $\sum_i F((Px)_i)=3F(m)$ for every real input, with no excluded degeneracies. Thus the source inequality holds with equality on the entire original input domain. Retraction gives $F(s)=F(-s)=-3$ and $F(0)=0$, while midpoint convexity at $s,-s$ would require $0\leq-3$.

The source's positive theorem with its original special column-span premise and its forward convexity implications remain separate. No regularity-restricted converse is settled by this unrestricted counterexample.

## Reuse and qualification boundary

The algebra, quadratic lift, field-hom injectivity, vector-space splitting, convex-combination membership and determinant/submatrix rank APIs are reused from mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. The finite norm cancellation and the full source-question application are compositions and algebraic normalization. This source note records the exact unrestricted question and its mathematical boundary; it makes no publication, priority or exhaustive-literature assertion.

The supplied bounded literature qualification identifies no earlier verified equal-or-stronger full answer. Niezgoda (2013), DOI `10.7153/mia-16-16`, supplies forward results assuming convexity. The later expected-loss paper arXiv:2606.22183 also imposes convexity and probabilistic/generator conditions. Neither quoted scope supplies this unrestricted converse. Burai–Makó–Szokol (2019) and the complete *Functions Generating Strongly Schur-Convex Sums* chapter, DOI `10.1007/978-3-0348-0249-9_13`, remain unread; other unexamined bibliography originals are not invoked. There is no claim of exhaustive literature coverage, global novelty or priority. Independent source-fidelity and prefreeze review remain outstanding.
