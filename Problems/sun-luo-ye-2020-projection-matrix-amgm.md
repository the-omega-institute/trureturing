---
slug: sun-luo-ye-2020-projection-matrix-amgm
bibkey: sunluoye2020projectionamgm
doi: 10.1287/moor.2019.0990
url: https://arxiv.org/abs/1503.06387v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/ProjectionAMGMRefutation.result
---

# The Sun–Luo–Ye projection-matrix AM-GM conjecture

## Problem

R. Sun, Z.-Q. Luo, and Y. Ye, *On the efficiency of random permutation for ADMM and coordinate descent*, Math. Oper. Res. 45(1) (2020), 233–271, Section 3.3, Conjecture 1, arXiv:1503.06387v3, state:

> We observe that we only need to prove a matrix AM-GM inequality for projection matrices. We conjecture that the following matrix AM-GM inequality holds.
>
> **Conjecture** (matrix AM-GM inequality for projection matrices). Suppose $P_i \in \mathbb R^{N \times N}, i=1,\dots,n$ are projection matrices, then
> $$\frac{1}{n!}\sum_{\sigma=(\sigma_1,\dots,\sigma_n)\in\Gamma} P_{\sigma_n}P_{\sigma_{n-1}}\cdots P_{\sigma_1}\preceq\left(\frac1n\sum_i P_i\right)^n.$$

Here $\Gamma$ is the set of permutations of $\{1,\dots,n\}$ and $X\preceq Y$ means that $Y-X$ is positive semidefinite. The source and its coordinate-descent motivation are recorded in [the Library note](../Library/QuadraticForms/sunluoye2020projectionamgm.md). Preregistration: [#15647](https://github.com/the-omega-institute/trureturing/issues/15647).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Real $N\times N$ matrices, indexed by $1,\dots,n$ | `claim`: dimensions `n N`, family on `Fin n`, real matrices on `Fin N` | Finite reindexing |
| Projection matrices | `claim`: symmetry and idempotence, inlined literally; the private instance proof uses Mathlib `IsStarProjection` | Orthogonal real projections; no rank restriction in the claim |
| $n$ projection matrices | `claim`: $1\le n$ | The source's reciprocal requires a positive number of factors |
| Arithmetic mean, raised to $n$ | `meanProj`, and its $n$th power in `claim` | The inverse of the real cast of $n$ scales the sum |
| Average over all permutations, with the first entry rightmost | `symProd` | The real inverse factorial scales the sum of reversed permutation words |
| Positive-semidefinite order | `claim`: the mean power minus the symmetrized product is `Matrix.PosSemidef` | Exact difference direction |
| Refutation of the universal assertion | `result`: negation of `claim` | Witness $n=N=3$; no assumptions on the result |

## Motivation

The source proposes the conjecture as a route to the best convergence rate of random-permutation coordinate descent for quadratic problems. Refuting the unrestricted projection inequality identifies a failure of that route; it does not determine the optimal coordinate-descent rate.

## Gap

The preregistration's literature screen found no settlement of this projection inequality within its searched scope. Related norm AM-GM inequalities, average-of-norms inequalities, and results for well-conditioned coordinate-descent matrices have different conclusions or hypotheses. Exhaustiveness of the literature screen is not established.

## Route

Write $M=n^{-1}\sum_i P_i$ and $G=(n!)^{-1}\sum_\sigma P_{\sigma_n}\cdots P_{\sigma_1}$. At $n=N=3$, let $z=(1,1,1)$ and $v_i=2e_i-z$, and set $P_i=v_iv_i^\top/3$.

The module's private `instance_is_projection` checks symmetry and idempotence. Its private `mean_form` and `sym_form` evaluate the two quadratic forms as $1/243$ and $1/27$. Its private `quadratic_form_value` therefore gives $z^\top(M^3-G)z=-8/243$. The private `instance_not_posSemidef` applies `Matrix.PosSemidef.dotProduct_mulVec_nonneg` to contradict this negative value; `result` refutes `claim`.

## Falsifier

The settlement would fail if these matrices did not satisfy the source's projection hypotheses, if permutation multiplication order were reversed incorrectly, or if the quadratic form were nonnegative. The compiled declarations check the hypotheses, the stated order and the negative value.

## Evidence

Kernel-checked source: [ProjectionAMGMRefutation.lean](../D5/S3/Quantum/Matrix/ProjectionAMGMRefutation.lean), namespace `D5.S3.Quantum.Matrix.ProjectionAMGMRefutation`. The public conclusion is `result`; the axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The scalar three-coordinate complement-projection argument under Triage is prose. Its corresponding unpublished source has reported Lean 4.33 compilation evidence, but no accepted current exact-type/axiom report. It is outside the kernel-checked refutation cited above.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9). There are no other new public theorems in this module.

Experiment entry: [sun-luo-ye-2020-projection-matrix-amgm](https://github.com/the-omega-institute/trureturing-experiments/tree/38f78a9f7126378ad73d9b496e1c73b6df883bc7/docs/reports/sun-luo-ye-2020-projection-matrix-amgm), script `check.py`. Command: `python3 check.py` from that directory, with NumPy installed. Exit code: 0. Script SHA-256: `5e7643a7ccb84fb77ca498bf6b810c56eb769b401d27b042e55f5e322d3bcfc9`. Final discrepancy count: `bad= 0`.

The exact rational checks enumerate all $n!$ words at $n=3,5,7$: respectively 6, 120 and 5040 words, with quadratic forms $-8/243$, $-50624/232058125$ and $-1838265624/3236831537545039$. Direct matrix word multiplication is also checked at $n=3$. The floating-point checks use the 399 interior points of a 400-step grid for each equiangular family at $n=2,3,4,5$. Negative points at $n=3$ range from $-0.49625$ to $-0.20375$; at $n=5$ from $-0.246875$ to $-0.1125$. There are no negative grid points at $n=2,4$. These grid readings do not establish a uniform continuum or even-$n$ result.

## Triage

| Item | Status and evidence kind | Scope |
| --- | --- | --- |
| Projection witness and $z^\top(M^3-G)z=-8/243$ | Proved, kernel-checked: private `instance_is_projection` and `quadratic_form_value`; public `result` refutes `claim` | $n=N=3$, $z=(1,1,1)$ |
| Odd-$n$ rational family and its closed form | Proved in prose below | Odd $n\ge3$; no uniform Lean theorem is delivered |
| Exact rational family readings | Computed by the experiment entry | $n=3,5,7$; quadratic forms and permutation enumeration listed in Evidence |
| Equiangular failing interval $-1/(n-1)<t<-1/(2n-1)$ for odd $n$ | Proved in prose below | Full-rank equiangular Gram matrices |
| Odd-$n$ transition grid readings | Computed by the experiment entry | $n=3,5$, 399 interior points of a 400-step grid each; agrees with the derived interval on those points |
| No equiangular failure at $n=2,4$ | Computed by the experiment entry | 399 interior grid points at each dimension; unrestricted even-$n$ inequality remains open |
| Scalar coordinate-descent class $P_i=I-a_i a_i^\top$, $n=N=3$ | Proved in prose below | Every unit, linearly independent triple; no sign or conditioning restriction |
| All-$n$ scalar and arbitrary-block coordinate-descent classes $P_i=I-A_iA_i^\top$ | Open | $A_i^\top A_i=I$ and square nonsingular concatenation; the rank-one refutation does not settle these classes |
| Optimal RP-CD convergence rate | Open | The source's intended application is not settled by this refutation |
| Unrestricted projection inequality for even $n$ | Open | No universal even-$n$ theorem or counterexample is delivered |

### What the settlement shows

**Odd-$n$ family, proved in prose.** For $n\ge3$, let $z=\mathbf1$, $v_i=(n-1)e_i-z$, and $d=n^2-3n+3$. Then $v_i^\top v_i=d$, $v_i^\top v_j=-(n-2)$ for $i\ne j$, $v_i^\top z=-1$, and $\sum_i v_i=-z$. Thus $P_i=v_iv_i^\top/d$ is a symmetric rank-one idempotent and $Mz=z/(nd)$. Consequently

$$z^\top M^n z=\frac1{n^{n-1}d^n},\qquad z^\top Gz=\frac{(-(n-2))^{n-1}}{d^n}.$$

Each permutation word has the second value because consecutive factors have distinct indices. For odd $n\ge3$, subtraction gives

$$z^\top(M^n-G)z=\frac{1-(n(n-2))^{n-1}}{n^{n-1}d^n}<0.$$

This derivation is a prose proof; the module checks only $n=3$. The experiment entry separately computes $n=3,5,7$.

**Equiangular mechanism, proved in prose for the odd-$n$ transition.** For $n\ge3$, let the unit-vector Gram matrix be $(1-t)I+tJ$, with $-1/(n-1)<t<1$, and write $V$ for the matrix of columns, $C=VV^\top$ and $s=V\mathbf1$. All words have adjacent inner products $t$. Counting words with prescribed distinct endpoints gives

$$G=\frac{t^{n-1}}{n(n-1)}(ss^\top-C),\qquad M=C/n.$$

Put $\lambda=1+(n-1)t>0$. On the direction $s$, the eigenvalue of $M^n-G$ is

$$\frac\lambda{n^n}\bigl(\lambda^{n-1}-n^{n-1}t^{n-1}\bigr).$$

On the orthogonal complement it is

$$\left(\frac{1-t}{n}\right)^n+\frac{t^{n-1}(1-t)}{n(n-1)}.$$

For odd $n$, the second eigenvalue is nonnegative. For $t\ge0$ the first is nonnegative since $\lambda\ge nt$. For $t<0$ the first is negative exactly when $\lambda<-nt$, namely $t<-1/(2n-1)$. Together with Gram positivity this gives the stated open failing interval. The rational family has $t=-(n-2)/d$ in that interval. The grid checks at $n=2,4$ are computed evidence only.

**Failure mechanism and surviving statements.** Symmetry, idempotence and positive semidefiniteness of the individual rank-one projections do not ensure the proposed comparison of the two averages. Negative pairwise inner products produce positive word contributions when $n-1$ is even, exceeding the mean-power value in the direction $z$. The paper's weaker bound $G\preceq M$ remains a literature result; it is not a theorem of this module. The conjecture's proposed implication for an optimal RP-CD rate cannot be obtained from the refuted unrestricted assertion.

The constructed rank-one projections in $\mathbb R^n$ have complements of rank $n-1$. Any factorization $I-P_i=A_iA_i^\top$ therefore needs at least $n-1$ columns in each $A_i$. Their concatenation needs at least $n(n-1)>n$ columns for $n\ge3$, so it cannot be square. This prose rank argument explains the scope boundary; it is not kernel-checked here. The all-$n$ scalar and arbitrary-block structured inequalities, their rate question and the unrestricted even-$n$ case remain open.

### Three scalar coordinate-descent columns, proved in prose

For every three unit, linearly independent columns $a_1,a_2,a_3\in\mathbb R^3$,
set $A=[a_1,a_2,a_3]$ and $P_i=I-a_i a_i^\top$. Then, with exactly the
existing meanProj and reversed symProd conventions,

$$
G=\frac16\sum_{\sigma\in S_3}P_{\sigma_3}P_{\sigma_2}P_{\sigma_1}
\preceq M^3,\qquad M=\frac13(P_1+P_2+P_3).
$$

Unit length makes each $P_i$ a symmetric idempotent complement projection.
The columns need not be mutually orthogonal, their correlations may have
either sign, and there is no positive lower bound on their conditioning.
This is the scalar $n=N=3$ part of the coordinate-descent class motivated by
Sun–Luo–Ye, equation (37) and Claim 4.1, equations (51a)–(51b). The argument
below is a complete prose derivation; it does not assert a new kernel-checked
public theorem or literature priority.

Write

$$
C=A^\top A=
\begin{pmatrix}1&x&y\\x&1&z\\y&z&1\end{pmatrix},
\quad x=a_1^\top a_2,\quad y=a_1^\top a_3,\quad z=a_2^\top a_3.
$$

This is the Gram matrix of the actual columns, so no separate realization
assumption is needed. Its positive semidefiniteness gives $x^2,y^2,z^2\le1$:
for example, its quadratic form at $(-x,1,0)$ is $1-x^2$, with analogous
vectors $(-y,0,1)$ and $(0,-z,1)$. Independence gives

$$
\delta=\det C=1+2xyz-x^2-y^2-z^2=(\det A)^2>0.
$$

To obtain the precise congruence, put $R_i=a_i a_i^\top$ and
$S=\sum_iR_i=AA^\top$. The six permutations occur exactly once in $G$.
In their expansion, each ordered pair of distinct $R_i$ has coefficient
$1/2$, while each word with all three indices has coefficient $-1/6$.
Since $R_i^2=R_i$,

$$
G=I-S+\frac12(S^2-S)-\frac16T_3,\qquad
T_3=\sum_{\sigma\in S_3}R_{\sigma_3}R_{\sigma_2}R_{\sigma_1}.
$$

Here $R_iR_jR_k=(a_i^\top a_j)(a_j^\top a_k)a_i a_k^\top$.
Thus $T_3=AHA^\top$, where

$$
H=\begin{pmatrix}0&yz&xz\\yz&0&xy\\xz&xy&0\end{pmatrix}.
$$

Also $M=I-S/3$, $S^2=ACA^\top$ and $S^3=AC^2A^\top$. Subtracting the
displayed expansion of $G$ from $M^3$ gives the exact identity

$$
M^3-G=A(B/54)A^\top,\qquad B=27I-9C-2C^2+9H,
$$

or, entry by entry,

$$
B=\begin{pmatrix}
16-2(x^2+y^2)&-13x+7yz&-13y+7xz\\
-13x+7yz&16-2(x^2+z^2)&-13z+7xy\\
-13y+7xz&-13z+7xy&16-2(y^2+z^2)
\end{pmatrix}.
$$

It remains to check the sign of this symmetric matrix over the entire
correlation region just obtained. Its first leading minor is
$d_1=B_{11}=16-2(x^2+y^2)\ge12$. For the second, write
$X=x^2$, $Y=y^2$, $Z=z^2$. Direct expansion gives

$$
\begin{aligned}
d_2&=B_{11}B_{22}-B_{12}^2\\
&=27+(1-X)(138-4X)+4X(Y+Z)+59(Y+Z)-45YZ+91\delta.
\end{aligned}
$$

Every term after $27$ is nonnegative, using $0\le X,Y,Z\le1$,
$\delta>0$, and the identity

$$
59(Y+Z)-45YZ=45Y(1-Z)+14Y+59Z.
$$

In particular $d_2>0$. For the determinant set
$p=x^2+y^2+z^2$, $q=xyz$,
$r=x^2y^2+x^2z^2+y^2z^2$, and

$$
T=(1-x^2)(1-y^2)(1-z^2)=1-p+r-q^2\ge0.
$$

The exact determinant identity is

$$
\begin{aligned}
\det B={}&(2322+90p)T\\
&+\delta(1342-154p+1694q-90q^2)\\
&+36(1-q)(12+11q-5q^2).
\end{aligned}
$$

Here $p\ge0$, $q^2\le1$ and $\delta=1+2q-p>0$ imply
$p<1+2q$ and $-1/2\le q\le1$. These bounds justify each sign without
a conditioning restriction. Explicitly,

$$
1342-154p+1694q-90q^2
{}>1188+1386q-90q^2
\ge1098+1386q\ge405>0,
$$

and $12+11q-5q^2\ge12-11/2-5=3/2>0$.
Consequently the first and third determinant terms are nonnegative and
the middle term is strictly positive, so $\det B>0$.

For completeness, the leading-minor criterion here follows from an exact
completion of squares. For $w=(u,v,t)$ one has

$$
\begin{aligned}
d_1d_2\,w^\top Bw={}&
d_2(d_1u+B_{12}v+B_{13}t)^2\\
&+\bigl(d_2v+(d_1B_{23}-B_{12}B_{13})t\bigr)^2
+d_1(\det B)t^2.
\end{aligned}
$$

Since $d_1d_2>0$, this proves $B\succeq0$. The congruence then gives
$w^\top(M^3-G)w=(A^\top w)^\top B(A^\top w)/54\ge0$ for every real $w$,
which is the claimed Loewner inequality. The argument uses only the
strict inequality $\delta>0$, so it includes independent columns
arbitrarily close to singularity.

This positive partial result concerns rank-two complements of unit
rank-one matrices. The kernel-checked counterexample above uses rank-one
$P_i$ and lies outside this coordinate-descent class. The all-$n$ scalar
inequality and the arbitrary-block question remain open. The latter has
$n\ge1$, $d_i\ge1$, $N=\sum_i d_i$, $A_i\in\mathbb R^{N\times d_i}$,
$A_i^\top A_i=I_{d_i}$ and square nonsingular concatenation
$[A_1,\ldots,A_n]$. The optimal RP-CD convergence rate and the separate
Kim–Lee–Yun second-moment comparison also remain open.

## ASSUMED-UNVERIFIED

The literature screen's completeness is unverified. In particular, the body of Luenberger–Ye, *Linear and Nonlinear Programming*, fifth edition, Chapter 14, DOI 10.1007/978-3-030-85450-8_14, was access-blocked in the recorded source check. Absence of a settlement in the searched sources is not a proof that none exists elsewhere. The family, transition and three-coordinate complement-projection derivations above are prose proofs, not new uniform kernel-checked results. The all-$n$ scalar and arbitrary-block inequalities, optimal RP-CD rate and separate second-moment comparison remain open. Numerical grid readings cover only their stated finite samples.
