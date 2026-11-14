---
slug: sun-luo-ye-2020-projection-matrix-amgm
bibkey: sunluoye2020projectionamgm
doi: 10.1287/moor.2019.0990
url: https://arxiv.org/abs/1503.06387v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/ProjectionAMGMRefutation.result
  - D5/S3/Quantum/Matrix/ProjectionAMGMRefutationScalar200.result
---

# The Sun–Luo–Ye projection-matrix AM-GM conjecture

## Problem

R. Sun, Z.-Q. Luo, and Y. Ye, *On the efficiency of random permutation for ADMM and coordinate descent*, arXiv:1503.06387v3, Section 3.3, Conjecture 3.1, equation (37), PDF p.20, state:

> We observe that we only need to prove a matrix AM-GM inequality for projection matrices. We conjecture that the following matrix AM-GM inequality holds.
>
> **Conjecture 3.1** (matrix AM-GM inequality for projection matrices). Suppose $P_i \in \mathbb R^{N \times N}, i=1,\dots,n$ are projection matrices, then
> $$\frac{1}{n!}\sum_{\sigma=(\sigma_1,\dots,\sigma_n)\in\Gamma} P_{\sigma_n}P_{\sigma_{n-1}}\cdots P_{\sigma_1}\preceq\left(\frac1n\sum_i P_i\right)^n.$$

Here $\Gamma$ is the set of permutations of $\{1,\dots,n\}$ and $X\preceq Y$ means that $Y-X$ is positive semidefinite. The source and its coordinate-descent motivation are recorded in [the Library note](../Library/QuadraticForms/sunluoye2020projectionamgm.md). Preregistration: [#15647](https://github.com/the-omega-institute/trureturing/issues/15647).

The inspected mathematical source is arXiv v3. The matching journal record is
*Mathematics of Operations Research* 45(1) (2020), 233–271,
DOI [10.1287/moor.2019.0990](https://doi.org/10.1287/moor.2019.0990);
the journal PDF was not independently inspected. The conjecture number above
is the arXiv v3 number.

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

### Structured block target and source identities

The separately registered target [#17674](https://github.com/the-omega-institute/trureturing/issues/17674),
with its [pre-probe scope notice](https://github.com/the-omega-institute/trureturing/issues/17674#issuecomment-6287957803),
restricts (37) to the following complete domain. For every integer $n\ge1$
and positive integers $d_1,\ldots,d_n$, put $N=\sum_i d_i$ and take real
$A_i\in\mathbb R^{N\times d_i}$ with $A_i^\top A_i=I_{d_i}$ such that
the actual concatenation $A=[A_1,\ldots,A_n]$ is square and nonsingular.
Set $P_i=I_N-A_iA_i^\top$, $M=n^{-1}\sum_iP_i$, and
$G=(n!)^{-1}\sum_{\sigma\in\Gamma}P_{\sigma_n}\cdots P_{\sigma_1}$.
The target is $G\preceq M^n$, with all block permutations uniformly
weighted and the number of blocks as the exponent. The six-dimensional
witness below refutes this universal restricted assertion.

The block dimensions and normalization come from source Sections 2.1.1
and 2.2, equations (7)–(8) and (23). Claim 4.1, equations (51a)–(51b),
PDF p.23, assumes this square nonsingular, block-orthonormal structure
and states identities. In the original block coordinates, let $L_\sigma$
have block $(\sigma_i,\sigma_j)$ equal to
$A_{\sigma_i}^\top A_{\sigma_j}$ for $j\le i$ and zero otherwise,
and put $Q_\sigma=L_\sigma^{-1}$ and
$Q=(n!)^{-1}\sum_\sigma Q_\sigma$. Then those identities are

$$
I-AQ_\sigma A^\top=P_{\sigma_n}\cdots P_{\sigma_1},\qquad
I-AQA^\top=G.
$$

They hold for the witness below; Claim 4.1 is not refuted. Lemma 3,
equation (52), and Corollary 4.1, equation (53), prove the weaker bound
$G\preceq M$. The target $G\preceq M^n$ is a strengthening on that
structured domain and a restriction of unrestricted Conjecture 3.1.
The unrestricted conjecture was already refuted by the historical Lean
result above before the block probes. No literal published, still-open
full-block assertion matching #17674 was established by the inspected
pre-probe record. The block result is retained here as exposition, with
no new open-problem-resolution admission or literature-priority claim.

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

The scalar three-coordinate complement-projection argument under Triage remains prose. The complete scalar200 source is now included verbatim in [ProjectionAMGMRefutationScalar200.lean](../D5/S3/Quantum/Matrix/ProjectionAMGMRefutationScalar200.lean), namespace `D5.S3.Quantum.Matrix.ProjectionAMGMRefutationScalar200`. The current Lean 4.35 scoped report covers 130 scalar declarations and 29 unchanged historical-owner declarations, with only `propext`, `Classical.choice` and `Quot.sound`, no `sorryAx`, and source-bound `utility_refutation.is_closed_negation=true` for the closed included `claimScalar` and literal `result : Not claimScalar`. This is current scoped evidence, not whole ordinary acceptance or independent complete admission review. The historical private report at base `1ab17526d4b70881217bc0bbfaebaff8f5e98890` remains inherited evidence only. The historical unrestricted claim/result and frozen identity remain unchanged.

The six-dimensional block counterexample under Triage is a separate prose
proof with an exact integer certificate and a self-contained checker. It
satisfies the square nonsingular concatenation and block orthonormality
conditions of Claim 4.1. A separate checker, independently authored from
the fixed witness using exact rational arithmetic, completed on Mac Studio
on 2026-10-20 with native exit 0. It verified the full block Gram matrices,
positive square-root normalization, $\det K=3500$, the full six-dimensional
projectors, all six reversed words, every (51a) matrix identity and their
(51b) average, and the exact negative form displayed below. This independent
check is distinct from the original researcher's integer checker. Neither
is Lean kernel verification. The historical 29-declaration scoped report
concerns only the unchanged `ProjectionAMGMRefutation` module; it does not
certify this block witness or the scalar-three prose. The block exposition
introduces no new Lean declaration, kernel statement, frozen result or
open-problem-resolution admission.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9). There are no other new public theorems in this module.

Experiment entry: [sun-luo-ye-2020-projection-matrix-amgm](https://github.com/the-omega-institute/trureturing-experiments/tree/38f78a9f7126378ad73d9b496e1c73b6df883bc7/docs/reports/sun-luo-ye-2020-projection-matrix-amgm), script `check.py`. Command: `python3 check.py` from that directory, with NumPy installed. Exit code: 0. Script SHA-256: `5e7643a7ccb84fb77ca498bf6b810c56eb769b401d27b042e55f5e322d3bcfc9`. Final discrepancy count: `bad= 0`.

The exact rational checks enumerate all $n!$ words at $n=3,5,7$: respectively 6, 120 and 5040 words, with quadratic forms $-8/243$, $-50624/232058125$ and $-1838265624/3236831537545039$. Direct matrix word multiplication is also checked at $n=3$. The floating-point checks use the 399 interior points of a 400-step grid for each equiangular family at $n=2,3,4,5$. Negative points at $n=3$ range from $-0.49625$ to $-0.20375$; at $n=5$ from $-0.246875$ to $-0.1125$. There are no negative grid points at $n=2,4$; those finite grid readings do not settle the even-$n$ question. The scalar200 certificate below supplies an exact even-$n$ refutation at $n=200$.

## Triage

| Item | Status and evidence kind | Scope |
| --- | --- | --- |
| Projection witness and $z^\top(M^3-G)z=-8/243$ | Proved, kernel-checked: private `instance_is_projection` and `quadratic_form_value`; public `result` refutes `claim` | $n=N=3$, $z=(1,1,1)$ |
| Odd-$n$ rational family and its closed form | Proved in prose below | Odd $n\ge3$; no uniform Lean theorem is delivered |
| Exact rational family readings | Computed by the experiment entry | $n=3,5,7$; quadratic forms and permutation enumeration listed in Evidence |
| Equiangular failing interval $-1/(n-1)<t<-1/(2n-1)$ for odd $n$ | Proved in prose below | Full-rank equiangular Gram matrices |
| Odd-$n$ transition grid readings | Computed by the experiment entry | $n=3,5$, 399 interior points of a 400-step grid each; agrees with the derived interval on those points |
| No equiangular failure at $n=2,4$ | Computed by the experiment entry | 399 interior grid points at each dimension; this finite grid does not conflict with the separate $n=200$ scalar certificate |
| Scalar coordinate-descent class $P_i=I-a_i a_i^\top$, $n=N=3$ | Proved in prose below | Every unit, linearly independent triple; no sign or conditioning restriction |
| Arbitrary-block coordinate-descent assertion $G\preceq M^n$ | Refuted in prose with exact integer checks below | $n=3$, $N=6$, $d_1=d_2=d_3=2$; actual orthonormal blocks and square nonsingular concatenation |
| All-order scalar basis assertion `claimScalar` | Complete source included with current Lean 4.35 scoped typed-refutes evidence; existing-owner canonical integration, whole acceptance and independent review remain separate | An actual real unit-column basis at $n=N=200$, with the complete $200!$ reversed-permutation average and exponent $200$ |
| Optimal RP-CD convergence rate | Open | The source's intended application is not settled by this refutation |
| Kim–Lee–Yun second-moment comparison | Open | Separate from the first-moment matrix inequality tested here |
| Unrestricted projection inequality for even $n$ | Refuted in the scalar basis subclass at $n=200$ | The smallest failing dimension and a characterization of the remaining even-$n$ cases are open |

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

The constructed rank-one projections in $\mathbb R^n$ have complements of rank $n-1$. Any factorization $I-P_i=A_iA_i^\top$ therefore needs at least $n-1$ columns in each $A_i$. Their concatenation needs at least $n(n-1)>n$ columns for $n\ge3$, so it cannot be square. This prose rank argument explains why the original dimension-three witness is outside the structured block class; it is not kernel-checked here. It does not preclude a higher-dimensional structured perturbation. The scalar200 basis certificate below settles the unrestricted all-order scalar assertion, including an even value of $n$, while the optimal rate, second moment and smallest failing dimension remain open. The construction below separately refutes the arbitrary-block assertion.

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
rank-one matrices. The kernel-checked dimension-three counterexample above
uses rank-one $P_i$ and lies outside this coordinate-descent class. The
complete scalar200 basis certificate below now refutes the unrestricted
all-order scalar inequality, without identifying its smallest failing
dimension. The arbitrary-block assertion has $n\ge1$,
$d_i\ge1$, $N=\sum_i d_i$, $A_i\in\mathbb R^{N\times d_i}$,
$A_i^\top A_i=I_{d_i}$ and square nonsingular concatenation
$[A_1,\ldots,A_n]$; the next construction refutes it. The optimal RP-CD
convergence rate and the separate Kim–Lee–Yun second-moment comparison
remain open.

### The complete scalar200 basis refutation

This is the full finite scalar counterexample included in the existing
owner's Draft source, with current source-bound scoped native evidence and
frozen scalar membership. Whole current acceptance remains incomplete. It
does not add a second resolution marker to this dossier.

Fix $n=200$, $K=10^9$ and $s=\sqrt{K^2+1}$. In the standard orthonormal
basis $e_0,\ldots,e_{199}$, put

$$
a_0=e_1,\qquad a_i=\frac{K e_1+e_{i+1}}s\ (1\le i\le198),\qquad
a_{199}=\frac{e_0-e_1}{\sqrt2},\qquad z=e_0+200e_1.
$$

Every column has squared length one. The identities
$e_1=a_0$, $e_{i+1}=s a_i-Ka_0$, and
$e_0=\sqrt2 a_{199}+a_0$ recover every standard basis vector, so the
200 columns span $\mathbb R^{200}$ and are linearly independent. Set
$P_i=I-a_i a_i^\top$.

For the comparison, retain the last projection $Q=P_{199}$ and replace
the first 199 projections by $P=I-e_1e_1^\top$. In the complete labelled
permutation sum the unique $Q$ position occurs $199!$ times, hence the
full reversed-permutation average is exactly

$$
\frac1{200}\sum_{k=0}^{199}P^{199-k}QP^k
 =\frac{PQ+QP+198PQP}{200}.
$$

No permutation terms are discarded. On $\operatorname{span}(e_0,e_1)$,
the auxiliary mean is $B=\left[\begin{smallmatrix}399&1\\1&1\end{smallmatrix}\right]/400$
and the auxiliary product average is
$\left[\begin{smallmatrix}1/2&1/400\\1/400&0\end{smallmatrix}\right]$;
at $(1,200)$ the latter difference has quadratic form $3/2$.

The Euclidean operator norm of $B$ is at most $401/402$. The exact
binomial estimate
$(402/401)^{196}\ge258507/160801>8/5$ gives
$(401/402)^{196}<5/8$. Direct multiplication gives
$B^2(1,200)=(119601/80000,1/200)$ with squared length below $9/4$.
Using symmetry and $B^{100}=B^{98}B^2$ yields

$$
(1,200)^\top B^{200}(1,200)<45/32,
$$

so the auxiliary AM-GM difference has quadratic form below $-3/32$.

Exactly 198 factors change between the actual and auxiliary families.
Each difference is supported on $\operatorname{span}(e_1,e_{i+1})$ and has
matrix $\left[\begin{smallmatrix}1&-K\\-K&-1\end{smallmatrix}\right]/(K^2+1)$;
its square is the plane identity divided by $K^2+1$, so its norm is at
most $1/s$. Product telescoping for contractions bounds every original
permutation word against its auxiliary word by $198/s$. The mean
difference is at most $198/(200s)$, and telescoping its 200th power gives
$198/s$. Thus the two original differences differ in norm by at most
$396/s<396/K$.

Since $\|z\|^2=40001$, Cauchy--Schwarz gives the strict full-space
certificate

$$
z^\top(M^{200}-G)z
 < -\frac3{32}+\frac{15840396}{1000000000}
 < -\frac1{16}<0.
$$

This is a literal negation of the all-order scalar basis assertion and,
because $n=200$ is even, an even-$n$ counterexample. It preserves the
complete $200!$ average, exponent 200, finite $K$, actual basis and all
full-space error estimates. The source correspondence with a Hessian
square-root convention uses $C=A^\top A$, $U=AC^{-1/2}$, so $U$ is
orthogonal and carries every projection, mean, power and permutation word
by conjugation; $U^\top z$ has the same negative form. This bridge does
not assign a sign to the separate expected-inverse reformulation.

The current included source has literal result type $\operatorname{Not}
\texttt{claimScalar}$, no `sorryAx` in its scoped report, and unchanged SHA-256
`1067ac81d5cb1acca53faf795d906c6d832b55ab7c16c3890f44a6c143ca15ec`.
Its six public authored declarations are `meanProj`, `symProd`, `IsCDFamily`,
`cdProj`, `claimScalar` and the sole theorem `result`. Only the scalar projection
endpoint is formalized; no formal full-block, Hessian or update-transport theorem
is claimed. The smallest failing dimension, optimal RP-CD rate, expected-inverse
and separate second-moment comparisons remain open.

**Existing-owner source interpretation and exact obligation.** Admission basis:
`open-problem-resolution`, original all-$n$ Tier 1 registration
[#17674](https://github.com/the-omega-institute/trureturing/issues/17674),
created 2026-10-16T05:39:52Z. The first $n=3$ test was not a dimension cap.
The named assertion is the structured first-moment comparison called the
original matrix AM-GM in [KLY arXiv:2505.23152v1](../Library/QuadraticForms/kimleeyun2025randompermutations.md),
Appendix E.2, pp.50–51, under Assumption 2.2; SLY Conjecture 3.1/(37),
Claim 4.1/(51a,b) and the Remark after (54) supply the parent identity and
explicit structured application. The current author's existing-owner
interpretation uses that contextual named identity, the original registration
and the inherited bounded exact-claim literature screen jointly. It does not
make the already-refuted unrestricted assertion newly open. No inspected
passage separately labels the precise scalar restriction a still-open
conjecture; KLY's general-quadratic knowledge statement is historical evidence,
and E.2's later future work is about second moments. The ended source review
is quality **approve**, tests **approve**, architecture **comment**, not current
admission. The architecture exact-named-assertion concern remains explicitly
reserved for later independent complete review; no new number, title, slug,
retroactive registration or exhaustive-absence claim is supplied.

The sole typed `OpenProblemResolutionClaim` remains hosted by
`ProjectionAMGMRefutation.result`, with scalar `result` added as a distinct
member through the existing single-owner/multiple-member interface. Its
current frozen scalar declaration and matching theorem-like Scribe Describe
are required; the historical unrestricted binding alone cannot stand for it.
The canonical deposit-uncovered entrance has frozen the scalar module from
its current source-bound scoped report, after canonical Scribe emission and
deposit-header-check. Whole current acceptance and later independent complete
review must establish their respective evidence. No generated member pin is
hand edited. The scalar `result` is a designated `basis=refutes` conclusion,
exempt from four-slot registration; all other new theorems are private live
helpers. Existing public `sixPerms_univ` registration and its other consumers
remain intact.

**Declaration-level author accounting.** This integration uses the external
open-problem-resolution basis and makes no escape-witness claim. The author
records `proof_shape: bind-only` for each theorem below: the supplied chain
combines the pinned norm/projection/dimension/permutation facts, induction and
explicit algebraic and order normalization into the registered counterexample.
These are this author's current declaration labels, not an adjudication or
replacement of the historical architecture UNRESOLVED / quality bind-only /
tests content disagreement or any earlier prefreeze rejection. Each private
helper is retained only on the live proof path to `result`; representative
actual consumers are listed below. Definitions and abbreviations are the
necessary claim vocabulary, witness data and consumed organization, not
additional settlement theorems.

| Theorem/helper | Author proof_shape | Live use |
| --- | --- | --- |
| `std_dot_std` | bind-only | `std_norm` |
| `std_norm` | bind-only | `a200_unit` |
| `nextIndex_eq` | bind-only | `a200_unit` |
| `a200_unit` | bind-only | `a200_isCDFamily` |
| `s_pos` | bind-only | `a200_spans` |
| `a200_spans` | bind-only | `a200_independent` |
| `a200_independent` | bind-only | `a200_isCDFamily` |
| `a200_isCDFamily` | bind-only | `result` |
| `cdProj_projection` | bind-only | `cdProj_contraction` |
| `cdProj_contraction` | bind-only | `P200_contraction` |
| `P200_contraction` | bind-only | `total_operator_error` |
| `a0_unit` | bind-only | `P0_contraction` |
| `P0_contraction` | bind-only | `total_operator_error` |
| `P0_eq` | bind-only | `P0_word` |
| `P0_endpoints` | bind-only | `total_factor_error` |
| `embed2_dot` | bind-only | `auxiliary_negative_form` |
| `embed2_v2` | bind-only | `P_z` |
| `planeProj_projection` | bind-only | `P200_middle_norm` |
| `planeError_square` | bind-only | `P200_middle_norm` |
| `planeError_selfAdjoint` | bind-only | `P200_middle_norm` |
| `s_sq` | bind-only | `P200_middle_error` |
| `P200_middle_error` | bind-only | `P200_middle_norm` |
| `P200_middle_norm` | bind-only | `total_factor_error` |
| `total_factor_error` | bind-only | `total_operator_error` |
| `list_prod_contraction` | bind-only | `list_prod_sub_bound` |
| `list_prod_sub_bound` | bind-only | `pow_sub_bound` |
| `pow_sub_bound` | bind-only | `total_operator_error` |
| `mean_contraction` | bind-only | `total_operator_error` |
| `mean_sub_bound` | bind-only | `total_operator_error` |
| `symProd_sub_bound` | bind-only | `total_operator_error` |
| `sum_perm_eval_zero` | bind-only | `sum_perm_eval` |
| `sum_perm_eval` | bind-only | `sum_perm_inv_eval` |
| `sum_perm_inv_eval` | bind-only | `symProd_P0_position_average` |
| `single_word` | bind-only | `P0_word` |
| `P0_word` | bind-only | `symProd_P0_position_average` |
| `symProd_P0_position_average` | bind-only | `symProd_P0_form` |
| `binomial_three_terms` | bind-only | `rational_power_bound` |
| `rational_power_bound` | bind-only | `B2_power_form_bound` |
| `P_projection` | bind-only | `aux_word_form` |
| `P_embed2` | bind-only | `mean_P0_embed2` |
| `Q_embed2` | bind-only | `mean_P0_embed2` |
| `mean_P0_eq` | bind-only | `mean_P0_embed2` |
| `mean_P0_embed2` | bind-only | `mean_P0_pow_embed2` |
| `mean_P0_pow_embed2` | bind-only | `auxiliary_negative_form` |
| `P_z` | bind-only | `aux_word_form` |
| `aux_word_form` | bind-only | `symProd_P0_form` |
| `symProd_P0_form` | bind-only | `auxiliary_negative_form` |
| `B2_symmetric` | bind-only | `B2_power_form_bound` |
| `B2_norm_bound` | bind-only | `B2_power_form_bound` |
| `B2_squared_vector` | bind-only | `B2_squared_vector_norm` |
| `B2_squared_vector_norm` | bind-only | `B2_power_form_bound` |
| `dot_self_eq_l2_sq` | bind-only | `B2_power_form_bound` |
| `B2_power_form_bound` | bind-only | `auxiliary_negative_form` |
| `auxiliary_negative_form` | bind-only | `strict_negative_certificate` |
| `total_operator_error` | bind-only | `strict_negative_certificate` |
| `quadratic_form_error` | bind-only | `strict_negative_certificate` |
| `z_squared_norm` | bind-only | `strict_negative_certificate` |
| `s_gt_K` | bind-only | `strict_negative_certificate` |
| `strict_negative_certificate` | bind-only | `P200_not_posSemidef` |
| `P200_not_posSemidef` | bind-only | `result` |
| `result` | bind-only | designated refutation, registration-exempt |

### Three blocks of two columns: an exact counterexample, proved in prose

The block assertion fails already for $n=3$, $N=6$ and
$d_1=d_2=d_3=2$. The construction here is repo-derived; literature
priority is not established. The source hypotheses are those of
Sun–Luo–Ye, arXiv:1503.06387v3, Claim 4.1, PDF p.23. The tested
comparison is the restriction of Conjecture 3.1, equation (37), PDF p.20,
to that structured domain, as specified above. This is a readable argument
and exact computational certificate, not a new kernel-checked result.

Let $e_0,e_1,e_2,f_0,f_1,f_2$ be the standard orthonormal basis of
$\mathbb R^6$, in that order. Indices on $e_i,f_i$ are taken modulo
three. Define

$$
x_i=5(e_i+e_{i+1})+f_i,\qquad
y_i=5(e_i-e_{i+1}+2e_{i+2})-f_{i+1},\qquad
A_i=\begin{bmatrix}x_i/\sqrt{51}&y_i/\sqrt{151}\end{bmatrix}.
$$

The index set $\{0,1,2\}$ merely relabels the source's three blocks.
For every $i$, $x_i^\top x_i=51$, $y_i^\top y_i=151$ and
$x_i^\top y_i=0$. Therefore $A_i$ is a real $6\times2$ matrix and
$A_i^\top A_i=I_2$ exactly. There are six columns in all, so the
concatenation $A=[A_0,A_1,A_2]$ is square.

To check actual nonsingularity, let
$K=[x_0,y_0,x_1,y_1,x_2,y_2]$, and let the cyclic shift $S$ on
$\mathbb R^3$ send $e_i$ to $e_{i+1}$. Reordering its columns to
$[x_0,x_1,x_2,y_0,y_1,y_2]$ gives

$$
K'=\begin{pmatrix}5(I+S)&5(I-S+2S^2)\\I&-S\end{pmatrix}.
$$

Interchanging the two groups of three rows and then taking the Schur
complement of $I$ yields
$\det K'=-5^3\det(I+3S^2)=-3500$, since
$\det(I+3S^2)=1+3^3=28$. The column reordering has odd sign, so

$$
\det K=3500,\qquad
\det A=\frac{3500}{(51\cdot151)^{3/2}}>0.
$$

Thus this example is inside the nonsingular domain, with no limiting
invertibility assumption.

Now use the original variables, without changing projection complements
or the number of updates:

$$
P_i=I_6-A_iA_i^\top
 =I_6-\frac{x_ix_i^\top}{51}-\frac{y_iy_i^\top}{151},\quad
M=\frac{P_0+P_1+P_2}{3},\quad
G=\frac16\sum_{\sigma\in S_3}P_{\sigma(2)}P_{\sigma(1)}P_{\sigma(0)}.
$$

The exponent is $n=3$, rather than the ambient dimension six. Each
$P_i$ is a symmetric idempotent, directly from the checked block
orthonormality. Put $z=e_0+e_1+e_2$, $L=51\cdot151=7701$,
$R_i=LP_i$ and $T=R_0+R_1+R_2$. The first integer matrix is

$$
R_0=\begin{pmatrix}
2651&-2500&-2550&-755&255&0\\
-2500&2651&2550&-755&-255&0\\
-2550&2550&2601&0&510&0\\
-755&-755&0&7550&0&0\\
255&-255&510&0&7650&0\\
0&0&0&0&0&7701
\end{pmatrix}.
$$

Writing $C=\operatorname{diag}(S,S)$, the other two are
$R_i=C^iR_0(C^\top)^i$. Since $Cz=z$, cyclic relabeling leaves
every word's quadratic form unchanged. Transposition reverses a word
and also leaves its quadratic form unchanged. Cyclic relabeling and
reversal cover all six permutations, so it suffices to evaluate
$z^\top R_2R_1R_0z$. This proves the word correspondence for the full
uniform average, rather than replacing it by a cyclic average.

On the subspace spanned by $z$ and $f_0+f_1+f_2$, the matrix of $T$ is

$$
B=\begin{pmatrix}2903&-1000\\-1000&22901\end{pmatrix}.
$$

The two basis vectors are orthogonal and both have squared norm three.
Consequently direct multiplication gives

$$
\begin{aligned}
z^\top T^3z
 &=3\bigl(2903^3+2\cdot2903\cdot1000^2+22901\cdot1000^2\bigr)
 =159515304981,\\
R_0z&=(-2399,2701,2601,-1510,510,0)^\top,\\
R_2z&=(2701,2601,-2399,510,0,-1510)^\top,\\
z^\top R_2R_1R_0z&=(R_2z)^\top R_1(R_0z)=10214053403.
\end{aligned}
$$

It follows, with all six words counted exactly once, that

$$
\begin{aligned}
z^\top M^3z&=\frac{159515304981}{27L^3},\\
z^\top Gz&=\frac{10214053403}{L^3},\\
z^\top(M^3-G)z
 &=\frac{159515304981-27\cdot10214053403}{27L^3}
 =-\frac{38754712300}{4110398037909}<0.
\end{aligned}
$$

The mean cube is symmetric, and the transpose pairs in the full
permutation average make $G$ symmetric. This strictly negative form at
the nonzero vector $z$ therefore refutes positive semidefiniteness of
$M^3-G$ in the original block domain.

**Reproducible exact check (computed).** The following standalone
Python 3 listing uses only integers and the standard library. It checks
the dimensions, block inner products, the determinant by all 720
Leibniz terms, idempotence after clearing denominators, and the original
six reversed words. Command: save the listing as `check_block.py` and
run `python3 check_block.py`. The Mac Studio run exited 0 and printed
`exact block counterexample: PASS`. This is an exact computation,
not a Lean kernel or axiom-closure report.

```python
from itertools import permutations
X = [[5,5,0,1,0,0], [0,5,5,0,1,0], [5,0,5,0,0,1]]
Y = [[5,-5,10,0,-1,0], [10,5,-5,0,0,-1], [-5,10,5,-1,0,0]]
L, n = 7701, 6
z = [1,1,1,0,0,0]
def mul(a, b):
    return [[sum(a[i][k]*b[k][j] for k in range(n))
             for j in range(n)] for i in range(n)]
def form(a):
    return sum(z[i]*a[i][j]*z[j] for i in range(n) for j in range(n))
for x, y in zip(X, Y):
    assert len(x) == len(y) == n
    assert sum(t*t for t in x) == 51
    assert sum(t*t for t in y) == 151
    assert sum(a*b for a,b in zip(x,y)) == 0
K = [[v[r] for pair in zip(X,Y) for v in pair] for r in range(n)]
det = 0
for p in permutations(range(n)):
    v = (-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))
    for i in range(n):
        v *= K[i][p[i]]
    det += v
assert det == 3500
R = [[[L*int(i==j)-151*x[i]*x[j]-51*y[i]*y[j]
       for j in range(n)] for i in range(n)] for x,y in zip(X,Y)]
for r in R:
    assert r == [list(row) for row in zip(*r)]
    assert mul(r,r) == [[L*v for v in row] for row in r]
T = [[sum(r[i][j] for r in R) for j in range(n)] for i in range(n)]
assert form(mul(mul(T,T),T)) == 159515304981
words = [form(mul(mul(R[p[2]],R[p[1]]),R[p[0]]))
         for p in permutations(range(3))]
assert words == [10214053403]*6
assert 159515304981-27*10214053403 == -3*38754712300
assert 27*L**3 == 3*4110398037909
print("exact block counterexample: PASS")
```

**Mechanism and limits (proved in prose).** Replace the coefficient five
in $x_i,y_i$ by any positive real $k$, and normalize by
$\sqrt{2k^2+1}$ and $\sqrt{6k^2+1}$. The same determinant calculation
gives $\det K(k)=28k^3$, so every such concatenation is nonsingular.
As $k$ tends to infinity, the top three coordinates of the removed
two-dimensional spaces approach the orthogonal complements of
$v_i=2e_i-(e_0+e_1+e_2)$. Hence the actual $P_i(k)$ tend to
$\operatorname{diag}(v_iv_i^\top/3,I_3)$. Restricting every limiting word
to the top three coordinates gives exactly the earlier rank-one word;
the mean and its cube restrict in the same way. This explains why the
negative obstruction can survive enlargement. The finite $k=5$
calculation above supplies actual nonsingularity and a strict sign,
independently of a continuity-only existence argument.

The square-concatenation condition thus does not rescue the general
block AM-GM comparison. The example has two columns per block and does
not contradict the scalar-three positive result. Splitting its blocks
into six scalar updates changes the average, the words and the exponent;
that operation alone gives no scalar conclusion. The separate scalar200
basis certificate above refutes the unrestricted all-order scalar claim.
Failure of this sufficient matrix inequality also does not refute the
RP-CD rate conjecture or the separate second-moment comparison. The
weaker literature bound $G\preceq M$ remains distinct.

**Admission boundary.** The finite certificate consists of exact
substitution, matrix multiplication and arithmetic normalization. It is
reported as bind-only, with no established open-problem-resolution
exception for the restricted block assertion and no new Lean module.
The argument and checker are retained as existing-dossier exposition;
the historical unrestricted kernel result and scalar-three admission
disposition are unchanged.

## ASSUMED-UNVERIFIED

The literature screen's completeness is unverified. In particular, the body of Luenberger–Ye, *Linear and Nonlinear Programming*, fifth edition, Chapter 14, DOI 10.1007/978-3-030-85450-8_14, was access-blocked in the recorded source check. Absence of a settlement in the searched sources is not a proof that none exists elsewhere. The family, transition, scalar-three and six-dimensional block derivations above are prose proofs, not new kernel-checked results. The block refutation has exact integer computational evidence; literature priority is not established. The complete scalar200 source is now included with current scoped Lean 4.35 evidence; its canonical member binding and whole-normal evidence must be assessed at the exact candidate head, separately from source-only approvals and historical native evidence. The scalar d_i=1 source specialization is direct; the ordinary Hessian correspondence uses the conventional symmetric positive root, which KLY does not separately specify. No kernel transport theorem is claimed. The optimal RP-CD rate, separate second-moment comparison and smallest failing dimension remain open. Numerical grid readings cover only their stated finite samples.

The inherited scalar source screen used 37 retrievals and incomplete 41/33-row
Semantic Scholar citation screens (KLY itself was absent). Records
2308.00899, 1512.04680 and 1508.00193 remain metadata/abstract screens. Failed
Google/DuckDuckGo/Bing access provides no absence evidence. The disabled
`iffalse` AM-GM material in Lee–Wright is excluded from published evidence.
The inspected follow-up norm, average-of-norms, near-identity, spectral-rate
and special-Hessian domains do not settle the exact first-moment comparison;
recent preprint proofs were not independently validated. SLY v1 was not
inspected and older versions do not inherit v3 labels. The journal text,
numbering and equivalence and KLY conference equality remain unverified.
The current dossier's scalar exposition is the same candidate work, not an
independently earlier literature settlement. All earlier prefreeze rejects,
architecture UNRESOLVED / quality bind-only / tests content, comment-only
rounds, exposition-only approvals and the invalid-Pro round remain historical;
no vote, spent cap or allocation is changed. Current scoped truth and typed
negation do not by themselves settle named-problem fidelity or whole delivery.
