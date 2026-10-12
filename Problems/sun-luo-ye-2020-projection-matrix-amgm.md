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

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9). There are no other new public theorems in this module.

Experiment entry: [sun-luo-ye-2020-projection-matrix-amgm](https://github.com/the-omega-institute/trureturing-experiments/tree/38f78a9f7126378ad73d9b496e1c73b6df883bc7/docs/reports/sun-luo-ye-2020-projection-matrix-amgm), script `check.py`. Command: `python3 check.py` from that directory, with NumPy installed. Exit code: 0. Script SHA-256: `5e7643a7ccb84fb77ca498bf6b810c56eb769b401d27b042e55f5e322d3bcfc9`. Final discrepancy count: `bad= 0`.

The exact rational checks enumerate all $n!$ words at $n=3,5,7$: respectively 6, 120 and 5040 words, with quadratic forms $-8/243$, $-50624/232058125$ and $-1838265624/3236831537545039$. Direct matrix word multiplication is also checked at $n=3$. The floating-point checks use 400 grid points for each equiangular family at $n=2,3,4,5$. Negative points at $n=3$ range from $-0.49625$ to $-0.20375$; at $n=5$ from $-0.246875$ to $-0.1125$. There are no negative grid points at $n=2,4$. These grid readings do not establish a uniform continuum or even-$n$ result.

## Triage

| Item | Status and evidence kind | Scope |
| --- | --- | --- |
| Projection witness and $z^\top(M^3-G)z=-8/243$ | Proved, kernel-checked: private `instance_is_projection` and `quadratic_form_value`; public `result` refutes `claim` | $n=N=3$, $z=(1,1,1)$ |
| Odd-$n$ rational family and its closed form | Proved in prose below | Odd $n\ge3$; no uniform Lean theorem is delivered |
| Exact rational family readings | Computed by the experiment entry | $n=3,5,7$; quadratic forms and permutation enumeration listed in Evidence |
| Equiangular failing interval $-1/(n-1)<t<-1/(2n-1)$ for odd $n$ | Proved in prose below | Full-rank equiangular Gram matrices |
| Odd-$n$ transition grid readings | Computed by the experiment entry | $n=3,5$, 400 points each; agrees with the derived interval on those points |
| No equiangular failure at $n=2,4$ | Computed by the experiment entry | 400 grid points at each dimension; unrestricted even-$n$ inequality remains open |
| Structured coordinate-descent class $P_i=I-A_iA_i^\top$ with square invertible $[A_1,\dots,A_n]$ | Open | The rank-one family does not supply a witness in this restricted class |
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

The constructed rank-one projections in $\mathbb R^n$ have complements of rank $n-1$. Any factorization $I-P_i=A_iA_i^\top$ therefore needs at least $n-1$ columns in each $A_i$. Their concatenation needs at least $n(n-1)>n$ columns for $n\ge3$, so it cannot be square. This prose rank argument explains the scope boundary; it is not kernel-checked here. The structured inequality, its rate question and the unrestricted even-$n$ case remain open.

## ASSUMED-UNVERIFIED

The literature screen's completeness is unverified. In particular, the body of Luenberger–Ye, *Linear and Nonlinear Programming*, fifth edition, Chapter 14, DOI 10.1007/978-3-030-85450-8_14, was access-blocked in the recorded source check. Absence of a settlement in the searched sources is not a proof that none exists elsewhere. The family and transition derivations above are prose proofs, not uniform Lean formalizations. Numerical grid readings cover only their stated finite samples.
