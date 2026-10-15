---
bibkey: corvalan2023interpolation
authors: Álvaro Corvalán
year: 2023
title: Interpolation and Extrapolation Statements equivalent to the Riemann Hypothesis
doi: null
url: https://arxiv.org/abs/2312.00211v3
claim: "The preprint proposes fixed-weight extrapolation closure criteria. Its printed dictionary and quantifier rewrites require calibration; the weighted norm construction admits the existing actual FIB target transport, but no required approximation estimate is supplied."
strata_touched: []
license: citation-only
triage: anchor
---

# Fixed-weight approximation and the actual FIB target

The inspected primary is [arXiv:2312.00211v3](https://arxiv.org/abs/2312.00211v3),
revised 1 June 2026. Its [PDF](https://arxiv.org/pdf/2312.00211v3) has
SHA256 `28ef4a091c67287cea59a93f9ef447450978257c3b0b6182860ce8bbac08f05e`;
the [author-source archive](https://arxiv.org/src/2312.00211v3) has SHA256
`f756d275cf3a72a42dabe55898ba6f5794e12ae904cbe9d8579df6d81341f71d`.
The selected definitions, Criterion 21, Theorem 24 and their supporting
arguments were read. This is a scoped source-applicability analysis and
paper application, without an independent whole-paper proof audit,
originality claim or Lean certification. The printed criterion is not
adopted without the normalization qualifications below.

## What the proposed sufficient condition actually asks for

Let

$$
E_\theta=(L^1(0,1),L^2(0,1))_{\theta,\infty;K},\qquad
\|f\|_{E_\theta}=\sup_{t>0}t^{-\theta}K(t,f;L^1,L^2),\qquad
p(\theta)=\frac2{2-\theta}.
$$

[Criterion 21](https://arxiv.org/html/2312.00211v3#Thmtheorem21),
author TeX label `N-B-with-extrapol`, proposes a positive fixed weight
$M$, tempered at $\theta=1$ and $O(1)$ there, such that

$$
\inf_{f\in\Phi}\sup_{0<\theta<1}
M(\theta)\|\chi-f\|_{E_\theta}=0,
\qquad \chi=\mathbf1_{(0,1)}.
\tag{I1}
$$

[Theorem 24](https://arxiv.org/html/2312.00211v3#Thmtheorem24),
label `strong Nyman-Beurling-Milman equivalence`, repeats the closure
formulation. The weight is chosen once. For each error tolerance, one
approximant must serve all interpolation parameters in the supremum;
neither the weight nor the approximant may be chosen separately after
observing each parameter. The paper supplies no coefficients or
truncation-dependent error bound attaining this closure.

The cited Jawerth–Milman input is
[Theorem 20](https://arxiv.org/html/2312.00211v3#Thmtheorem20),
label `M_delta`. It assumes a mutually closed Banach couple, tempered
weight and exact interpolation functors with characteristic function
$t^\theta$. The paper credits Milman's *Extrapolation and Optimal
Decompositions with Applications to Analysis*, Theorem 21, p.44.
This standard interpolation result is reused as a literature input;
its upstream proof is not reproved or independently certified here.

### Calibration before using the printed criterion

The following distinctions concern the actual displayed source formulas.
They do not establish that no corrected weighted criterion can hold.

- The source writes its dictionary constraint as
  $\sum_a c_a\rho(1/a)=0$ with $a\ge1$, where
  $\rho(u)=u-\lfloor u\rfloor$. At $a=1$ this uses $\rho(1)=0$.
  Consequently the printed dictionary admits $\rho_1$ alone and excludes
  an individual standard balanced probe
  $\rho_n-\rho_1/n$ for $n\ge2$. It is not literally the standard
  constraint $\sum_a c_a/a=0$. The definitions in the introduction,
  Theorem 4 and the later remarks retain this endpoint issue. The
  [existing classical criterion](baezduarte2002nyman.md) and the
  balanced natural generators in the
  [coefficient-functional application](baezduarte2000natural.md#published-coefficient-functionals-and-restricted-dictionaries)
  remain the separate dictionary suppliers.
- Immediately after its norm-closure statement, Criterion 21 changes
  $\inf_f\sup_\theta$ to $\sup_\theta\inf_f$. The same interchange
  recurs later. These expressions are not generally equal; (I1) is
  the uniform closure condition used here.
- In the reverse proof the bound $M(\theta)\le k$ does not justify
  the printed lower comparison by $k\|\chi-f\|$. At a fixed
  $\theta$ the valid consequence of a small weighted norm is division
  by the positive fixed value $M(\theta)$.
- Conditions only near $\theta=1$ do not control an arbitrary weight
  on the rest of $(0,1)$. A full-interval supremum needs a controlled
  extension there, or an explicitly restricted endpoint interval.

In particular, no RH equivalence for the source's literal printed
$\Phi$ is imported into the project. The useful object retained below
is its weighted norm, applied to an independently specified dictionary.

## A controlled weight and an independently specified dictionary

For definiteness take a fixed $a>0$ and

$$
M_a(\theta)=(1-\theta)^a,\qquad
\|f\|_{X_a}=\sup_{0<\theta<1}
(1-\theta)^a\|f\|_{E_\theta}.
\tag{I2}
$$

This weight is positive and bounded throughout the interval, and
$M_a((1+\theta)/2)=2^{-a}M_a(\theta)$ supplies the endpoint tempering.
It is an available choice, not a weight forced by the five FIB modes.
No equivalence with an unweighted $L^2$ norm is assumed.

On $(0,1)$ use the standard balanced natural span

$$
b_n(x)=\left\{\frac1{nx}\right\}
-\frac1n\left\{\frac1x\right\},\qquad
\mathcal V=\operatorname{span}\{b_n:n\ge2\}.
\tag{I3}
$$

Extend each function by zero outside $(0,1)$. The same formula for
$b_n$ on the half-line is already zero for $x>1$.
Write $W_a=\overline{\mathcal V}^{X_a}$; this closure is defined without
asserting that it contains $\chi$ or the FIB target. Its definition is
not a new RH criterion.

## The existing Binet transport acts in this norm

Reuse [FIB §391](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md),
including its actual coefficients and absolute inverse budget:

$$
q=\varphi^{-2},\qquad \beta_d=\log(1-(-q)^d),\qquad
\gamma*\beta=\beta*\gamma=\mathbf1,\qquad
\sum_d|\gamma_d|\le\frac1{\beta_1-T},\quad
T=\sum_{d\ge2}|\beta_d|<\beta_1.
$$

Here $\beta_d$ is a coefficient sequence, distinct from the ATOM
$\beta=\rho(\alpha)$. For the zero-extended convention define

$$
U_df(x)=\mathbf1_{(0,1/d)}(x)f(dx),\qquad
\mathscr B_\beta=\sum_{d\ge1}\beta_dU_d,\qquad
\mathscr B_\gamma=\sum_{d\ge1}\gamma_dU_d,\qquad
\Phi_\beta=\mathscr B_\beta\chi.
\tag{I4}
$$

These are the restrictions of the same support-preserving half-line
operators. They are not ordinary unrestricted unit-interval dilations.
The endpoint bounds are $\|U_d\|_{L^1}=d^{-1}$ and
$\|U_d\|_{L^2}=d^{-1/2}$. Applying the same operator to each term in
the defining $K$-functional decomposition therefore gives

$$
\|U_df\|_{X_a}\le d^{-1/2}\|f\|_{X_a}.
$$

Thus the existing absolute coefficient and inverse budgets give, in
the new specified norm as well,

$$
\|\mathscr B_\beta\|_{X_a\to X_a}\le B_{1/2},\qquad
\|\mathscr B_\gamma\|_{X_a\to X_a}\le G_{1/2},\qquad
\mathscr B_\gamma\mathscr B_\beta
=\mathscr B_\beta\mathscr B_\gamma=I,
\tag{I5}
$$

where $B_{1/2}=\sum_d|\beta_d|d^{-1/2}$ and
$G_{1/2}=\sum_d|\gamma_d|d^{-1/2}\le(\beta_1-T)^{-1}$.
No inverse theorem is reproved: this is the existing Dirichlet-inverse
transport applied with the common endpoint bound.

The dictionary is compatible with the same operation:

$$
U_db_n=b_{dn}-\frac1n b_d,\qquad b_1=0.
\tag{I6}
$$

Consequently each finite coefficient truncation of either transport
maps $\mathcal V$ into $\mathcal V$. Operator-norm convergence then
preserves $W_a$, and the inverse gives
$\mathscr B_\beta W_a=W_a$. In particular the actual-target error
budgets satisfy

$$
\frac{\operatorname{dist}_{X_a}(\chi,W_a)}{G_{1/2}}
\le\operatorname{dist}_{X_a}(\Phi_\beta,W_a)
\le B_{1/2}\operatorname{dist}_{X_a}(\chi,W_a).
\tag{I7}
$$

This transports both the target and the permissible closed span. It
provides no positive value, zero value or rate for either distance.
The earlier $L^2$ support classification is not silently transferred
to this different norm.

### Finite transport tails can be paid independently

For a finite balanced approximant $v\in\mathcal V$ and an integer $D\ge1$, use
$\mathscr B_{\beta,D}=\sum_{d\le D}\beta_dU_d$. The already supplied
bound $|\beta_d|\le q^d/(1-q)$ gives

$$
\|\mathscr B_\beta v-\mathscr B_{\beta,D}v\|_{X_a}
\le\frac{q^{D+1}}{(1-q)^2\sqrt{D+1}}\|v\|_{X_a}.
\tag{I8}
$$

Hence an actual finite approximant to the transported target can be
formed with the explicit error budget

$$
\|\Phi_\beta-\mathscr B_{\beta,D}v\|_{X_a}
\le B_{1/2}\|\chi-v\|_{X_a}
+\frac{q^{D+1}}{(1-q)^2\sqrt{D+1}}\|v\|_{X_a}.
\tag{I9}
$$

By (I6) the output still has finite balanced natural support. If the
input indices are at most $N$, the output indices are at most $DN$.
The exponentially small second term is a transport cost; the first
term is the unproved approximation estimate. A small transport tail
alone cannot make that first term small. Nor does (I9) assert that the
transported finite coefficients are the fixed natural prefixes
$e_n=(\mu*\beta)_n$ considered in §391.

## Remaining consumer

The source opens a norm choice for a future approximation argument.
Using it requires an actual balanced family $v_j$, one fixed weight,
and a proved common-parameter bound
$\|\chi-v_j\|_{X_a}\to0$, or the corresponding actual-target bound.
The displayed transport supplies neither. Any RH conclusion must
also use the classical criterion with its correct dictionary and the
required embeddings; it does not follow by importing the paper's
literal printed definition.

The five modes encode all natural indices and can organize the
finite support in (I6). Their legal seams and interval-length
conservation do not estimate this weighted approximation error. The
Robin same-integer signed integral remains unpaid. This application
reuses standard interpolation and the existing Binet inverse; it is
not a new supplier theorem, a proof of RH or a claim that the
weighted route outperforms existing approximation methods.
