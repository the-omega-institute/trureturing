---
bibkey: baezduarte2000natural
authors: Luis Báez-Duarte
year: 2000
title: Arithmetical Aspects of Beurling's Real Variable Reformulation of the Riemann Hypothesis
doi: null
url: https://arxiv.org/abs/math/0011254v1
claim: "Proposition 4.4 excludes full-sequence L2 convergence of the unbalanced natural Möbius prefixes on the half-line. It does not exclude every subsequence or freely chosen coefficients in the Nyman–Beurling criterion."
strata_touched: []
license: citation-only
triage: anchor
---

# The natural-prefix obstruction and its exact scope

The pinned source is [arXiv:math/0011254v1](https://arxiv.org/abs/math/0011254v1),
submitted 2000-11-29. The [21-page PDF](https://arxiv.org/pdf/math/0011254v1)
has SHA256 `951ecc56eaae5b80eb8128ab4f98b5184d06ed97da608a130d65940daea8e94c`.
The inspected [author TeX](https://arxiv.org/src/math/0011254v1)
has SHA256 `32453b451c900c7c557fc7da5eb8b93987d9d2addca4d31d293b9f844e84801d`.
The selected definitions, Proposition 4.4 and its proof, and the subsequent
scope distinctions were read. This is source reuse, not a new proof or a
Lean verification of the paper.

## Space, coefficients and cutoff

Section 1 works in $L^p((0,\infty),dx)$, defines
$\chi=\mathbf1_{(0,1]}$, and uses the fractional part $\rho(t)=t-\lfloor t\rfloor$.
Its dilation is $K_af(x)=f(ax)$. Equations (1.4) and (1.18) define
$g(n)=\sum_{k\le n}\mu(k)/k$ and the unbalanced natural prefix

$$
S_n(x)=\sum_{k=1}^n\mu(k)\rho\!\left(\frac1{kx}\right).
$$

Thus the approximation residual has sign $\chi+S_n$; it is not
$\chi-S_n$. The coefficient cutoff passes through all positive integers
$n$, and the half-line norm retains the region $x>1$.

Proposition 4.4, PDF p. 17, states that if $\zeta$ has a zero of real
part $1/p$, then $S_n$ and the associated balanced sequence $V_n$ do
not converge in $L^p$. In particular they do not converge in $L^2$.
This last conclusion uses the known existence of zeros on the critical
line, not RH. Its proof retains the tail $x>1/m$; equation (4.10)
under the assumed convergence yields

$$
\|\chi+S_m\|_p^p\ge
\frac{m^{p-1}}{p-1}|g(m)|^p.
$$

The paper combines that implication with the non-little-oh statement
(4.9). Proposition 4.5, PDF p. 18, also gives (4.11)–(4.12), including
$\|\chi+S_n\|_2\ge\sqrt n\,|g(n)|$. These are quoted source results;
no lower-bound scan is required to reuse them.

## What this obstruction does not say

Remarks 4.6 and the paragraph following Proposition 4.5 explicitly
discuss selected zero-crossing subsequences as unresolved possibilities
in this source. Full-sequence nonconvergence does not by itself exclude
all subsequences. A Fibonacci cutoff schedule would need a separate
argument; it cannot be rejected just by changing the index name in
Proposition 4.4.

Proposition 4.6, PDF p. 18, treats the distinct natural sequences $B_n$
and $F_n$. Proposition 4.7, PDF p. 19, treats fixed-coefficient series
in the balanced family $\mathcal C^{nat}$ on the unit interval. Neither
is silently substituted for Proposition 4.4 on the half-line.

The closure criterion permits coefficients depending on the cutoff.
Its natural-dilation form is already sourced in the
[2002 criterion note](baezduarte2002nyman.md). The proof in that source
uses damped coefficients and an order of limits; its Introduction also
discusses the logarithmically mollified Selberg approximation. Those
are different approximation problems from the unweighted $S_n$.
Pointwise or unit-interval $L^1$ convergence of natural prefixes supplies
neither half-line $L^2$ convergence nor an unconditional mollifier estimate.

## Interface with actual FIB coefficients

[FIB §391](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
uses the actual coefficients $e=\mu*\beta$ of §§384–386. The target
transported with those coefficients is $\Phi_\beta=\sum_d\beta_dK_d\chi$,
not the unchanged $\chi$. The prefix identity retains every $d>n$
target term. The dominant-head estimate already in §384 and the existing
Dirichlet-inverse budget supply an absolutely summable inverse.

That section's additional interface is a paper application of standard
dilation, convolution and convergence facts, not a new Nyman–Beurling
theorem or a claim of priority. The literature obstruction is used
directly. It does not settle actual FIB critical growth, a signed Robin
remainder or RH.

## Published coefficient functionals and restricted dictionaries

In $\mathscr H=L^2((0,\infty),dx)$, write
$\rho_n(x)=\{1/(nx)\}$ for positive integer $n$.
For approximants with freely varying finite coefficients, use the
continuous arithmetic functionals already supplied by Michel Balazard,
[*An arithmetical function related to Baez-Duarte's criterion for the
Riemann hypothesis*, arXiv:1812.04309v1](https://arxiv.org/pdf/1812.04309v1),
Proposition 4, printed p.5, with the definitions on pp.1--2.
The source works in $\mathcal K=L^2((0,\infty),t^{-2}dt)$ and its closed
arithmetic subspace $D$. The unitary change of variables
$Vf(t)=f(1/t)$ sends $\rho_n$ to $\{t/n\}$ and $\chi$ to
$\eta_1=\mathbf1_{[1,\infty)}$. Its functionals $w(m;\cdot)$ have
bounded pullbacks $\ell_m$ to $V^{-1}D$, with

$$
\ell_m(\rho_n)=-\mathbf1_{m=n},\qquad
\ell_m(\chi)=\mu(m),\qquad
\ell_m(K_d\chi)=\mathbf1_{d\mid m}\mu(m/d).
\tag{C1}
$$

For the last normalization, $VK_d\chi=\eta_d=\mathbf1_{[d,\infty)}$
has arithmetic jump function $u(j;\eta_d)=\mathbf1_{j=d}$;
apply the source's definition $w=\mu*u$. Thus $p_j=\sum_n a_{j,n}\rho_n
\to f$ in the half-line norm forces $a_{j,m}\to-\ell_m(f)$ for each
fixed $m$. There is no fixed-coefficient or nested-support assumption.
This reuses the published continuous functionals, without repeating
triangular coefficient recovery or constructing a new dual system.

For comparison, the untransported target has the existing classification

$$
\chi\in W_A\quad\Longleftrightarrow\quad
\mathrm{RH}\ \text{and}\ \{m:\mu(m)\ne0\}\subseteq A,
\qquad
W_A=\overline{\operatorname{span}}\{\rho_n:n\in A\},
\quad A\subseteq\mathbb N_{>0}.
\tag{C2}
$$

The necessary support follows from (C1); membership in the complete
natural closure implies RH by the
[existing natural-dilation criterion](baezduarte2002nyman.md).
The squarefree sufficient dictionary is already explicit in Bhaskar
Bagchi, [arXiv:math/0607733v1](https://arxiv.org/pdf/math/0607733v1),
Remarks 4 and 8, printed pp.142 and 145. His balanced generators are
$\rho_l-\rho_1/l$ on $(0,1)$ and vanish on $x>1$, so squarefree $l$
and the squarefree index $1$ suffice in this half-line dictionary.
Equation (C2) is a direct combination of those known results, without
a new criterion or priority claim.

## Apply the functionals to the actual transported FIB target

Retain the actual $\beta$, $e=\mu*\beta$ and $\Phi_\beta$ above.
Each $K_d\chi$ lies in the closed subspace $V^{-1}D$.
The operator-norm convergence in FIB equation (391.4) and continuity of (C1) give

$$
\ell_m(\Phi_\beta)
=\sum_{d\mid m}\beta_d\mu(m/d)=e_m.
\tag{C3}
$$

The same FIB volume's existing (240.a), using the strict bounds in
§382.3 and the unit correction, already gives $e_m\ne0$ for every
positive integer $m$. Reuse that full-support result directly.
Consequently, for this actual target,

$$
\boxed{\quad
\Phi_\beta\in W_A
\quad\Longleftrightarrow\quad
\mathrm{RH}\ \text{and}\ A=\mathbb N_{>0}.
\quad}
\tag{C4}
$$

Indeed, if $\Phi_\beta\in W_A$, coefficient continuity forces every
index into $A$. The full natural closed space $W_{\mathbb N_{>0}}$
is preserved by each $K_d$, because $K_d\rho_n=\rho_{dn}$.
It is therefore preserved by the existing operator-norm sums
$\mathscr B_\beta$ and $\mathscr B_\gamma$. Applying the inverse gives
$\chi=\mathscr B_\gamma\Phi_\beta\in W_{\mathbb N_{>0}}$, hence RH.
Conversely, RH and $A=\mathbb N_{>0}$ give $\chi\in W_A$, and applying
$\mathscr B_\beta$ gives $\Phi_\beta\in W_A$.

There is also an immediate quantitative separation when $m\notin A$:

$$
\operatorname{dist}(\Phi_\beta,W_A)
\ge\frac{|e_m|}{\|\ell_m\|}>0.
\tag{C5}
$$

The functional norm is taken on $V^{-1}D$; it is finite by Proposition 4
and positive by $\ell_m(\rho_m)=-1$. Thus squarefree-only pruning,
although sufficient for $\chi$ under RH, fails for the actual target.
Invertibility of the complete transport does not preserve arbitrary
restricted subspaces. No new norm computation or finite Gram scan is
needed for this application.

The five occupancy patterns still encode every natural index. Equations
(C3)--(C5) constrain schemes that permanently omit a generator; they do
not exclude finite approximants whose available indices exhaust all
naturals, changing coefficients, or compressed representations retaining
the necessary probes. The full-prefix divergence above remains about
its particular coefficients. These applications specify a support
obligation for the actual FIB target, supply no unconditional
approximation rate or signed Robin estimate, and have not been Lean
compiled. The cited source statements and parameter correspondence were
inspected; no independent recertification of their full proofs or
originality claim is made.
