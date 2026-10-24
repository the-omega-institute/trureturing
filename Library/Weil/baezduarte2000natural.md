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
The selected definitions, the Order Lemma in §2, the unitary formulas
in §4, Proposition 4.4 and its proof, and the subsequent scope distinctions
were read. This is source reuse, not a new proof or a
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

## The same published tools exclude the fixed complete Abel net

The Order Lemma in §2, original TeX label `orderlemma`, and the unitary
operator in §4, labels `Uinvariant`, `Urho1` and `Uchi`, also give an
application to a different approximation family. The following argument
uses those existing results; it is not a new Order Lemma, an inference
from divergence of the natural prefixes, or a claim of literature priority.
The analytic application is given on paper and has not been completely
formalized in Lean.

For $t>0$ keep the **complete unbalanced** exponential net

$$
S_t(x)=\sum_{n\ge1}\mu(n)e^{-nt}\rho_n(x),\qquad
\rho_n(x)=\{1/(nx)\},\qquad E_t=S_t+\chi.
\tag{A1}
$$

Its series is absolutely convergent in the half-line Hilbert space:
$\|\rho_n\|_2=n^{-1/2}\|\rho_1\|_2$ and
$\sum e^{-nt}n^{-1/2}<\infty$. No cutoff schedule occurs in (A1).
We show that

$$
\|E_t\|_{L^2(0,\infty)}\not\longrightarrow0\qquad(t\downarrow0).
\tag{A2}
$$

### A shrinking test keeps the moving part of the error

Use the source's isometry $U$. Its exact formulas are

$$
U\rho_n(x)=\frac{\{nx\}}{nx},\qquad
U\chi(x)=\frac{\sin(2\pi x)}{\pi x}.
\tag{A3}
$$

For a fixed $c>0$ put

$$
g_{c,t}(x)=\frac{\mathbf1_{(0,ct)}(x)}{c\sqrt t},\qquad
\|g_{c,t}\|_2=c^{-1/2},
$$

and define

$$
\begin{aligned}
h_c(u)&=\frac1c\int_0^c\frac{\{uy\}}{uy}\,dy,\\
K_c(u)&=e^{-u}h_c(u),\\
A_c(t)&=\sum_{n\ge1}\mu(n)K_c(nt).
\end{aligned}
\tag{A4}
$$

The integrand at $y=0$ may be assigned the value one. One has
$0\le h_c\le1$, and $h_c(u)=1$ whenever $0<u<1/c$.
Absolute Hilbert convergence of (A1) permits termwise pairing in (A3).
The substitution $x=ty$ then gives

$$
\langle US_t,g_{c,t}\rangle=\sqrt t\,A_c(t).
\tag{A5}
$$

Since $|U\chi(x)|\le2$, Cauchy--Schwarz yields the exact estimate

$$
|\sqrt t\,A_c(t)|
\le c^{-1/2}\|E_t\|_2+2\sqrt t.
\tag{A6}
$$

Consequently convergence contradicted in (A2) would imply
$A_c(t)=o(t^{-1/2})$ for **every fixed** $c>0$.
The test has constant norm and shrinking support; no pointwise limit of
$S_t$ is substituted for Hilbert convergence.

### Apply the existing Order Lemma at a known critical zero

Write

$$
\widehat K_c(s)=\int_0^\infty K_c(u)u^{s-1}\,du.
$$

It is holomorphic for $\Re s>0$, since $|K_c(u)|\le e^{-u}$.
Fix any known zero $\rho$ with $\Re\rho=1/2$; its existence is
unconditional and does not assume RH or simplicity. Dominated convergence,
using $h_c(u)=1$ below $1/c$, gives

$$
\widehat K_c(\rho)\longrightarrow\Gamma(\rho)\ne0
\qquad(c\downarrow0).
\tag{A7}
$$

Choose and then hold fixed one $c$ for which
$\widehat K_c(\rho)\ne0$. Absolute summation for $\Re s>1$ gives

$$
\int_0^\infty A_c(t)t^{s-1}\,dt
=\frac{\widehat K_c(s)}{\zeta(s)}.
\tag{A8}
$$

Here the absolute interchange is bounded by
$\Gamma(\Re s)\sum n^{-\Re s}$. Also
$|A_c(t)|\le(e^t-1)^{-1}$, so the integral from $1$ to infinity
in (A8) is entire in $s$. Set $F_c(X)=A_c(1/X)$ for $X\ge1$.
Its Mellin transform therefore has the meromorphic continuation

$$
\int_1^\infty F_c(X)X^{-s-1}\,dX
=\frac{\widehat K_c(s)}{\zeta(s)}
 -\int_1^\infty A_c(t)t^{s-1}\,dt
\qquad(\Re s>1),
\tag{A9}
$$

with the right side meromorphic on $\Re s>0$ and a genuine pole at
$\rho$. The pole's order is the multiplicity of that zero.
The source's Order Lemma applies: $F_c$ is locally bounded and $O(X)$;
the pole implies its convergence abscissa is at least $1/2$, while the
$O(X)$ bound makes it at most one. Thus it has the finite abscissa
required there. The lemma gives

$$
F_c(X)\ne o(X^{1/2}),\quad\text{equivalently}\quad
A_c(t)\ne o(t^{-1/2}).
\tag{A10}
$$

This contradicts the consequence of (A6), proving (A2). In particular,
there is no need to replace a multiple zero by a hypothetical simple one,
or to sum the residues of all zeros.

### Retain the unit-interval and logical boundaries

The unit interval has the same obstruction. For $x>1$ one has
$S_t(x)=a(t)/x$, where

$$
a(t)=\sum_{n\ge1}\frac{\mu(n)}n e^{-nt}\longrightarrow0.
$$

This limit is the classical Abel theorem applied to the convergent
series $\sum\mu(n)/n=0$, whose PNT provenance is recorded in the
source's §1. Therefore

$$
\|E_t\|_{L^2(0,\infty)}^2
=\|1+S_t\|_{L^2(0,1)}^2+|a(t)|^2,
\qquad
\|1+S_t\|_{L^2(0,1)}\not\longrightarrow0.
\tag{A11}
$$

In [Alvarez Cruz--Alvarez Gutierrez v3](alvarezcruz2026colombeau.md),
Conjecture 6.2 uses exactly this complete net with $t=\varepsilon^2$.
Equations (A2)--(A11) exclude its convergence conclusion for the actual
net, without assuming RH. This is stronger for this particular family
than a local $O(\varepsilon^2)$ lower bound that still tends to zero.
It is not the literal negation of the implication
$\mathrm{RH}\Rightarrow P$: that logical negation would additionally
require RH itself. No RH conclusion is drawn.

This argument excludes full convergence as $t\downarrow0$. It does not
exclude every subsequence or every cutoff $n(t)$. It does not settle
arbitrary balanced exponential families or freely chosen approximation
coefficients, or change the existing results for $n^{-\delta}$ damping. A cutoff can inherit it only after its complete
Hilbert tail is shown to vanish at the stated scale. The unchanged
[Nyman--Beurling closure criterion](baezduarte2002nyman.md), the signed
Robin remainder and actual critical FIB growth remain separate problems.
