---
bibkey: baezduarte2000natural
authors: Luis Báez-Duarte
year: 2000
title: Arithmetical Aspects of Beurling's Real Variable Reformulation of the Riemann Hypothesis
doi: null
url: https://arxiv.org/abs/math/0011254v1
claim: "Proposition 4.4 excludes full-sequence L2 convergence of natural Möbius prefixes. The published Order Lemma and classical Mellin–Fourier tools also yield a paper-level obstruction for continuous fixed-shape smoothing with the stated power bounds; arbitrary coefficients and RH remain separate."
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

## Fixed-shape smoothing and the same published Order Lemma

The source's §2 Order Lemma, original TeX label `orderlemma`, applies
to complete smoothed nets as well as natural prefixes. Combine it with
the classical fractional-part Mellin formula and Fourier uniqueness.
The following application excludes an entire fixed-shape family; the
exponential net is one instance. It does not reprove those published
tools, infer smoothing failure from prefix divergence, or claim literature
priority. The analytic application has not been completely formalized
in Lean.

Let $w:(0,\infty)\to\mathbb C$ be continuous and not identically zero.
Assume that some $C>0$ and real $a,b$ satisfy

$$
a<\tfrac12<b,\qquad
|w(u)|\le Cu^{-a}\ (0<u\le1),\qquad
|w(u)|\le Cu^{-b}\ (u\ge1).
\tag{A1}
$$

For $t>0$ define the **complete unbalanced** net

$$
S_t^w(x)=\sum_{n\ge1}\mu(n)w(nt)\rho_n(x),
\qquad \rho_n(x)=\{1/(nx)\}.
\tag{A2}
$$

Each series converges absolutely in $L^2(0,\infty)$: use
$\|\rho_n\|_2=n^{-1/2}\|\rho_1\|_2$ and $b>1/2$ for its tail.
The conclusion is

$$
\boxed{\quad S_t^w\text{ has no strong limit in }L^2(0,1)
\text{ as }t\downarrow0.\quad}
\tag{A3}
$$

Restriction then excludes a strong limit on the half-line. No value
$w(0)$, positivity, zero simplicity, RH or cutoff schedule is assumed.

### Strong convergence would cancel every moving interval test

Fix $0<\alpha<\beta<\infty$. For small enough $t$, the real test
$g_t=t^{-1/2}\mathbf1_{(\alpha t,\beta t)}$ is supported in $(0,1)$
and has norm $\sqrt{\beta-\alpha}$. If $S_t^w\to F$ strongly there,
Cauchy--Schwarz gives

$$
\left|\int_0^1 S_t^w(x)g_t(x)\,dx\right|
\le\sqrt{\beta-\alpha}\left(
\|S_t^w-F\|_2+
\|F\mathbf1_{(\alpha t,\beta t)}\|_2\right)\longrightarrow0.
\tag{A4}
$$

Define

$$
\begin{aligned}
K_{\alpha,\beta}(u)
 &=w(u)\int_\alpha^\beta\{1/(uy)\}\,dy,\\
A_{\alpha,\beta}(t)
 &=\sum_{n\ge1}\mu(n)K_{\alpha,\beta}(nt).
\end{aligned}
\tag{A5}
$$

Termwise pairing is justified by the absolute Hilbert convergence
above. Substitution $x=ty$ identifies the left side of (A4) with
$|\sqrt t\,A_{\alpha,\beta}(t)|$. Consequently strong convergence
would force $A_{\alpha,\beta}(t)=o(t^{-1/2})$ for **every** such interval.
The argument uses shrinking $L^2$ mass of any proposed limit $F$,
without substituting pointwise convergence or the special target $-\chi$.

### Apply the Order Lemma with the actual Mellin domains

Abbreviate the kernel and sum in (A5) by $K,A$. Their bounds are

$$
K(u)=O(u^{-a})\ (u\downarrow0),\qquad
K(u)=O(u^{-b-1})\ (u\to\infty),
\tag{A6}
$$

because $\{1/(uy)\}\le1$ and $\{1/(uy)\}\le1/(u\alpha)$.
Thus $\widehat K(s)=\int_0^\infty K(u)u^{s-1}\,du$ is holomorphic
on $a<\Re s<b+1$. Absolute summation gives

$$
\int_0^\infty A(t)t^{s-1}\,dt
=\frac{\widehat K(s)}{\zeta(s)},\qquad
1<\Re s<b+1.
\tag{A7}
$$

For this interchange, the sum of absolute integrals is bounded by
$\sum n^{-\sigma}\int_0^\infty |K(u)|u^{\sigma-1}\,du$,
where $\sigma=\Re s$. Splitting the sum at $n=1/t$ also gives
$A(t)=O(t^{-1})$ near zero, since $a<1$, and
$A(t)=O(t^{-b-1})$ at infinity. The function $A$ is locally bounded;
the continuous kernel and its locally uniform summable tail even give
continuity.

Set $Q(X)=A(1/X)$ for $X\ge1$. Its Mellin integral is holomorphic
for $\Re s>1$, and on the nonempty overlap $1<\Re s<b+1$ it equals

$$
\int_1^\infty Q(X)X^{-s-1}\,dX
=\frac{\widehat K(s)}{\zeta(s)}
 -\int_1^\infty A(t)t^{s-1}\,dt.
\tag{A8}
$$

The last integral is holomorphic for $\Re s<b+1$, not asserted entire.
The right side is meromorphic on the strip $a<\Re s<b+1$.
Glue it with the original $Q$ transform on $\Re s>1$ to obtain
the meromorphic half-plane $\Re s>a$ required by the Order Lemma.

Fix one known critical-line zero $\rho=1/2+i\gamma$ of $\zeta$.
If $\widehat K(\rho)\ne0$, (A8) has a genuine pole there.
In this branch $Q=O(X)$ has finite convergence abscissa: it is at most
one, and the pole prevents it from being below $1/2$.
The Order Lemma then gives $Q(X)\ne o(X^{1/2})$.
This contradicts (A4). Therefore the assumed strong convergence implies

$$
\widehat K_{\alpha,\beta}(\rho)=0
\qquad\text{for every }0<\alpha<\beta<\infty.
\tag{A9}
$$

The finite-abscissa assertion is only needed in the nonzero-numerator
branch; a kernel yielding $A=0$ need not have finite abscissa.

### All the interval cancellations would force the profile to vanish

Put

$$
H_\rho(y)=\int_0^\infty
w(u)u^{\rho-1}\{1/(uy)\}\,du,\qquad y>0.
\tag{A10}
$$

The majorant $|w(u)|u^{-1/2}$ is integrable at both ends by (A1).
Fubini identifies (A9) with $\int_\alpha^\beta H_\rho(y)\,dy=0$.
Dominated convergence makes $H_\rho$ continuous: for each limiting
$y>0$, fractional-part discontinuities occur at only countably many $u$.
Hence $H_\rho=0$ everywhere.

To use classical Fourier uniqueness, choose
$\max(a,0)<r<1/2$ and put $\kappa=1/2-r\in(0,1)$. Define

$$
f(v)=w(e^v)e^{(r+i\gamma)v},\qquad
k_\kappa(z)=e^{\kappa z}\{e^{-z}\},\qquad
\check f(v)=f(-v).
\tag{A11}
$$

Both functions are in $L^1(\mathbb R)$:
$\|f\|_1=\int_0^\infty|w(u)|u^{r-1}\,du<\infty$,
while $k_\kappa$ decays as $e^{\kappa z}$ at $-\infty$ and
$e^{(\kappa-1)z}$ at $+\infty$. Substitution $u=e^v$ gives

$$
e^{\kappa z}H_\rho(e^z)=(\check f*k_\kappa)(z)=0.
\tag{A12}
$$

Use the Fourier convention $\widehat h(\tau)=\int h(z)e^{-i\tau z}\,dz$.
The classical fractional-part Mellin formula gives

$$
\widehat k_\kappa(\tau)
=-\frac{\zeta(\kappa-i\tau)}{\kappa-i\tau}.
\tag{A13}
$$

This is the proto-Müntz formula in Báez-Duarte,
[*A general strong Nyman--Beurling criterion*, arXiv:math/0505453v1](https://arxiv.org/abs/math/0505453v1),
§3, original TeX label `rhomuntz`, after the change $u=e^{-z}$.
Its multiplier is nonzero on a dense set: zeros of the nonzero holomorphic
$\zeta$ in $0<\Re s<1$ are isolated. The convolution theorem in (A12)
therefore forces the continuous Fourier transform of $\check f$ to
vanish everywhere. Classical $L^1$ Fourier injectivity, for example
[Tao, *245C Notes 2*, Exercise 56(e)](https://terrytao.wordpress.com/2009/04/06/the-fourier-transform/),
gives $f=0$ almost everywhere. Its continuity gives $f=0$ everywhere,
and therefore $w=0$, contrary to (A1). This proves (A3) as a paper
application of the cited tools.

The extra logarithmic weight $e^{rv}$ in (A11) is essential to this
argument: $w(e^v)$ need not be integrable as $v\to-\infty$.
Nor do bare integral Mellin bounds suffice for the discrete sampling
in (A2); the pointwise bounds in (A1) supply that control.

### What the general obstruction adds, and what remains open

It is insufficient to check only $\widehat w(\rho)$. The classical
Müntz profile
$w_*(u)=2(1/u-1/(e^u-1))$ satisfies (A1) with $a=0,b=1$ and
$\widehat w_*(s)=-2\Gamma(s)\zeta(s)$ for $0<\Re s<1$.
This formula is the same cited source's `muntzdef` and `mellinmuntz`
with input $e^{-u}$. Thus its Mellin transform vanishes at every
critical zero. It is still excluded by (A3), since the argument retains
all interval kernels $K_{\alpha,\beta}$ rather than one scalar Mellin
value. The profile and its classical identity are reused examples,
not additional new results.

In particular $w(u)=e^{-u}$ satisfies (A1), so

$$
\|\chi+S_t^{\exp}\|_{L^2(0,1)}\not\longrightarrow0,
\qquad
\|\chi+S_t^{\exp}\|_{L^2(0,\infty)}\not\longrightarrow0.
\tag{A14}
$$

[Alvarez Cruz--Alvarez Gutierrez v3](alvarezcruz2026colombeau.md),
Conjecture 6.2 uses exactly this complete net with $t=\varepsilon^2$.
Equation (A14) excludes its convergence conclusion without assuming
RH. It is not the literal negation of $\mathrm{RH}\Rightarrow P$:
that logical negation would additionally require RH. Subtracting a
balancing correction converging to zero in the same Hilbert norm also
cannot repair this particular exponential net; the existing classical
Abel limit $\sum\mu(n)e^{-nt}/n\to0$ supplies such a correction when
it multiplies $\rho_1$.

The conclusion concerns complete nets with one fixed profile satisfying
(A1), as $t\downarrow0$. It does not exclude every subsequence,
every separately chosen cutoff, profiles changing with $t$, arbitrary
balanced families, or freely optimized coefficients. A cutoff inherits
the obstruction only if its complete Hilbert tail tends to zero.
The published $n^{-\delta}$ approximation and its order of limits in
the [natural-dilation criterion](baezduarte2002nyman.md) are different
families. The actual FIB coefficient transport, critical FIB growth,
the signed Robin remainder and RH remain separate problems.

The nearby scalar obstruction in Báez-Duarte,
[*Möbius convolutions and the Riemann hypothesis*, arXiv:math/0504402v1](https://arxiv.org/abs/math/0504402v1),
§4, original TeX label `lpvariantthm`, assumes nonvanishing of the
profile's Mellin transform on its relevant boundary line. That scalar
convolution theorem does not state (A3); (A9)--(A13) supply the joint
interval argument without the scalar nonvanishing hypothesis.
The distinction is one of hypotheses and approximation families,
without an originality or exhaustive-search claim.
