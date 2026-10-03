---
bibkey: fukushima2011dirichlet
authors: Masatoshi Fukushima, Yoichi Oshima, and Masayoshi Takeda
year: 2011
title: Dirichlet Forms and Symmetric Markov Processes, second revised and extended edition
doi: 10.1515/9783110218091
url: https://doi.org/10.1515/9783110218091
claim: The symmetric-kernel construction and regular minimal-extension theorem apply to the actual continuous-plus-prime-graph theta energy in the pole measure. They supply its minimal closed realization, not the one-half variance lower bound or equality with the maximal domain.
strata_touched: []
license: bibliographic-reference-only
triage: anchor
---

# The minimal mixed theta jump form

## Source contract

The inspected source is an [HTML reproduction of the second edition](https://dokumen.pub/dirichlet-forms-and-symmetric-markov-processes-2nd-rev-and-ext-ed-9783110218091-9783110218084.html),
whose title page gives print ISBN 9783110218084 and electronic ISBN
9783110218091. Some reproduced mathematical markup is damaged; the legible
operator-domain characterization below is used instead of transcribing the
unreadable square-root display. No publisher PDF was retrieved.

The source is Fukushima–Oshima–Takeda, second revised and extended edition,
Example 1.2.4, printed pp.14–15, conditions (j.1)–(j.3) and equations
(1.2.22)–(1.2.25), together with Theorem 3.1.2, printed p.110.
The first construction permits a measurable destination kernel $j(x,dy)$,
including atoms, when $m(dx)j(x,dy)$ is symmetric, its off-$\varepsilon$
rates are locally integrable and its local small-jump second moment is
finite. More explicitly, (j.1) is
$x\mapsto j(x,X\setminus U_\varepsilon(x))\in L^1_{\rm loc}(m)$ for
every $\varepsilon>0$, (j.2) is symmetry of $m(dx)j(x,dy)$, and (j.3)
is the finite $|x-y|^2$ moment on every compact $K\times K$.
Its maximal finite-energy domain is closed when it is dense in $L^2(m)$. The regular
minimal-extension theorem has separate algebra, cutoff and Markov
hypotheses; it does not automatically equate that extension to the maximal
domain.

Theorem 3.1.2 assumes a closable nonnegative Markovian symmetric form on
$L^2(X;m)$, with $X$ locally compact separable metric and $m$ a full-support
positive Radon measure. Its initial domain must be a uniformly dense
subalgebra of compactly supported continuous functions, admitting a
nonnegative cutoff equal to one on any compact $K$ and zero outside any
relatively compact open $G$ containing $K$. The conclusion is a regular
minimal closed extension with that initial domain as a special standard
core. The theorem's additional locality assertion is conditional on the
initial form being local and is not invoked for this jump form.

Theorem 1.3.1, printed p.20, and Corollary 1.3.1, printed p.21,
equation (1.3.10), give the unique associated self-adjoint generator $A$:
$D(A)\subset D[\mathcal E]$ and
$\mathcal E(u,v)=(-Au,v)$ for $u\in D(A)$ and $v\in D[\mathcal E]$.
We use the nonnegative convention $T=-A$.

## The exact energy, speed and graph atoms

Use the [theta-weighted even Weil interface](lagarias2004li.md), with
$\rho(x)=2\Phi(x)\cosh(x/2)$ and $d\nu=\rho(x)\,dx$.
The original positive smooth even $\Phi$ makes $\nu$ a full-support Radon
probability, equivalent to Lebesgue measure. Put
$\psi(t)=e^{-t/2}/(1-e^{-2t})$ and
$w_n=\Lambda(n)/\sqrt n$, retaining every prime power.
The actual conductance measure off the diagonal is

$$
\begin{aligned}
J_\Gamma(dx,dy)&=\Phi(x)\Phi(y)\psi(|x-y|)\,dx\,dy,\\
J_p(dx,dy)&=\sum_{n\ge2}w_n\Phi(x)\,dx\,
\left[\Phi(x+\log n)\delta_{x+\log n}(dy)
+\Phi(x-\log n)\delta_{x-\log n}(dy)\right].
\end{aligned}
$$

With $J=J_\Gamma+J_p$, the real preform is exactly

$$
D(h)=\tfrac12\iint |h(y)-h(x)|^2J(dx,dy)
=E_\Gamma(h)+E_{\rm prime}(h).
$$

FOT (1.2.23) has no prefactor one-half. Its conductance measure must
therefore be $J_{\rm FOT}=J/2$, with $m=\nu$. The corresponding measurable
destination kernel, set to zero on the diagonal, is exactly

$$
j_{\rm FOT}(x,dy)=\frac1{4\cosh(x/2)}
\left[\Phi(y)\psi(|x-y|)\,dy
+\sum_{n\ge2}w_n\left(
\Phi(x+\log n)\delta_{x+\log n}(dy)
+\Phi(x-\log n)\delta_{x-\log n}(dy)\right)\right].
$$

Thus $\nu(dx)j_{\rm FOT}(x,dy)=J(dx,dy)/2$ preserves the normalization.
Translation exchanges the two prime graphs, so $J$ is symmetric. The
continuous part and each integrated graph marginal charge no $\nu$-null
set. This is not pointwise absolute continuity of $j(x,\cdot)$: that would
exclude the actual atoms.

## The integrability checks retain all long edges

[Romik's theta tail](../Analytic/romik2021orthogonal.md) gives
$\Phi(x)\le Ce^{-2|x|}$. Thus, for $t\ge0$,

$$
C_\Phi(t):=\int\Phi(x)\Phi(x+t)\,dx
\le C^2(t+\tfrac12)e^{-2t}.
$$

The actual global second jump moment is finite:

$$
M_2:=\iint |x-y|^2J(dx,dy)
=2\int_0^\infty t^2\psi(t)C_\Phi(t)\,dt
+2\sum_{n\ge2}w_n(\log n)^2C_\Phi(\log n)<\infty.
$$

At zero use $C_\Phi(t)\le\|\Phi\|_2^2$ and
$\psi(t)\sim(2t)^{-1}$; at infinity use exponential decay. For the prime
part, $\Lambda(n)\le\log n$ gives the summable majorant
$C(\log n)^3(\log n+1/2)n^{-5/2}$, without PNT or RH.
Off any fixed diagonal band the total $J$ mass is finite, and the row
prime sums are uniformly finite on compact $x$ sets, since
$\Phi(x\pm\log n)\le C_Kn^{-2}$ there.
The Gamma row rate at the diagonal is infinite; these hypotheses concern
off-diagonal mass and square differences, not a finite total Gamma rate.

In particular every compact Lipschitz $h$ has
$D(h)\le\operatorname{Lip}(h)^2M_2/2$.
Use compact Lipschitz functions as the uniformly dense algebra for the
minimal-extension theorem: this domain is closed under unit clipping and
admits the required compact-set/open-set cutoffs. Compact smooth functions
are not literally closed under that clipping.

They have the same form closure here. For compact Lipschitz $h$, ordinary
mollification gives compact smooth $h_\varepsilon$ with common support
in a slightly larger compact set, uniform convergence and
$\operatorname{Lip}(h_\varepsilon)\le\operatorname{Lip}(h)$.
The difference increments converge pointwise and their squares are
bounded by $4\operatorname{Lip}(h)^2|x-y|^2$. Dominated convergence using
$M_2$ gives $D(h_\varepsilon-h)\to0$; the $L^2(\nu)$ error also tends to
zero. This verifies the smooth-core interface rather than assuming
clipping preserves smoothness.

## Minimal closure, constants and the even restriction

Let $\mathcal F_{\max}=\{h\in L^2(\nu):D(h)<\infty\}$ and

$$
\mathcal F_{\min}
=\overline{C_c^\infty(\mathbb R)}^{\,\|\cdot\|_{D,1}},
\qquad \|h\|_{D,1}^2=\|h\|_{L^2(\nu)}^2+D(h).
$$

The preceding smooth inclusion makes the maximal domain dense in $L^2(\nu)$.
The source construction supplies a closed maximal form and a regular
minimal form with $\mathcal F_{\min}\subseteq\mathcal F_{\max}$.
The initial compact Lipschitz form is closable as a restriction of that
closed maximal form, so the minimal-extension theorem applies. Equality
of the minimal and maximal domains is not used or asserted.
For $0\le\chi\le1$ even compact smooth and one on $[-1,1]$, put
$\chi_R(x)=\chi(x/R)$. Then

$$
\|\chi_R-1\|_{L^2(\nu)}\to0,
\qquad D(\chi_R)\le\frac{\|\chi'\|_\infty^2M_2}{2R^2}\to0.
$$

Thus $1\in\mathcal F_{\min}$ with zero energy, including all prime tails.
Reflection preserves both $\nu$ and $J$. Averaging a function with its
reflection is contractive in the form norm and preserves the smooth
core, hence

$$
\overline{C_{c,\rm even}^\infty}^{\,\|\cdot\|_{D,1}}
=\mathcal F_{\min}\cap L^2_{\rm even}(\nu).
$$

Complexification gives the even complex closed realization in that even
Hilbert space. It is not claimed densely defined on the full non-even
Hilbert space. Denote its associated nonnegative self-adjoint operator by $T$.
The cited representation gives

$$
h\in D(T)\iff h\in\mathcal F_{\min,\rm even}
\text{ and }D(h,g)=\langle u,g\rangle_\nu
\text{ for some }u\in L^2_{\rm even}(\nu)
\text{ and every }g\in\mathcal F_{\min,\rm even},
\qquad Th=u.
$$

The energy and speed measure are the original ones. Here the pairing is
linear in its first argument and $D(h,g)$ is the polarized complex form.

This is a source application and model-specific verification, without new
Lean certification or an originality claim. The source supplies no
one-half Poincare constant or spectral description. The same-test target
$D(h)\ge\operatorname{Var}_\nu(h)/2$, hence RH and full Robin, remains
unproved. The minimal realization suffices for the compact-test target;
no stronger maximal-domain core equality is a prerequisite.
