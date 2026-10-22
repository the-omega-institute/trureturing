---
bibkey: suzuki2023aspects
authors: Masatoshi Suzuki
year: 2023
title: Aspects of the screw function corresponding to the Riemann zeta-function
doi: 10.1112/jlms.12785
url: https://arxiv.org/abs/2206.03682v4
claim: The screw-kernel form has a uniform high-complement lower bound in its transform norm; its nondegeneracy on the full L2 space at every support is equivalent to RH. Smooth-domain nondegeneracy and positive high complements do not supply that all-support condition.
strata_touched: []
license: citation-only
triage: anchor
---

# High complements and the space-completion condition

## Primary source and scope

https://doi.org/10.1112/jlms.12785

https://arxiv.org/abs/2206.03682v4

The journal article is in *Journal of the London Mathematical Society*
**108** (2023), no. 4, 1448–1487. The locators below refer to the
32-page arXiv v4 PDF, whose title page says “Version of May 31, 2023”.
The versioned HTML displays a different body date; it is not used for
these locators. These are paraphrases of inspected source statements,
not a new criterion, an independent audit of the whole proof, or Lean
certification.

## The high-complement estimate uses the primitive metric

Section 4.2, printed p.12, equation (4.1), defines $K(a)$ as smooth
$2a$-periodic functions restricted to $[-a,a]$ and extended by zero,
and $K_N(a)$ by vanishing Fourier coefficients for $|n|\le N$.
For $\phi\in L^2(-a,a)$ put

$$
I_0^{(a)}\phi(t)=\int_{-a}^t\phi(u)\,du,
\qquad
\Phi_1(\phi,z)=\frac{\widehat\phi(z)-\widehat\phi(0)}{z},
$$

using the continuous value at $z=0$, and define

$$
\mathfrak K_{N,0}(a)=
\{\phi\in L^2(-a,a):\widehat\phi(0)=0,\ I_0^{(a)}\phi\in K_N(a)\}.
$$

Theorem 4.3, printed p.15, equation (4.12), states

$$
\forall a_0,\mu>0\ \exists N\ge0\ \forall 0<a\le a_0\
\forall\phi\in\mathfrak K_{N,0}(a):\quad
\langle\phi,\phi\rangle_{G_g,a}
\ge\mu\int_{\mathbb R}|\Phi_1(\phi,z)|^2\,dz.
$$

The squared transform norm on the right is that of the primitive, as
used in its proof on p.16; it is not a lower bound by $\mu\|\phi\|_2^2$.
The cutoff depends on the support ceiling and requested margin. The
source statement does not supply the explicit cutoff and coupling
budget required by the project's quantitative section estimates.
Suzuki explicitly follows Yoshida's Lemma 3 in proving the leakage
estimate (4.13). Generic high-complement existence is therefore a
result to reuse, rather than a new research target.

The theorem is quoted in its transform normalization. With the source
convention $\widehat\psi(z)=\int e^{izt}\psi(t)\,dt$ and
$\psi=I_0^{(a)}\phi$, Plancherel gives
$\int_{\mathbb R}|\Phi_1(\phi,z)|^2\,dz=2\pi\|\psi\|_2^2$.
The displayed Parseval equality on p.16 omits this factor. Its fixed
factor can be absorbed in the arbitrary requested $\mu$, but numerical
constants must retain it; no numerical constant is transferred here.

## The finite form retains the correction from its complement

Section 5.2, printed pp.17–19, uses a closed positive subspace $V_N(a)$
whose $L^2$ orthogonal complement has dimension $2N+3$.
Equations (5.3)–(5.4) form the corrected entries

$$
\langle u_m-v_m,u_n-v_n\rangle_{G_g,a},
\qquad |m|,|n|\le N+1,
$$

where $v_n\in V_N(a)$ represents the coupling to $u_n$ in the original
form. The resulting sign test concerns this corrected form, not the
raw Fourier compression. This finite-complement strategy is an
existing method; it does not settle the corrected entries' sign at
all supports.

## Smooth-source and completed-space nondegeneracy are distinct

Theorem 1.4, printed p.3, states that RH is equivalent to nondegeneracy
of $\langle\cdot,\cdot\rangle_{G_g,a}$ on $L^2(-a,a)$ for **every**
$a>0$, equivalently the absence of a zero eigenvalue for its integral
operator at every such support. This equivalence supplies no
unconditional all-support nondegeneracy assertion.

Section 5.4, printed p.23, reports Yoshida's unconditional
nondegeneracy on $C(a)$ and $K(a)$ (his Propositions 2 and 7), while
his RH criterion concerns the completed space
$\widehat K(a)=W(a)\oplus\widehat{K_N(a)}$ for every $a>0$.
Here the high subspace is completed in the positive Weil-form metric.
These Yoshida attributions remain secondary: his original text has
not been inspected here. In particular, the unsquared norm displayed
in Suzuki's p.12 summary is not silently replaced by a claimed
original homogeneous coercivity statement.

For the [project's actual Fourier sections](connesconsanimoscovici2026spectral.md#an-explicit-error-for-the-actual-even-fourier-sections),
the remaining obligation is the actual corrected sign, with controlled
coupling and tails over cofinal supports. For a FIB completion route,
one must also identify the source space, metric and transported form
with the domain in the reused criterion. Nondegeneracy on smooth
sources alone does not discharge the completed-space hypothesis.
This source comparison provides no new Robin estimate or RH proof.
