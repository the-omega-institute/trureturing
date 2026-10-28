---
slug: hirche-2020-cachin-renyi-information-combining-convexity
bibkey: hirche2020renyibounds
doi: 10.48550/arXiv.2004.14408
url: https://arxiv.org/abs/2004.14408v1
triage: theorem
motivation_gids:
  - D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity.result
---

# Cachin Rényi information combining convexity and concavity

## Problem

The target is the whole of C. Hirche, “Rényi Bounds on Information
Combining”, ISIT 2020, arXiv:2004.14408v1, §IV-D, Conjecture IV.18, Eq. (88):

> There exists a value $1 < \hat\alpha < 1.3863$, such that
> $h_\alpha(h_\alpha^{-1}(x) \ast h_\alpha^{-1}(y))$ is convex for
> $0 < \alpha < \hat\alpha$ and concave for $\alpha \ge 2$.

The formal claim supplies the witness $\hat\alpha=5/4$ and quantifies over
every fixed $y\in[0,\log2]$, with convexity or concavity in $x$ on the whole
closed entropy interval. Put

$$
h_\alpha(p)=
\begin{cases}
-p\log p-(1-p)\log(1-p),&\alpha=1,\\
\log(p^\alpha+(1-p)^\alpha)/(1-\alpha),&\alpha\ne1,
\end{cases}
\qquad p\star q=p+q-2pq.
$$

The inverse branch has probability domain $[0,1/2]$. Logarithms are natural,
all orders are real, and the Shannon value is Mathlib's `Real.binEntropy`.

## Motivation

This provides the scalar convexity and concavity inputs for binary Rényi information
combining. The convexity interval crosses the Shannon order, and concavity quantifies over
every real order at least two. Both statements include entropy endpoints.

## Gap

No independent literature or priority search is claimed. The exact maximal convexity
threshold and quantum conditional-entropy inequalities are outside the formal target.

## Route

Put $\psi(t)=h_\alpha((1-t)/2)$, $n=\alpha-1$ and
$r(t)=(1-t)/(1+t)$. For $0<r<1$, let

$$
T=\frac{1-r^n}{1+r^n},\quad
A=\frac{nr^{n-1}(1-r^2)}{1-r^{2n}},\quad
B=\frac{1-r}{1+r}T,\quad F=\frac{A-B}{1+B}.
$$

For $n\ge1$, the certificate proves that $F$ is increasing. Its nonnegative derivative
uses $J_n(z)=(n-1)-(n+1)z+(n+1)z^n-(n-1)z^{n+1}\ge0$, obtained by two
applications of derivative-sign monotonicity on $[z,1]$ with $z>0$.
For $f=-\psi'>0$, differentiation gives $f'=fF(r(t))/t$.
Consequently $vf(vt)/f(t)$ increases in $t$ for $0<v<1$.
The inverse of $\psi$ decreases, so the first derivative of the transported
combining function decreases in its entropy input. Continuity gives
concavity on the closed interval. The cases $v=0$ and $v=1$ are respectively
a constant and the identity. No endpoint inverse derivative is required.

For $-1<n<0$, the shared derivatives give $A'\le0$, $B'>0$,
$A>0$ and $-1<B<0$, so $F'<0$. At the Shannon order,
$-\psi_1'(t)=\operatorname{artanh}(t)$ and
$E_1(t)=t/((1-t^2)\operatorname{artanh}(t))$ increases because
$\operatorname{artanh}(t)\ge t$.

For $0<n\le1/4$, the auxiliary quotient $C_n$ and $D_n=C_n+nz$ satisfy
the Riccati equations below. An even analytic quotient in $t$ removes the
singularity before substituting $z=t^2$. Its second and fourth derivatives
at zero give local negative curvature. The first-zero argument then gives
$C_n''<0$ on $(0,1)$ and $D_n'<0$, so $1-2zD_n'/D_n$ is strictly increasing.
This equals $F_n((1-t)/(1+t))$ at $z=t^2$. The same inverse transport
therefore gives convexity, with the derivative sign reversed.

The reuse boundary is:

| Needed interface | Reused source | Role |
| --- | --- | --- |
| Binary Shannon entropy and derivative | Mathlib `Real.binEntropy`, `Real.hasDerivAt_binEntropy` | The order-one definition and bias derivative |
| Inverse hyperbolic tangent | `ContractionSpectrumOrder.hasDerivAt_artanh`; Mathlib `Real.artanh_eq_half_log`, `Real.artanh_pos`, `Real.sum_range_le_log_div` | The logarithmic and Shannon derivatives share one source; the one-term logarithm bound gives artanh(t) ≥ t |
| Binary Rényi entropy and convolution | `RenyiInformationCombiningOrderThree.hRenyi`, `bconv`, `bconv_bias` | Non-Shannon entropy, convolution and the bias product identity |
| Inverse branch and continuity | Mathlib `Function.invFunOn_mem`, `Function.invFunOn_eq`, `Set.InjOn.leftInvOn_invFunOn`, `Continuous.continuous_symm_of_equiv_compact_to_t2` | The specified probability inverse and continuity on the closed entropy interval |
| Hyperbolic quotient and derivatives | Mathlib `Real.cosh`, `Real.sinh`, `Real.cosh_sq_sub_sinh_sq` and derivative composition | The Riccati quotient uses explicit cosh/sinh in place of a coth interface |
| Real-power derivatives and binomial series | Mathlib `Real.hasDerivAt_rpow_const`, `Real.one_add_rpow_hasFPowerSeriesAt_zero` | Negative orders and removable initial quotient |
| Analytic removable division | Mathlib `HasFPowerSeriesAt.has_fpower_series_dslope_fslope` | Initial Taylor coefficients |
| First-zero selection and mean value theorem | Mathlib `IsCompact.exists_isLeast`, derivative-sign monotonicity | Global negative curvature |
| Closed-interval convexity | Mathlib `MonotoneOn.convexOn_of_deriv`; `convexOn_of_deriv2_nonneg` is also available | The first-derivative criterion transports through the continuous inverse without a separate second derivative of G |
| Real-order elasticity and inverse transport | Existing `CachinElasticityMonotone` and main-module infrastructure | Shared functions, derivatives and probability branch |

## Falsifier

A violation to the witness theorem consists of a permitted $y$, two entropy
points and a convex weight, violating convexity at some $0<\alpha<5/4$ or
concavity at some $\alpha\ge2$. A source mismatch
or a prior settlement would affect the source or novelty claim independently
of kernel verification.


## Evidence

The settling declaration is `result : claim` in
`D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity.lean`.
The real-power, Shannon, analytic-initial-data and Riccati certificates are
used on the live proof path. The inverse identities are proved
for the specified probability branch. The settling declaration has axiom closure
contained in `propext`, `Classical.choice`, and `Quot.sound`.

## Triage

The complete source conjecture reads: “There exists a value
$1 < \hat\alpha < 1.3863$, such that
$h_\alpha(h_\alpha^{-1}(x) \ast h_\alpha^{-1}(y))$ is convex for
$0 < \alpha < \hat\alpha$ and concave for $\alpha \ge 2$.”
The formalized scope is this entire assertion with witness
$\hat\alpha=5/4$. The settling `result` combines convexity for every $0<\alpha<5/4$ with
concavity for every $\alpha\ge2$, including the Shannon order and all
entropy endpoints.

The exact separate-convexity threshold

$$
\alpha_c=\frac{\sqrt{13}-1}{2}
$$

is **proved on paper, not formalized**. With $n=\alpha-1$,
$C_n(z)=n\sqrt z\coth(n\operatorname{artanh}\sqrt z)$ (with the continuous
$n=0$ and $z=0$ values) satisfies

$$
2z(1-z)C_n'=(1-z)C_n-C_n^2+n^2z.
$$

Its initial derivatives are
$C_n'(0)=-(1-n^2)/3$ and
$C_n''(0)=-2(1-n^2)(4-n^2)/45$. Differentiating the Riccati equation twice
gives

$$
2z(1-z)C_n'''=(-3+7z-2C_n)C_n''+2C_n'(1-C_n').
$$

A first zero of $C_n''$ would have nonnegative derivative, while this
identity makes that derivative negative because $C_n'<0$. Thus $C_n''<0$.
For $D_n=C_n+nz$ and $-1<n\le(\sqrt{13}-3)/2$, its initial slope
$D_n'(0)=(n^2+3n-1)/3\le0$ and its negative curvature imply $D_n'<0$.
Since $D_n>0$, the elasticity
$E_\alpha(t)=1-2t^2D_n'(t^2)/D_n(t^2)$ is strictly increasing. The inverse
entropy transport then gives separate convexity, including the threshold.
The local expansion

$$
E_\alpha(t)=1+\frac{2(3-\alpha-\alpha^2)}3t^2+O(t^4)
$$

makes the elasticity decrease near zero when $\alpha>\alpha_c$, excluding
separate convexity there. This expansion and the exact threshold are not
claimed as kernel-verified conclusions.

The interval $(\alpha_c,2)$ lies between the two convexity/concavity regimes.
Lemma IV.16 of the paper shows neither convexity nor concavity on
$(1.387,1.95)$. That lemma does not by itself settle concavity throughout
$(\alpha_c,2)$; the local expansion excludes convexity above
$\alpha_c$, and a concavity classification of the remaining orders is not
asserted here.

## ASSUMED-UNVERIFIED

The paper locator and the absence of a later settlement have not been
independently verified against later literature. The formal theorem has no mathematical
premise asserting the conjecture or its elasticity inequality.
