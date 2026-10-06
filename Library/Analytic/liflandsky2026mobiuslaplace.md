---
bibkey: liflandsky2026mobiuslaplace
authors: Sergey Liflandsky
year: 2026
title: Explicit formulas for the Möbius Laplace transform and a criterion for the Riemann hypothesis and simple zeros
doi: null
url: https://arxiv.org/abs/2607.09797v4
claim: The exact Möbius Laplace endpoint implies RH and simple zeros; the converse retains a uniform Fejér zero-sum bound, and the endpoint implication already specializes Báez-Duarte's convolution theorem.
strata_touched: []
license: citation-only
triage: anchor
---

# The Möbius Laplace endpoint and its additional obligations

The primary version is [arXiv:2607.09797v4](https://arxiv.org/abs/2607.09797v4),
revised 14 September 2026. The title above is the title in its
[v4 full text](https://arxiv.org/html/2607.09797v4); the abstract landing
page retains a different title and abstract. The inspected scope is
Theorem 1.3, §7.1's hypothesis and Theorem 7.2, §8.1's
Propositions 8.2–8.3 and Remark 8.4, and §8.2's explicit predecessor
correspondence. The complete contour, special-function and Fejér proofs
are not independently audited. This is a preprint source note, with no
Lean verification or original FIB criterion claimed.

## Endpoint implication and converse conditions

Write

$$
\Phi_\mu(t)=\sum_{n\ge1}\mu(n)e^{-nt},\qquad t>0.
$$

Theorem 1.3(a) states that

$$
\Phi_\mu(t)=O(t^{-1/2})\quad(t\downarrow0)
\quad\Longrightarrow\quad
\text{RH and simplicity of every nontrivial zero}.
$$

The implication does not assume RH or simplicity. It is stronger than
a criterion whose conclusion is RH alone.

Under RH and simplicity, Theorems 1.3(b) and 7.2 make this endpoint
equivalent to the existence of one constant $C_0$ such that,
simultaneously for every $T>0$ and $t>0$,

$$
\left|
\sum_{|\gamma|<T}
\left(1-\frac{|\gamma|}{T}\right)
\frac{\Gamma(1/2+i\gamma)}{\zeta'(1/2+i\gamma)}
t^{-i\gamma}
\right|\le C_0.
$$

Both positive and negative ordinates are retained. Absolute summability
of these residue coefficients is a sufficient alternative condition;
no linear-independence hypothesis on the ordinates is required.
The source explicitly does not derive the uniform bound from RH and
simplicity alone. Pointwise convergence of a smoothed zero sum does not
discharge this two-parameter uniform estimate.

Proposition 8.2 states that an endpoint with logarithmic loss
$O(t^{-1/2}(\log(1/t))^a)$, $a\ge0$, implies RH and bounds every
nontrivial zero's multiplicity by $a+1$.
Proposition 8.3 states that the exact endpoint also forces
square-summability of the residues. Remark 8.4 distinguishes that
necessary condition from the absolute summability used as a sufficient
hypothesis; it does not prove the latter.

## The endpoint implication already has a predecessor

Section 8.2 explicitly specializes
[Báez-Duarte's Theorem 4.1](baezduarte2005mobiusconvolutions.md).
In that paper's multiplicative-convolution notation, take

$$
g(v)=\sum_{n\le v}\frac{\mu(n)}n,\qquad
h(u)=u^{-1}e^{-1/u},\qquad \phi(u)=u h'(u).
$$

The source gives the exact parameter map

$$
G_\phi(y)=y^{-1}\Phi_\mu(1/y),\qquad
\phi^\wedge(s)=s\Gamma(s+1).
$$

Thus the small-$t$ bound becomes
$G_\phi(y)=O(y^{-1/2})$ as $y\to\infty$.
The source verifies the required Mellin convergence, extension and
nonvanishing conditions for this test. The endpoint implication is
therefore an existing convolution criterion, rather than a new theorem
to reproduce in FIB coordinates.

## Consequence for the actual FIB dilation filter

The [existing smoothing note](verjovsky2026mobiussmoothing.md) already
records the actual two-way dilation identities for $e=\mu*\beta$ and
the summable inverse $\gamma=\beta^{-1}$.
Applying its existing dilation-and-triangle argument to the weighted
supremum $\sup_{t>0}\sqrt t\,|\Phi(t)|$ uses weights $d^{-1/2}$.
The existing inverse budgets make both transport constants finite.

An exact FIB endpoint would consequently carry the source's stronger
RH-and-simplicity obligation, together with the corresponding uniform
zero-sum condition. No endpoint bound for the actual FIB or Möbius
transform is supplied by the filter identities, the five-pattern
geometry, or this note. The RH-only $L^p$ criterion for every $1\le p<2$
in the existing smoothing note remains a different target. Neither
criterion supplies the outstanding complete signed Robin estimate.
