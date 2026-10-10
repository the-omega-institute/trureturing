---
bibkey: gafnitao2026exceptionalintervals
authors: Ayla Gafni; Terence Tao
year: 2026
title: On the number of exceptional intervals to the prime number theorem in short intervals
doi: 10.2140/ent.2026.5.221
url: https://arxiv.org/abs/2505.24017v1
claim: Theorem 1.2 bounds the measure exponent of fixed-relative-error short Chebyshev increments through zero density; it does not identify Robin excess states with that exceptional set or provide their prime-sampled count.
strata_touched: []
license: citation-only
triage: anchor
---

# Short-increment exceptional sets and the Robin baseline

The inspected primary is the [versioned HTML](https://arxiv.org/html/2505.24017v1)
of arXiv:2505.24017v1, submitted 29 May 2025. Its abstract metadata
lists *Essential Number Theory* 5 (2026), 221–241 and the DOI above.
The journal edition, complete proof and numerical optimizations were
not independently audited. The definitions and theorem locators
below refer to that manuscript. No Lean certification is claimed.

## The averaging variable and fixed tolerance

Definition 1.1 fixes $0<\theta<1$, $X>1$ and $\varepsilon>0$, and
defines a set of real starting points

$$
\mathcal E_\varepsilon(X,\theta)
=\{x\in[X,2X]:
|\psi(x+x^\theta)-\psi(x)-x^\theta|
\ge\varepsilon x^\theta\}.
$$

Here $\psi$ includes every prime power. Let $\mu_\varepsilon(\theta)$
be the infimum of the exponents $\xi$ for which its Lebesgue measure
is $\ll_{\varepsilon,\theta}X^\xi$ eventually, and set
$\mu(\theta)=\sup_{\varepsilon>0}\mu_\varepsilon(\theta)$.
An eventually empty set has exponent $-\infty$. The tolerance is
fixed; no uniform rate as $\varepsilon\downarrow0$ is supplied by
this definition.

Section 1.1 defines $A(\sigma)$ by
$N(\sigma,T)\le T^{A(\sigma)(1-\sigma)+o(1)}$ at fixed
$0\le\sigma<1$, counting zero multiplicities and both ordinate
signs. It sets $A(\sigma)=-\infty$ if that zero set is empty.
Theorem 1.2 gives

$$
\mu(\theta)\le
\inf_{\epsilon>0}
\sup_{\substack{0\le\sigma<1\\
A(\sigma)\ge(1-\theta)^{-1}-\epsilon}}
\bigl[(1-\theta)(1-\sigma)A(\sigma)+2\sigma-1\bigr].
$$

The empty supremum is $-\infty$. The small $\epsilon$ in this
formula is distinct from the fixed exceptional-set tolerance.
The source explicitly keeps the infimum because continuity of the
actual density exponent is not known. Theorem 1.3 refines the
right side by also using the source's zero additive-energy exponent;
neither theorem asserts a Robin-excess inclusion or a prime-sampling
law. The published density and energy arguments are reused rather
than recomputed here.

## Normal short increments need not fund a Robin baseline

The [existing uniform short-interval input](../ArithSums/nicolas2025comparison.md#the-local-prime-input-and-its-uniform-range)
already gives
$\psi(x+x^{2/3})-\psi(x)=x^{2/3}(1+o(1))$ uniformly at large
$x$, including its paid prime-power correction. Thus
$\mathcal E_\varepsilon(X,2/3)$ is empty eventually for each fixed
$\varepsilon>0$. This is a direct instance of that existing input,
not a new exceptional-set calculation.

The [same-source persistence application](../Arith/caveney2012sacaga.md#a-wider-actual-price-interval-for-the-same-supplied-power-excess)
uses normal short-interval increments to bound variation while
preserving a potentially positive Robin baseline. Under its
RH-failure hypothesis, the selected excess persists despite these
normal increments. No implication from an excessive full CA Robin
state to $\mathcal E_\varepsilon(X,2/3)$ has been established.
Such an implication would supply the missing exclusion itself.

At shorter lengths, the general measure theorem still concerns
fixed relative errors in increments. An estimate on that set cannot
be transported to a count of data-dependent first-prime CA samples
without a proved inclusion and sampling comparison. A shrinking
tolerance, the exponent tail and the actual $\log C_b$ denominator
also retain separate obligations. No one-sided prime-prefix count,
complete signed Robin tail estimate or RH proof is obtained.
