---
slug: bhatia-jain-2016-stolarsky-mean-matrices-class-a
bibkey: bhatia2016mean
doi: 10.13001/1081-3810.3082
url: https://journals.uwyo.edu/index.php/ela/article/view/1495
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/StolarskyMean/Defs.claim
---

# Bhatia–Jain: Stolarsky mean matrices in class A

## Problem

R. Bhatia and T. Jain, *Mean matrices and conditional negativity*,
Electronic Journal of Linear Algebra 29 (2016), 206–222, section 2.9,
defines the Stolarsky means by

> Sγ (a, b) = ((aγ − bγ)/(γ(a − b)))^{1/(γ−1)}, −∞ < γ < ∞

with their continuous extensions at equal inputs and at parameters
zero and one. Class A means positive entries and exactly one positive
eigenvalue, counted with multiplicity. The supplied source states:

> This family does not yield readily to our analysis. We have some evidence for the following: **Conjecture 1.** Let λ1, λ2, . . . , λn be positive numbers. The matrix [Sγ(λi, λj)] is in the class A if γ ≥ 2 but this is not always so when 0 ≤ γ < 2.

The exact formal target quantifies over every real parameter at least
two and every nonempty positive finite family, allowing repeated
nodes. For each parameter from zero inclusive to two exclusive it
asks for some positive finite family outside class A. The source
proves parameters three and four in Theorems 2.10 and 2.11 and relates
parameters zero, one half, and two to earlier sections.

## Motivation

The real parameter range cannot be reduced to integer power
factorizations. Conditional negativity would give a stronger positive
range conclusion: the quadratic form is nonpositive whenever the
coordinates of the test vector sum to zero. A positive diagonal then
forces exactly one positive eigenvalue.

## Gap

The Loewner divided-difference matrix is proportional to the
entrywise power $S_\gamma^{\gamma-1}$. Its inertia does not determine
that of $S_\gamma$; entrywise roots require their own argument.
Likewise, pointwise nonnegativity of a curvature function does not
establish positive definiteness of every finite translation matrix.

Put $\psi_\gamma(t)=S_\gamma(e^{-t},e^t)$ and
$f_\gamma=\psi_\gamma''-\psi_\gamma$. The needed analytic bridge is
positive definiteness of $f_\gamma$, followed by the mixed-derivative
integration from this one-dimensional statement to conditional
negativity of the mean kernel. The formal curvature theorem and the integration bridge are
complete. The final conjunction still requires repairs to the counterexample module.

## Route

For $p=\gamma-1\ge1$, define

$$
E_a(t)=\frac{\sinh(at)}{at},\quad E_a(0)=1,\qquad
\Phi_p=\left(\frac{E_1}{E_p}\right)^2,
\qquad
\rho_p=\frac{E_p^2}{E_{p+1}^{2-1/p}E_1^{1/p}}.
$$

The logarithmic formula

$$
\log E_a(t)=2\int_0^\infty(1-\cos(ts))\frac{h_a(s)}s\,ds,
\qquad h_a(s)=\frac1{e^{\pi s/a}-1},
$$

and exponential convexity give
$h_b\ge(b/a)h_a$ for $0<a\le b$. Hence
$(2-1/p)h_{p+1}+h_1/p-2h_p\ge0$. The nonnegative logarithmic
density criterion proves positive definiteness of $\rho_p$,
$E_1^{-2}$, and $\Phi_p$. The general second-difference theorem
proves positive definiteness of the continuous extension of
$Q_p(t)=(1-\Phi_p(t))/t^2$. The exact identity is

$$
f_{p+1}(t)=\frac{\rho_p(t)E_1(t)^{-2}Q_p(t)}{p+1}.
$$

This holds also at zero by continuity of both sides. The Schur
product theorem gives positive definiteness of $f_\gamma$.

For positive inputs the paper argument then uses

$$
-\partial_a\partial_b S_\gamma(a,b)
=\frac{f_\gamma(\tfrac12\log(a/b))}{4\sqrt{ab}}.
$$

Integrating this positive kernel twice against the cumulative
coefficients of a zero-sum vector gives conditional negativity.
For parameters below two, the three positive nodes
$(e^{-2z},1,e^{2z})$ supply a two-dimensional positive subspace at
suitable spacing. The integration and spectral steps compile. The counterexample module
requires repairs before the exact formal conjunction can be integrated.

## Falsifier

A parameter at least two and positive finite node family with either
a nonpositive entry or a positive eigenvalue count different from one
would refute the positive-range claim. A parameter in $[0,2)$ for
which every positive finite node family lies in class A would refute
the negative-range claim. An invalid density estimate or failed
factorization would invalidate that route without proving the
opposite matrix statement.

## Evidence

The pinned definitions and exact conjunction are in
[Defs.lean](../D5/S3/Quantum/Matrix/StolarskyMean/Defs.lean).
[KernelFactor.lean](../D5/S3/Quantum/Matrix/StolarskyMean/KernelFactor.lean)
proves profile smoothness, the exact factorization, and
`positiveDefinite_f` for every real parameter at least two.
It directly uses the compiled density formula in
[SinhLogIntegral.lean](../D5/S3/Analytic/Fourier/SinhLogIntegral.lean),
the nonnegative-density criterion, and the general quadratic-deficit
theorem in the PositiveDefinite library. [Result.lean](../D5/S3/Quantum/Matrix/StolarskyMean/Result.lean) proves
the mean-to-CND integration bridge and the complete positive range.
The ThreePoint source is not claimed as compiled here.

## Triage

- PROVED: `KernelFactor.positiveDefinite_f` establishes positive definiteness of the exact derivative defect for every real $\gamma\ge2$, including the arithmetic boundary.
- PROVED: `KernelFactor.f_eq_factor` identifies the derivative defect with the explicit product on the entire real line.
- PROVED: the reusable theorem `SecondDifference.Q_positiveDefinite` gives positive definiteness of the continuous extension of $(g(0)-g(t))/t^2$ for every even twice continuously differentiable positive definite real function.
- PROVED on paper, not formalized here: for $\gamma>2$, the closed form gives $f_\gamma(t)=O(e^{-3|t|})$, so it is integrable. Positive definiteness then gives the explicit Fourier positivity $2\int_0^\infty f_\gamma(t)\cos(\omega t)\,dt\ge0$ for every real frequency. At $\gamma=2$ the function is zero. The Fourier conclusion requires the integrability argument in addition to positive definiteness.
- COMPUTED in the supplied preregistration: 40-digit evaluations at $\gamma\in\{2.3,3,4.7,9\}$ and $t\in\{0.1,0.7,2.5\}$ agree to 15 digits between the closed form, numerical second differentiation, and the factor product. These computations were not rerun in this offline implementation.
- OPEN: whether $f_\gamma$ itself is infinitely divisible for $\gamma>2$. The supplied numerical Fourier tests of $f_\gamma^s$ were positive for $s\in\{0.05,0.3,1,3\}$ at $\gamma\in\{2.5,7\}$; finitely many tests do not establish infinite divisibility.
- PROVED: `Result.conditionallyNegative_stolarsky` establishes conditional negativity, and `Result.inClassA_stolarsky` establishes the complete class A conclusion for every real parameter at least two and every nonempty finite positive family.
- OPEN: the canonical `result : claim` integration; the counterexample module requires repairs. The positive-range proof is compiled independently of that module.
- OPEN and outside the conjecture: classification for $\gamma<0$.

## ASSUMED-UNVERIFIED

The source quotation and bibliographic locators are supplied
information. The DOI-to-PDF correspondence was not independently
confirmed because no local PDF or network access was available.

The supplied preregistration reports arXiv API queries combining
Stolarsky with eigenvalue, matrix, matrices, conditionally negative,
and positive definite; queries for exactly one positive eigenvalue
and mean matrices; web queries for the Bhatia–Jain conjecture and
citing papers; GitHub queries for Stolarsky mean; and local
D5/Problems/Library plus PR and issue queries for Stolarsky,
Bhatia–Jain, and conditional negativity.

Its checked sources include Bhatia–Jain, *Inertia of Kwong matrices*
(arXiv:2307.16007; Journal of Spectral Theory 2024), with no Stolarsky
matrix treatment; Bhatia–Friedland–Jain, *Inertia of Loewner matrices*
(arXiv:1501.01505), which treats $S_\gamma^{\gamma-1}$; Kosaki,
*Strong monotonicity for various means*, Theorem 12 in the supplied
preprint, which supplies ratios but not the whole matrix conjecture;
and Aggarwal–Singh work on translation kernels. No settlement was
found in that checked scope. Semantic Scholar and Google Scholar
were rate-limited or unavailable, so the citing literature was not
exhaustively checked. These are attributed search results, not an
independent search or a priority certification.

The [Bhatia–Jain note](../Library/Fourier/bhatia2016mean.md) and
[Kosaki note](../Library/Fourier/kosaki2014strong.md) bind the supplied
locators and their source boundaries. The analytical proof route was
supplied by GPT Pro via the two preregistered oracle tasks and checked
mathematically by the caller; only the Lean statements explicitly
identified above are formal evidence in this delivery.
