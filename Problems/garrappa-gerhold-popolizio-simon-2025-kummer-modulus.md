---
slug: garrappa-gerhold-popolizio-simon-2025-kummer-modulus
bibkey: garrappagerholdpopoliziosimon2025mittagleffler
doi: 10.1016/j.jmaa.2025.129588
triage: theorem
motivation_gids:
  - D5/S3/Analytic/KummerModulusLowerBound/Result.result
url: https://arxiv.org/abs/2410.11852
---

# A counterexample to the universal Kummer modulus lower bound

## Problem

R. Garrappa, S. Gerhold, M. Popolizio and T. Simon,
*On some inequalities for the two-parameter Mittag-Leffler function in the complex plane*,
J. Math. Anal. Appl. 551(1) (2025), 129588,
DOI 10.1016/j.jmaa.2025.129588, arXiv:2410.11852v4, Remark 6:

> In view of the preceding result and Remark 2, one may ask if for all α, β > 0 one has |M(α, α−β, z)| ≥ M(α, α−β, ℜz), z ∈ ℂ. (2.4) … In particular, (2.4) holds globally for α > 1 ≥ β > 0 … The question whether (2.4) holds globally for all α, β > 0 seems to be still open.

Remark 2(a) identifies M as "a Kummer confluent hypergeometric function": M(a, b, z) = Σ_{n≥0} (a)_n z^n / ((b)_n n!), b ∉ {0, −1, −2, …}.

The verified locators are Remark 6 and Remark 2(a) of v4; a page number
is not asserted from the supplied extract.

### Formal reading

Names without a prefix belong to `D5.S3.Analytic.KummerModulusLowerBound.Result`.

| Source object | Lean object | Correspondence |
| --- | --- | --- |
| $(a)_n/((b)_n n!)$ | `D5.S3.Analytic.KummerRatio.Defs.kummerCoeff` | The frozen real coefficient, cast into ℂ for complex arguments. |
| $M(a,b,z)$ | `kummerC` | Infinite sum of those coefficients times $z^n$. |
| $M(a,b,x)$ for real $x$ | `D5.S3.Analytic.KummerRatio.Defs.kummer` | The original real series. |
| The universal question | `claim` | All positive real $\alpha,\beta$, nonpole second parameter, and all complex $z$. |
| Negative answer | `result` | Exactly `¬ claim`. |

## Motivation

The settling declaration is `D5/S3/Analytic/KummerModulusLowerBound/Result.result`.
The source note is `D5/L/Asymptotics/garrappagerholdpopoliziosimon2025mittagleffler`.
A nonreal zero with a positive value at its real part prevents a global
modulus lower bound, even though the function is real on the real axis.

## Gap

The universal assertion is false. At $\alpha=1/2$, $\beta=2$,
the second parameter $-3/2$ is not a nonpositive integer.
The complex function vanishes at $z_0=1/2+i\sqrt2/2$,
while $M(1/2,-3/2,\Re z_0)=(2/3)e^{1/2}>0$.

## Route

The rising-factorial multiplication identity with lengths $(n,2)$ and
$(2,n)$, evaluated at $-3/2$, gives

$$\frac{(1/2)_n}{(-3/2)_n}
=1-\frac43 n+\frac43 n(n-1).$$

Combining the exponential series and its first two factorial moments yields

$$M(1/2,-3/2,z)=e^z\left(1-\frac43z+\frac43z^2\right).$$

The quadratic has roots $1/2\pm i\sqrt2/2$. Its value at $1/2$ is $2/3$.
The real identity follows from the complex identity by the real embedding
and its commutation with the infinite sum and exponential.

## Falsifier

The parameters satisfy every hypothesis of `claim`, but the real-axis
value is strictly positive and the complex norm is zero.
An error in the coefficient correspondence or the closed-form evaluation
would invalidate this refutation.

## Evidence

**PROVED.** `D5.S3.Analytic.KummerModulusLowerBound.Result.result`
states the negation of the universal assertion. The private helpers
`coeff_eq`, `complex_closed`, `real_closed`, `witness_zero` and `witness_pos`
establish the coefficient identity, closed forms, vanishing and positivity.

**COMPUTED.** The immutable
[experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/76b30be913222242d8f6b99d7fb3863e2dffd42a/experiments/garrappa-gerhold-popolizio-simon-kummer-modulus)
contains `ggps-check.py`, SHA-256
`6a8363b4e962111360855419ef4877298ea747b64948a17bc423e5b50ebb1fb9`.
Command: `python3 ggps-check.py`; exit code 0; mpmath precision 50 decimal digits.
The tested scope is the three fixed witnesses A, B and C and the three
additional fixed complex arguments checking A's identity. For A, the
computed modulus is about $1.94\times10^{-51}$ and the real-axis value
is $1.09914751380009$. This finite-precision residual supplements the exact
zero in Lean. For C, the computed root is
$0.237843258897860-0.365017840801028i$, the modulus residual is
$1.65\times10^{-51}$ and the real-axis value is $0.997645617862620$.
For B, the modulus is $0.0100765054719179$ and the real-axis value is
$0.0163887687932796$.

The supplied literature scope contains two citing works, on derivatives
of Mittag-Leffler functions (DOI 10.1007/s11071-025-11682-3) and nabla
Mittag-Leffler functions (DOI 10.1016/j.chaos.2025.117157), together with
the supplied web, repository and Formal Conjectures searches. No settlement
was found in that scope; the full texts of the two citing works were not
read. This is a bounded search, not a priority or completeness assertion.

## Triage

### What the settlement shows

- **PROVED.** The global assertion for all positive $\alpha,\beta$ is false:
  `D5.S3.Analytic.KummerModulusLowerBound.Result.result`. A nonreal zero
  of the quadratic factor and a positive value at its real part give the
  obstruction. This does not contradict Remark 6's range
  $\alpha>1\ge\beta>0$.
- **PROVED.** Witness A's global closed form
  $M(1/2,-3/2,z)=e^z(1-4z/3+4z^2/3)$ is
  `D5.S3.Analytic.KummerModulusLowerBound.Result.complex_closed`
  (private); its real restriction is `real_closed`. The selected-point
  residuals in Evidence are only numerical checks of this proved identity.
- **PROVED (in prose).** Witness C has $\alpha=3/2$, $\beta=3$.
  Kummer's transformation $M(a,b,z)=e^zM(b-a,b,-z)$ applies since
  $b=-3/2$ is not a pole. Here $b-a=-3$, so the series terminates:
  its constant term is $1$, and its three nonconstant terms are

  $$\frac{-3}{-3/2}(-z)=-2z,\qquad
  \frac{(-3)(-2)}{(-3/2)(-1/2)}\frac{(-z)^2}{2!}=4z^2,\qquad
  \frac{(-3)(-2)(-1)}{(-3/2)(-1/2)(1/2)}\frac{(-z)^3}{3!}
  =\frac83z^3.$$

  Every higher term vanishes because $(-3)_n=0$ for $n\ge4$.
  Thus $M(3/2,-3/2,z)=e^z(1-2z+4z^2+8z^3/3)$ for every complex $z$.
  This identity is proved in prose, not formalized in Lean here.
- **COMPUTED.** Witness C's nonreal root, modulus residual, positive
  real-axis value and numerical failure are the C readings in Evidence,
  with the pinned script, command, exit code, hash and precision there.
  Thus the numerical failure also occurs with $\alpha>1$.
  Comparing this witness with the paper's reciprocal complete-monotonicity
  result requires the function and interval qualifications in ASSUMED-UNVERIFIED.
- **COMPUTED.** Witness B has $\alpha=2$, $\beta=3/2$, so its second
  parameter is $1/2>0$. At $z=-10+5i$, the B readings in Evidence give
  $|M(2,1/2,z)|<M(2,1/2,-10)$. These are direct numerical evaluations
  of the Kummer series; no global closed form for B is claimed here.
  The computation uses the pinned script, command, exit code, hash and
  precision in Evidence.
- **PROVED (in prose).** Wherever a real entire function $f$ is positive,
  the global inequality $|f(x+iy)|\ge f(x)$ requires log-concavity.
  Taylor expansion at real $x$ gives
  $|f(x+iy)|^2=f(x)^2+y^2(f'(x)^2-f(x)f''(x))+O(y^4)$.
  Dividing the nonnegative difference by $y^2$ and taking $y\to0$
  gives $f'(x)^2-f(x)f''(x)\ge0$, equivalently
  $(\log f)''(x)\le0$ on each positive interval. This necessary condition
  is not asserted sufficient and is not a Lean theorem here.
- **OPEN.** The exact parameter region for (2.4), beyond the paper's
  $\alpha>1\ge\beta>0$, remains unclassified here. The Kummer
  transformation suggests further polynomial cases for integral $\beta$;
  no uniform classification follows from these three witnesses. Other
  theorems of the paper retain their stated hypotheses; no positive
  consequence depending on the universal assertion is obtained.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage, citation-index completeness and priority
are unverified. No new network search is asserted. B and C are numerical
observations at fixed parameters, not Lean proofs or uniform parameter
regions. C's global closed form is proved in prose in Triage; A's is proved
by `complex_closed` in Lean. No global closed form for B is asserted.
The log-concavity consequence is proved in prose only. A complete
classification beyond the paper's proved range is not supplied.

The precise function, parameter restrictions and interval of the paper's
reciprocal complete-monotonicity result have not been checked against the
article. That result cannot be applied to witness C on $[0,\infty)$:
the closed form proved in prose in Triage gives $f(0)=1$ and
$f'(0)=-1$, hence
$(1/f)'(0)=1$, whereas a completely monotone function is nonincreasing.
This derivative check is in prose; the numerical failure at C does not
establish a counterexample within a completely monotone reciprocal class.
