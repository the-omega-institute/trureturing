---
slug: karp-vishnyakova-zhang-2025-bessel-ratio-log-concavity
bibkey: karpvishnyakovazhang2025unimodality
doi: 10.1007/s00025-025-02431-4
url: https://arxiv.org/abs/2408.01755
triage: theorem
motivation_gids:
  - D5/S3/Analytic/BesselRatioLogConcavity/Result.claim
  - D5/S3/Analytic/BesselRatioLogConcavity/Result.result
---

# Log-concavity of modified Bessel ratios

## Problem

D. Karp, A. Vishnyakova and Y. Zhang, *Unimodality preservation by ratios of
functional series and integral transforms*, Results Math. (2025),
DOI 10.1007/s00025-025-02431-4, arXiv:2408.01755v2, Conjecture 1,
printed page 12, states verbatim (line breaks joined):

> Conjecture 1. Suppose b ≥ 0, ν1 ≥ ν2 > −1 and 0 < a1 ≤ a2. Then the ratio x → Iν1(a1 x)/Iν2(a2 x) is unimodal on (0, ∞). Moreover, if ν1 ≥ ν2 > 0 it is log-concave.

The modified Bessel function of the first kind has the standard series

$$
I_\nu(z)=\sum_{k=0}^{\infty}\frac{(z/2)^{2k+\nu}}{k!\Gamma(k+\nu+1)}.
$$

The encoded claim is

$$
\forall\nu_1\ge\nu_2>0\ \forall\,0<a_1\le a_2,\qquad
x\longmapsto\log\frac{I_{\nu_1}(a_1x)}{I_{\nu_2}(a_2x)}
\quad\hbox{is concave on }(0,\infty).
$$

The source's $b\ge0$ is immaterial because $b$ does not occur in the ratio.
The unimodality assertion is outside this claim.

| Source object | Lean name in `D5.S3.Analytic.BesselRatioLogConcavity.Result` |
| --- | --- |
| Standard real modified Bessel series | `besselI` |
| Universal positive-order log-concavity clause | `claim` |
| Negation of that clause | `result` |

## Motivation

Log-concavity imposes a three-point midpoint inequality on actual function
values. A positive rational series representation allows both finite lower
bounds and rigorous upper bounds for the infinite sums.

## Gap

Status: **Refuted**, by
`D5.S3.Analytic.BesselRatioLogConcavity.Result.result : ¬ claim`.
The witness has $\nu_1=\nu_2=1/10$, $a_1=1$, $a_2=2$ and
$x=3/2,9/2,15/2$.

## Route

Write $\nu=1/10$, $R(t)=I_\nu(t)/I_\nu(2t)$, and

$$
S(w)=\sum_{k=0}^{\infty}\frac{w^k}{k!(\nu+1)_k},\qquad
R(t)=2^{-\nu}\frac{S(t^2/4)}{S(t^2)}.
$$

The frozen Gamma–Pochhammer identity cancels the Gamma factor; real power
laws give the common positive factor $2^{-\nu}$. The series are summable.
Midpoint log-concavity would require $R(3/2)R(15/2)\le R(9/2)^2$.
The reversed strict inequality is equivalent to

$$
S(9/16)S(225/16)S(81/4)^2
>S(81/16)^2S(9/4)S(225/4).
$$

For $t_k(w)=w^k/[k!(11/10)_k]$, put

$$
L(w)=\sum_{k=0}^{59}t_k(w),\quad
\rho(w)=\frac{w}{61(611/10)},\quad
U(w)=L(w)+\frac{t_{60}(w)}{1-\rho(w)}.
$$

For $k\ge60$, $t_{k+1}(w)\le\rho(w)t_k(w)$.
At the six arguments $0\le\rho(w)<1$, hence $L(w)\le S(w)\le U(w)$.
Exact rational arithmetic gives

$$
\begin{aligned}
S(9/16)&\ge1.584,&S(225/16)&\ge223.368,&S(81/4)&\ge894.574,\\
S(81/16)&\le15.316,&S(9/4)&\le4.447,&S(225/4)&\le264068.
\end{aligned}
$$

These bounds already make the left product strictly greater than the right
product. Positivity and the strict monotonicity of the logarithm contradict
concavity at the midpoint $9/2$ of $3/2$ and $15/2$.

## Falsifier

The function must be the standard modified Bessel series, with the same
order and scales in all three values. All original series must converge.
The larger product needs lower bounds and the smaller product upper bounds;
finite partial sums alone do not certify the infinite-sum comparison.

## Evidence

The source locator is https://arxiv.org/abs/2408.01755v2, printed pages
11–12. The settling module is
`D5/S3/Analytic/BesselRatioLogConcavity/Result.lean`.
Its only public theorem is `result`.

The supplied literature check examined the single OpenAlex citing work
(2026, *Optimal Contest beyond Convexity*) and repository references to
2408.01755 and found no settlement in that scope. Literature completeness
and priority remain unverified.
The candidate and initial numerical witness are from the Claude Code
orchestrator using Claude Opus 5.5; the formal implementation is by a Codex
CLI seat.

The programs are in
[the-omega-institute/trureturing-experiments, revision
68dc2f95da20ea97a876d853bed2fb3eb1487827](https://github.com/the-omega-institute/trureturing-experiments/tree/68dc2f95da20ea97a876d853bed2fb3eb1487827/experiments/kvz-bessel-ratio-logconcavity),
directory `experiments/kvz-bessel-ratio-logconcavity`.

- **COMPUTED:** command `python3 kvz-cert.py`, exit 0;
  script sha256 `6953b156eae624d6bb132623f2b943543fade4cd51b90fd0ff7be626b735a4de`.
  With $N=60$ it compares
  $L=L(9/16)L(225/16)L(81/4)^2$ and
  $U=U(81/16)^2U(9/4)U(225/4)$ in exact rational arithmetic.
  Both $L>U$ and $L/U>102/100$ return true.
  The printed quotient $1.0282843597334759$ is a floating approximation.
- **COMPUTED:** command `python3 kvz-scan-second-derivative.py`, exit 0;
  script sha256 `38a539d50492dab954720d48d247b2a0396cd7de21519b88acd0c7fc532bcec5`.
  With mpmath at 30 decimal digits, $a_1=1$, $a_2\in\{1.2,1.5,2,3,5,10\}$,
  and $x=k/8$ for $1\le k\le120$, the script scans the order pairs
  $(.5,.5),(1.5,.5),(2.5,.5),(1.5,1.5),(2.5,1.5),(.3,.1),(.5,.1),
  (1,.1),(.2,.2),(.1,.05),(.5,.25),(1,.5),(.15,.1),(.4,.3)$.
  Orders and scales entered as Python floats retain that input precision.
  The maximum second derivatives for $(.3,.1)$ and $(.2,.2)$ are approximately
  $0.0040342$ and $0.010007$, both at $a_2=10$; their grid locations are
  $3.375$ and $2.75$. Every scanned half-integer pair has a negative maximum.
- **COMPUTED:** command `python3 kvz-scan-midpoint.py`, exit 0;
  script sha256 `ada02b7c2f838fedb9b5ad3edfde88486d88e22378f7543f95ee1f4fb2f25a40`.
  With 50 decimal digits and 300 terms per series, it scans
  $\nu\in\{1/10,1/5\}$, $a_2\in\{2,3,4,5,10\}$,
  centers $x=k/4$ for $2\le k\le39$, and
  $h\in\{1/2,1,3/2,2,3\}$ with $x-h>0$.
  For $\nu=1/10$, the largest midpoint gaps at scales $2,3,4,5,10$ are
  approximately $0.013946,0.020388,0.023760,0.025742,0.029195$.
  The scale-two maximum is at $x=9/2,h=3$.

## Triage

### What the settlement shows

- **PROVED (`D5.S3.Analytic.BesselRatioLogConcavity.Result.result`):**
  the positive-order log-concavity clause is false. The witness uses equal
  orders $1/10$, scales $1,2$ and the three points $3/2,9/2,15/2$.
  The full-series estimate reverses the required midpoint inequality.
- **COMPUTED:** the second-derivative and midpoint experiments in Evidence
  show the failure mechanism for tested small orders below $1/2$:
  the logarithmic ratio can bend upward and have a positive midpoint gap.
  These are finite numerical observations, not a uniform classification of
  all orders below $1/2$.
- **COMPUTED:** the half-integer pairs $(1/2,1/2),(3/2,1/2),(5/2,1/2),
  (3/2,3/2),(5/2,3/2)$ violate no second-derivative concavity test on the
  scanned grid. This does not prove concavity on the positive half-line.
- **OPEN:** whether orders bounded below by $1/2$ restore log-concavity,
  and the sharp parameter region for log-concavity.
- **OPEN:** Conjecture 1's unimodality clause is untouched. Unimodality is
  weaker than log-concavity and does not follow or fail from this midpoint
  comparison. The source's proved integer-order-difference unimodality
  statements are outside the refuted clause; no result may rely on that
  unrestricted log-concavity clause as a valid premise.

## ASSUMED-UNVERIFIED

Literature coverage, citation-index completeness and priority are unverified.
The source and literature checks supplied by the orchestrator are not an
independent exhaustive search. The grids are finite multiprecision
computations; the midpoint grid uses a fixed truncation and is not a uniform
concavity proof or a certified search over all positive arguments.
