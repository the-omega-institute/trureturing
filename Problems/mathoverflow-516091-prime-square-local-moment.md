---
slug: mathoverflow-516091-prime-square-local-moment
bibkey: unkown2026primesquaremoment
doi: null
url: https://mathoverflow.net/questions/516091/uniform-dominance-of-a-prime-square-term-in-an-euler-product-moment
triage: theorem
motivation_gids:
  - D5/S3/Analytic/SeriesInequalities/PrimeSquareMomentApproximation.result
---

# Uniform prime-square approximation for the full local moment

## Problem

The source is MathOverflow question 516091, revision 1, by **unkown**, GUID `5D544532-802E-47EE-9240-92FCF941D961`. The [attributed source note](../Library/AnalyticClosure/unkown2026primesquaremoment.md) gives the original definitions, question and bounded literature comparison. [Issue #18820](https://github.com/the-omega-institute/trureturing/issues/18820) specifies the quantified target.

All local Lean names below belong to `D5.S3.Analytic.SeriesInequalities.PrimeSquareMomentApproximation`.

| Source clause | Lean counterpart | Domain and endpoints |
| --- | --- | --- |
| $e_p(0)=1$ | `factor p 0` | Index zero is present |
| Rational $e_p(a)$ for integer $a\ge1$ | Nonzero branch of `factor` | Every positive natural exponent |
| Real $s>0$ | `Real.rpow` in `localMoment` | The final real threshold is chosen with $s\ge1$ |
| Full infinite sum over $a\ge0$ | `∑' a : ℕ, (factor p a)^s / p^a` | No truncation or finite proxy |
| $c=\log(7/6)/2$, $P=e^{cs}$ | `c`, `Real.exp (c*s)` | $P^2=\exp(2cs)$ |
| Sufficiently small fixed $\delta>0$ | `0 < δ`, `δ < 1 - c3/c` | `c3 = log(5/4)/3`; positive nonempty interval |
| Every fixed $B>2$ | `∀ B : ℝ, 2 < B →` | Threshold may depend on $δ,B,ε$ |
| Uniform $o(1)$ as real $s\to\infty$ | `∀ ε>0, ∃ S : ℝ, ∀ s≥S, ∀ p, ...` | One threshold precedes both $s$ and $p$ |
| Prime $p\equiv1\pmod4$ | `p : ℕ`, `p.Prime`, `p % 4 = 1` | No change of prime or congruence domain |
| $P^{1-δ}<p\le BP$ | `exp ((1-δ)*c*s) < p`, `p ≤ B*exp(c*s)` | Strict lower, closed upper |
| Logarithmic error $<ε$ | `originalClaim`, `result : originalClaim` | Absolute difference of the two original logarithms |

For positive $P$, its real power $P^{1-δ}$ equals the lower exponential cutoff by the positive-base real-power definition. The two expressions for $P^2$ also agree by exponential multiplication. No integer restriction on $s$ is introduced.

## Motivation

The retained prime-square term can grow on the moving window. A uniform logarithmic approximation therefore needs relative control of that term, as well as a bound on the entire infinite tail. The question isolates this local analytic step without requiring a global random-product theorem.

## Gap

The bounded source and literature checks in the attributed note did not locate an equivalent proof. The two inspected Euler-product comparisons concern global expectations or different function-field factors; they do not supply this moving-prime real-moment estimate. Global priority remains unverified.

## Route

For $p>1$, every $e_p(a)$ is positive and at most $3/2$. For $s\ge0$, comparison with $(3/2)^s p^{-a}$ proves summability of the original real series. Its zero-index term is one, so $m_p(s)>0$ for $s>0$. Thus the real tsum has its intended series value and the logarithm is taken on a positive argument.

For $a\ge3$, induction gives

$$
g(a)^3\le(5/4)^a,\qquad \log e_p(a)\le\log g(a)\le c_3a.
$$

The inductive ratio comparison reduces, after putting $y=a-3\ge0$, to nonnegativity of

$$
27y^6+675y^5+6759y^4+34525y^3+93906y^2+126300y+62568.
$$

Hence, with $q=e^{c_3s}/p<1$,

$$
0\le T:=\sum_{a\ge3}\frac{e_p(a)^s}{p^a}\le\frac{q^3}{1-q}.
$$

This is a bound on the full summable shifted series. For $p\ge2$, the exact exponent-two identity gives

$$
e_p(2)=\frac76\left(1-\frac4{21p-14}\right),\qquad
2c-\frac2p\le\log e_p(2)\le2c.
$$

Set $X=e^{2cs}/p^2$, $A=1+X$, $R=e^{-2s/p}$, $A_0=1+e_p(2)^s/p^2$, and $U=e_p(1)^s/p+T$. Then

$$
AR\le A_0\le A,\qquad 0\le U\le\frac1p+T,\qquad
m_p(s)=\left(1-\frac1p\right)(A_0+U).
$$

All factors are positive. The inequalities $\log(1-x)\ge-2x$ for $0\le x\le1/2$ and $\log(1+y)\le y$ give

$$
\left|\log m_p(s)-\log A\right|
\le\frac2p+\frac{2s}p+\frac{q^3}{1-q}.
$$

This relative sandwich is the additional uniform control needed when the retained term $X$ can grow. A small absolute tail alone does not replace the exponent-two and prefactor estimates.

The rational inequality $(5/4)^2<(7/6)^3$ proves $0<c_3<c$. Consequently $1-c_3/c>0$. For any admissible $δ$, put $α=(1-δ)c>c_3$ and $κ=α-c_3>0$. On $p>e^{αs}$,

$$
p^{-1}\le e^{-αs},\qquad q\le e^{-κs}.
$$

Eventually $q\le1/2$, and $q^3/(1-q)\le2q$. The error is therefore bounded uniformly by

$$
2e^{-αs}+2s e^{-αs}+2e^{-κs}\longrightarrow0
\qquad(s\in\mathbb R,\ s\to\infty).
$$

The proof extracts one threshold for this majorant to be below $ε$, for $e^{-κs}\le1/2$, and for $s\ge1$. The estimate already holds for all real $p\ge2$ satisfying the lower cutoff; the source's prime, congruence and upper-window restrictions are retained by specialization.

## Falsifier

A counterexample must provide an admissible fixed positive delta, a fixed real B>2 and a positive epsilon such that every real threshold has a later real s and a prime p≡1 modulo four in the exact strict-lower, closed-upper window whose logarithmic error is at least epsilon. Fixed-prime limits, natural-s subsequences and finite truncations do not test this assertion.

## Evidence

The [Lean source](../D5/S3/Analytic/SeriesInequalities/PrimeSquareMomentApproximation.lean) has the single settlement theorem `result : originalClaim`. The public scale helpers `c3_lt_c` and `c_pos` are used by its proof and by the source audit's nonvacuity construction. All other mathematical lemmas are private steps of the series comparison, logarithmic sandwich and real-limit proof. The header classification is `utility: none`: this is an infinite-domain analytic argument, not a bounded computational instance.

The source audit uses the same full quantified window statement, observing its first logarithm. Arbitrarily large primes congruent to one modulo four give window points at $s=\log p/c$. Replacing that observation with the constant $-1$ violates the conclusion with $ε=1/2$. This proves whole-family variation and sensitivity for the zero-error limit in the actual source domain. The actual logarithm readout distinguishes inputs $1$ and $e$. The separate positive-scale and strict-gap registrations observe their original real operands. The residual in each registration is explicitly unknown; no inexhaustibility or undecidability is asserted.

The mathematical and typed audit proofs compile, but the four-slot audit is **unfinished**. The source-family assessments for each of `result`, `c3_lt_c` and `c_pos` are `declared_unresolved`, with certificate `null` and diagnostic `IE-C050 ClosedTruthReadout`, reason `unclassified_form`, rule `source.residual_requires_open`. They reject the supplied real escape origin before source reconstruction: the source branch requires an absent origin, whereas the four-slot contract requires `escapeFrom := some ℝ`. Accepted source-family binding certificates and complete `declared_validated` four-slot records for these exact targets remain missing. [Issue #18929](https://github.com/the-omega-institute/trureturing/issues/18929) records the concrete template obstacle, verdict and missing evidence under the CLAUDE §3.9 linked-issue exception; it supplies neither proof nor audit validation. [Issue #18820](https://github.com/the-omega-institute/trureturing/issues/18820) is the target preregistration.

## Triage

Tier 1, resolution **Proved** for `originalClaim`, with admission basis `open-problem-resolution` and target preregistration #18820. This classification concerns the source's small technical question; it asserts no independent resolution credit before the required review and integration. The proof shape of `result` is content: its live proof uses the new complete geometric-tail and relative logarithmic estimates. `c_pos` and `c3_lt_c` are consumed bind-only scale helpers, obtained by rational normalization and existing logarithm laws.

**Proved scope:** the logarithmic sandwich uses a relative lower bound on the exponent-two contribution, so it remains valid when that contribution grows. The internal uniform estimate applies to every real $p\ge2$ above the lower cutoff; primality, congruence and the upper cutoff are needed only to retain the question's stated domain. The full-tail slope and $0<c_3<c$ provide an explicit positive delta interval. **Unresolved scope:** optimal delta endpoints, global products and prime sums require additional arguments and are not consequences claimed here. The source question's logarithm-control step is supplied; no other downstream source assertion is settled.

## ASSUMED-UNVERIFIED

The claimed resolution is the exact local approximation. It does not include a global Euler product, a prime sum, an optimal delta endpoint or any other open problem. The bounded primary and literature readings did not locate an equivalent proof; global priority and literature completeness remain `ASSUMED-UNVERIFIED`. A formal proof does not establish publication or author acceptance.
