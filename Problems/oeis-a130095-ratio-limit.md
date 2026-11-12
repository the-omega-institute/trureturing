---
slug: oeis-a130095-ratio-limit
bibkey: adamson2007a130095
doi: null
url: https://oeis.org/A130095
triage: theorem
motivation_gids:
  - D5/S1/Scale/FibonacciErrorRatio
---

# The full OEIS A130095 successive-term ratio limit

## Problem

The source comment states verbatim: “Conjecture: a(n)/a(n-1) tends to phi^2.” Its formula is “a(n) = sum {d | n} Fibonacci(2*d - 1).” Use F(0)=0, F(1)=1 and phi=(1+sqrt(5))/2. The exact target is

$$
\forall\epsilon\in\mathbb R,\quad \epsilon>0\Longrightarrow
\exists N\in\mathbb N,\quad N\ge2\ \land\
\forall n\in\mathbb N,\quad n\ge N\Longrightarrow
\left|\frac{a(n)}{a(n-1)}-\left(\frac{1+\sqrt5}{2}\right)^2\right|<\epsilon.
$$

The divisor sum includes every positive divisor. Every sufficiently large natural index is in scope; there is no subsequence or extra arithmetic hypothesis. In Lean both sequence values are cast to Real before division.

## Motivation

The frozen Fibonacci error-ratio module provides related golden-ratio asymptotics, but does not state the divisor-transform limit. This externally named assertion asks whether the proper-divisor contribution changes the full successive-term ratio.

## Gap

The source's revision 11 states the conjecture and formula without a proof. The bounded literature qualification is recorded in the source note and [issue 29484](https://github.com/the-omega-institute/trureturing/issues/29484). It does not establish worldwide priority or exhaustive continued openness.

The exact event, probabilities and deadline remain those in the unchanged [strict preregistration](https://github.com/the-omega-institute/trureturing/issues/29484#issuecomment-6815772263). Its SHA-256 is `1269af126316d9a2139ab8615463502c63c0e66145f740ac03f4cf6aa0f887a7`. The probabilities 0.97 and 0.97 concern mathematical truth, and the actual model families remain unverified. `firstmath=UNMEASURED` because the earlier Pro mathematical advice was not measured. This dossier supplies no terminal scoring or replacement prediction.

## Route

For n positive, split a(n)=F(2n-1)+R(n). A positive proper divisor d satisfies 2d<=n. Enlarge the remainder sum to all indices up to floor(n/2); the Fibonacci recurrence telescopes this sum to F(2 floor(n/2)), hence R(n)<=F(n). The doubling identity gives F(n)^2<=F(2n-1). Consequently 0<=R(n)/F(2n-1)<=1/F(n), and the upper bound tends to zero by the standard Fibonacci growth lower bound.

Reindex Mathlib's adjacent Fibonacci ratio theorem twice and multiply to obtain F(2n-1)/F(2n-3) tending to phi^2. Multiply this by the quotient of the two correction factors 1+R(n)/F(2n-1) and 1+R(n-1)/F(2n-3). Both correction factors tend to one. Positivity of a(k) for k>=1 and of the relevant Fibonacci values discharges all denominator obligations. The metric limit criterion supplies the exact displayed epsilon statement with N>=2.

## Falsifier

A failure of the full eventual epsilon statement, a missing positive divisor, a different Fibonacci convention, or an undischarged denominator hypothesis would invalidate the claimed source correspondence. Finite-prefix agreement does not prove this limit. A source-equivalent earlier published settlement would invalidate a claim of a new external resolution, without invalidating the mathematical proof.

## Evidence

The settling Lean declaration is `D5.S3.Arith.Divisors.OeisA130095RatioLimit.result`. The explicit targeted governed build verifies the complete event. The axiom closure of the result and its typed Reg evidence is contained in `{propext, Classical.choice, Quot.sound}`. The source-owned Reg mirror reconstructs the complete epsilon telescope and observes both sequence occurrences, with a source-equivalence bridge, whole-family variation, role sensitivity and actual dependence. Its residual continuation is explicitly unknown; no undecidability assertion follows. The canonical typed Scribe mirrors the sequence definition and the full epsilon statement. Independent review, canonical freeze and required checks remain separate from this implementation evidence.

## Triage

The named assertion is a tier-1 external OEIS conjecture under the bounded qualification. Its proposed admission basis is `open-problem-resolution`, not an escape-witness claim or a substantive new research-unit selection. Every proof step is classified bind-only under the repository rule.

| declaration | proof_shape | actual consumers |
| --- | --- | --- |
| `split` | bind-only | `a_pos`, `full_ratio_limit` |
| `a_pos` | bind-only | `full_ratio_limit` |
| `remainder_le` | bind-only | `remainder_ratio_limit` |
| `fib_square_le` | bind-only | `remainder_ratio_limit` |
| `inverse_fib_limit` | bind-only | `remainder_ratio_limit` |
| `remainder_ratio_limit` | bind-only | `full_ratio_limit` |
| `odd_ratio_limit` | bind-only | `full_ratio_limit` |
| `full_ratio_limit` | bind-only | `result` |
| `result` | bind-only | exact externally named settlement under issue 29484 |

All auxiliary lemmas are private and used on the live path to the single public result. The sequence definition earns its inclusion through that result. There are no new direct frozen D5 dependencies: the proof uses pinned Mathlib directly. No separate helper is counted as new mathematics.

**Proved mechanism in the implementation.** Proper-divisor contributions have vanishing relative size, so the full ratio inherits the odd-Fibonacci ratio. This is an all-index argument, including n=2 in the positivity domain, rather than a claim about primes or another subsequence.

**Scope and subsequent questions.** The implementation establishes the original ratio assertion. No quantitative convergence rate, general transform theorem or additional source formula is asserted. The source's generating-function and prime-congruence formulas are separate claims. No new Lean variants or companion endpoints are included.

## ASSUMED-UNVERIFIED

Worldwide literature completeness, priority, independent uptake and actual model-family diversity are unverified. The preserved first-mathematics timing is unmeasured. Independent pre-freeze approval is pending; no freeze or final event settlement is claimed by the implementation alone.
