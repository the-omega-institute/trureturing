---
slug: hannasubst
bibkey: hanna2009a163921a157675
doi: null
url: https://oeis.org/A163921/internal
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegrality.result
---

# Hanna's self-substitution integrality conjecture

## Problem

P. D. Hanna, [OEIS A163921](https://oeis.org/A163921/internal), unpaginated comment; [preregistration #18709](https://github.com/the-omega-institute/trureturing/issues/18709).

> Conjecture: if F(x) = exp( Sum_{n>=1} L(n)*x^n/n ) is an integer series, then the g.f. that satisfies: G(x) = exp( Sum_{n>=1} G( L(n)*x )^n*x^n/n ) is also an integer series.

For $L:\mathbb N\to\mathbb Q$, let $F(x)=\exp(\sum_{n\ge1}L(n)x^n/n)$. If every coefficient of $F$ is an integer, a solution of $G(x)=\exp(\sum_{n\ge1}G(L(n)x)^n x^n/n)$ exists, and every solution has integer coefficients. All series are ordinary formal series over $\mathbb Q$; analytic convergence and positivity are not hypotheses.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Sum over positive $n$ | `HannaSelfSubstitutionIntegrality.logSum` | The coefficient of degree $N$ is the finite sum of $[x^{N-n}]f(n)/n$ for $1\le n\le N$; subtraction is natural and division rational. |
| Exponential input $F$ is integral | `claim`'s hypothesis, using `HannaLogarithmicPowerClosure.IntegralSeries` | The exponential and logarithmic coefficient sum are inlined; each coefficient has an integer witness. |
| $G(L(n)x)^n$ | `SolvesHanna` | Mathlib `PowerSeries.rescale` performs dilation and `PowerSeries.subst` performs formal exponential substitution. |
| The generating function satisfying the equation is integral | Both conjuncts of `claim` | Existence and integrality of every solution; no assumed solution or extra restriction on $L$. |
| The conjecture holds | `HannaSelfSubstitutionIntegrality.result` | Exactly `claim`. |

The value $L(0)$ is unused. Rational $L$ preserves the stated scope: integral $F$ forces the positive-index values of $L$ to be integers. The source input expression is literal in `claim`; the proof reuses `HannaDiagonalGhostPowerIntegrality.logarithmicInput` through the private consumed correspondence `logSum_constants`.

## Motivation

The general theorem settles the A163921 comment and supplies the A157675 specialization $L(n)=2^n$, whose separate [dossier](hannasubst-a157675.md) and settling result refer to #18710. No further theorem conditional on these conjectures is identified in the inspected source entries. Both settling modules have generality `I`, utility `none`, and their respective external open-problem-resolution admission bases.

The admission basis is `open-problem-resolution`, not `escape-witness`. The tier-1 external assertions were preregistered before probes in #18709 (the general conditional assertion) and #18710 (the A157675 assertion). Those preregistrations supply the quoted OEIS sources, full quantifiers, tier and attributed literature screen. Their literature completeness remains `ASSUMED-UNVERIFIED`; the screen is not a worldwide priority certificate. Each module retains its definitions, its one settling `result`, and only auxiliary declarations used on a live proof path. Both `result` declarations and every theorem helper have `proof_shape: bind-only` and `escape_witness: none`; the source lists their actual consumers. The specialized `result` needs its own #18710 settlement exception, since it has no mathematical consumer. This is unbounded symbolic mathematics with utility `none`, not a finite positive instance.

## Gap

The source and literature checks recorded in #18709 and #18710 found no settlement in the inspected scope. The search-seat bibliography includes Heninger–Rains–Sloane on roots of series, Krattenthaler–Müller arXiv:1412.7014 on Dwork's criterion, Byszewski–Graff–Ward on Dold sequences, and Puri–Ward arXiv:math/9907003. Those bibliography readings are attributed to the preregistration, not asserted as independently re-read here. Literature completeness and worldwide priority are `ASSUMED-UNVERIFIED`.

## Route

The consumed `HannaDiagonalGhostPowerIntegrality.integral_input_ledger` supplies an integer Euler ledger for the input. The same owner's `divisor_ghost_gauss` implies $L(pm)\equiv L(m)\pmod p$ for primes $p$ and positive $m$. The private `power_lift` applies Mathlib's ideal congruence power lifting to obtain $p^{v_p(m)+1}\mid U^m-V^m$ from $p\mid U-V$.

Write $H_B(x)=\sum_{n\ge1}B(L(n)x)^n x^n/n$. Frobenius and these congruences pair the terms indexed by $pm$ in $H_B-p^{-1}H_B(x^p)$. Power lifting cancels the denominator $m$, so this difference is locally integral at $p$. The consumed `DoldExponentialIntegrality.local_exp_of_log_difference` gives local integrality of $\exp(H_B)$, and `integral_of_local` combines all primes. The private `preserve_integer_ghost` states the resulting preservation theorem.

The operator increases coefficient agreement by one degree. `PowerSeriesNormalizedContraction.exists_unique_fixed` supplies the fixed point; the private `claim_of_preservation` proves that its degree-$n$ coefficient equals that of an integral iterate from $1$. The public `result` combines preservation with this induction. `geometric_input` is consumed by `HannaSelfSubstitutionIntegralityA157675.result`. The frozen contraction theorem also applies over the integers under preservation; rational uniqueness then identifies every solution with that integral fixed point. Thus the displayed induction is consumed bind-only reasoning, not an escape witness or new proof content.

## Falsifier

An integral input with a nonintegral solution would contradict `result`. The assumption is substantive: the finite control $L(n)=[n=2]$ has nonintegral $F=\exp(x^2/2)$ and a noninteger solution coefficient in degree $4$. That control is computed evidence, not a refutation of the conditional theorem. No converse or asymptotic growth assertion is included.

## Evidence

The settling declaration is `D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegrality.result`. Its Blueprint Scribe displays the whole claim and acknowledges the [source note](../Library/ArithUnits/hanna2009a163921a157675.md). The sibling settling declaration is `D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegralityA157675.result`.

Experiment: [immutable program and data](https://github.com/the-omega-institute/trureturing-experiments/tree/75bcafbc09412042e4be559b7710f29f59a24ac7/docs/reports/oeis-a163921-a157675-hanna-self-substitution-integrality). With `EXPERIMENTS_CLONE` set to the local clone, command: `git -C "$EXPERIMENTS_CLONE" show 75bcafbc09412042e4be559b7710f29f59a24ac7:docs/reports/oeis-a163921-a157675-hanna-self-substitution-integrality/check.py | python3` with pipe failure propagation, exit 0; script SHA-256 `297cbb33b19c91905094c159b0ef87f8c8d3a8f7c4f5695a1b4020e0fa1a96a4`; final result `RESULT PASS`. The script is Apache-2.0 licensed. These readings cover degrees $0$ through $15$ only.

The escape audit is unfinished for the two settling results and `geometric_input`, listed in [#24041](https://github.com/the-omega-institute/trureturing/issues/24041). No Reg source or `declared_validated` registration is claimed. Missing evidence comprises faithful source reconstruction, an enrolled readout with its exact statement bridge, whole-family variation, sensitivity, and actual observational dependence.

## Triage

### What the settlement shows

1. **Proved, kernel-checked:** the general conditional integrality claim and the A157675 claim are the exact statements of `HannaSelfSubstitutionIntegrality.result` and `HannaSelfSubstitutionIntegralityA157675.result`. The private `exists_unique_solves` also proves uniqueness for every rational sequence $L$ without the integral-input hypothesis.
2. **Proved in prose:** the weaker assumptions $L(n)\in\mathbb Z$ and $L(pm)\equiv L(m)\pmod p$ for every prime $p$ and positive $m$ suffice. For integer $B$, Frobenius gives $B(L(pm)x)^p\equiv B(L(m)x^p)\pmod p$; power lifting gives divisibility by $p^{v_p(m)+1}$ for their $m$th powers. Division by $m$ leaves local integrality in the paired logarithmic difference. Dwork's sufficient criterion gives preservation at every prime; the coefficient-agreement induction gives integral fixed points. This derivation explains the private `preserve_integer_ghost` route; it is not an additional public Lean theorem.
3. **Proved in prose:** the $L=\sigma$ instance satisfies the input hypothesis. The formal Euler product $\prod_{d\ge1}(1-x^d)^{-1}$ has integer coefficients because each degree uses only finitely many factors. Its formal logarithm has degree-$n$ coefficient $\sum_{d\mid n}d/n=\sigma(n)/n$, so it is the required exponential input. Applying the general theorem gives integrality in every degree. The finite initial values below are computed, separately from this formal-product argument.
4. **Proved, kernel-checked:** `geometric_input` gives integral input for every integer $a$ with $L(n)=a^n$; the sibling `result` settles $a=2$. The private `input_pow_eq` identifies the exponential input with $(1-aX)^{-1}$.
5. **Computed:** the pinned checker verifies integral $F$ and $G$ through degree $15$ for $L=\sigma$, $L(n)=2^n$, and four fixed-seed integer Euler ledgers with exponents in $[-3,3]$. It reproduces $1,1,2,7,41,385,5769$ for A163921 and $1,1,3,19,237,5741,270857,25099497$ for A157675, and finds the first noninteger coefficient at degree $4$ for the control. Evidence: the immutable experiment entry, command, exit 0 and hash above. No uniform conclusion follows from this finite test.
6. **Computed inventory:** the canonical settling modules, Scribes and frozen state records implement the two declared claims. The proof reuses private Dold suppliers through `open private`; their frozen owners are unchanged. Registration remains unfinished under #24041; this inventory does not assert audit completion.
7. **Computed inventory:** no judge change is part of the delivery. Evidence is the path-restricted cumulative delivery diff; the content files and canonical state records are its scope.
8. **Open:** whether integrality of $G$ forces integrality of $F$, and the growth of the coefficients. Neither follows from the delivered conditional claim or the finite experiment.

## ASSUMED-UNVERIFIED

Literature completeness and independent priority are `ASSUMED-UNVERIFIED`. The source and literature checks attributed to the orchestrator are the checks recorded in #18709 and #18710. The unfinished escape audit in #24041 is separate from the mathematical settlement.
