---
slug: op-hanna350410
bibkey: hanna2021a350410family
doi: null
url: https://oeis.org/A350410
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Algebraic/HannaSquareExponentIntegrality.result
---

# Hanna's three square-exponent factorial integrality conjectures

## Problem

Paul D. Hanna's [OEIS A350410](https://oeis.org/A350410), [A350411](https://oeis.org/A350411) and [A350412](https://oeis.org/A350412), revisions 5, 5 and 9, each state: “This sequence is conjectured to consist entirely of integers.” The source NAME and EXAMPLE fields and [preregistration #27303](https://github.com/the-omega-institute/trureturing/issues/27303) fix the following normalizations.

Over $\mathbb Q[[x]]$, put $S_M(B)=\sum_{m=0}^M B^{m^2}/m!$. For A350410 and A350411, $A(0)=-1$ and $[x]A=1$, with $[x^n]S_{M(n)}(A)=0$ for all $n\ge2$, where $M(n)=n$ and $M(n)=n+1$ respectively. For A350412, $A(0)=0$, $[x]A=1$, and $[x^n]S_{2n}(A-1)=0$ for every $n\ge2$. Each normalized rational source exists uniquely, and every coefficient of every such source is an integer.

### Statement echo

All declaration names below belong to `D5.S1.Recurrence.Algebraic.HannaSquareExponentIntegrality`.

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Inclusive sum of square powers divided by $m!$ | `squarePowerSum` | Rational factorial division; all $0\le m\le M$. |
| First two sources start $-1+x$ | `normalized` | Constant coefficient $-1$ and coefficient one $1$. |
| Equations in every degree $n>1$ | `vanishingEquation` | Every natural $n\ge2$, with a degree-dependent cutoff. |
| Cutoff $n$ | `isSourceA350410` | The literal first source. |
| Cutoff $n+1$ | `isSourceA350411` | The literal second source. |
| Cutoff $2n$, expression $A-1$, and $A(0)=0$ | `isSourceA350412` | The source's translation and coefficient-one normalization. |
| Unique rational source and all-index integer coefficients, for each of the three sources | `claim` and `result` | Six conjuncts; no positivity or analytic assumption. |

The integer-coefficient quantifiers appear literally in `claim`; proofs use the existing `HannaLogarithmicPowerClosure.IntegralSeries` predicate. Existence and uniqueness identify the formal series selected by the source examples; they do not restrict the universal integrality assertion to a finite prefix. Generality is `I`, utility is `none`, and admission is `open-problem-resolution (#27303; Proved)`.

## Motivation

The three distinct OEIS conjectures share one coefficient argument. Their finite square-power sums have a nonzero slope, and the exceptional last factorial denominator is cleared by an exact divisibility identity. The inspected source records identify no other theorem conditional on these conjectures.

## Gap

The preregistration's literature screen found no target-specific settlement in the inspected OEIS records, arXiv searches, Zenodo records, MathOverflow searches or related integrality literature. Heninger, Rains and Sloane's fixed-root criteria concern different series. OpenAlex and Semantic Scholar were rate-limited, and unrestricted discovery was incomplete. Completeness and independent priority are `ASSUMED-UNVERIFIED`. There is no source arXiv identifier, identified journal paper or DOI for these OEIS records.

## Route

The private helpers `slope_closed` and `slope_nonzero` establish the coefficient slope. `pow_change_minus` applies the imported `LinearExponentDyadicSupport.pow_change`; `sum_change` sums its power differences. `last_divisibility` specializes the integer power-coefficient divisibility supplied by `HannaA181070Integrality.coefficientDivisibility` to the three allowed cutoffs. `cleared_spec` clears the remaining factorials. `source_exists` applies `PowerSeriesNormalizedContraction.exists_unique_fixed` to the integer coefficient operator, with strict prefix agreement established by `step_contract`. `source_unique` uses the same fixed-point owner over the rationals. `all_for_cutoff` combines the two conclusions. `translate_source` and `translate_integral` implement $A=B+1$ for the third source.

The direct imports are `LinearExponentDyadicSupport`, `PowerSeriesNormalizedContraction`, `UnitReversionSquareParity` (whose `Agree` describes prefix agreement), `HannaLogarithmicPowerClosure` (whose `IntegralSeries` expresses integer coefficients), and `HannaA181070Integrality` (whose `coefficientDivisibility` supplies the integer divisibility). These names designate mathematical owners, rather than additional claims of this delivery.

## Falsifier

A source mismatch would include changing the inclusive endpoint, the square exponent, the factorial denominator, either initial coefficient or the third source's translation. Finite prefix agreement alone cannot prove the all-degree claim. Positivity, asymptotic growth, global analytic convergence, and unrestricted replacement cutoffs or exponents are outside the result.

## Evidence

The settling GID is `D5/S1/Recurrence/Algebraic/HannaSquareExponentIntegrality.result`. Its Scribe displays the full six-conjunct claim and acknowledges the [source note](../Library/ArithUnits/hanna2021a350410family.md). The only public theorem is `result`; the more general cutoff and uniqueness statements are private helpers on its compiled proof path.

Experiment: [immutable program and data](https://github.com/the-omega-institute/trureturing-experiments/tree/3e1d776b280735532b3ec74064a3400a04dcdfad/docs/reports/hanna350410-square-exponent-integrality). Executed command: `git -C /Users/auric/trureturing-experiments show 3e1d776b280735532b3ec74064a3400a04dcdfad:docs/reports/hanna350410-square-exponent-integrality/check.py | python3` with shell `pipefail`, exit 0. Script SHA-256: `2ae06627f32d7a1b359dfd49d927c62feb31de9ad056d20cd19a40cbfb5cd8a8`; result `ALL_CHECKS_OK`. The computation uses exact integer and rational arithmetic. Its tested scope is given below; it supplies no universal proof.

The escape audit of `D5.S1.Recurrence.Algebraic.HannaSquareExponentIntegrality.result` is unfinished and tracked in [#27346](https://github.com/the-omega-institute/trureturing/issues/27346). No Reg source is delivered. Missing evidence is a faithful reconstruction of the full six-conjunct source family, an enrolled readout and whole-family intervention/sensitivity evidence. No validated registration is claimed.

## Triage

### What the settlement shows

1. **Proved in prose:** the mechanism is a nonzero rational coefficient slope and exact integer divisibility of the sole factorial denominator not cleared by $(M-1)!$. For $M\ge2$, $m^2/m!=1/(m-1)!+1/(m-2)!$ makes the alternating derivative sum telescope to $S'_M(-1)=(-1)^{M-1}/(M-1)!\ne0$. If $c=[x^n]F^{M^2}$ and $d=[x^{n-1}]F^{M^2-1}F'$, differentiation gives $nc=M^2d$. For $M=n$, $c=Md$; for $M=n+1$, $c=M(c-Md)$; for $M=2n$, $c=M(2d)$. Thus $M\mid c$, while $m!\mid(M-1)!$ for $m<M$. These identities give the unique integral next coefficient. This derivation explains the mechanism; the source claim itself is kernel-checked by `result`.
2. **Proved, kernel-checked:** the proof applies to every cutoff function choosing independently at each $n\ge2$ one of $n$, $n+1$ and $2n$. The choice need not be uniform in $n$. Evidence: private `all_for_cutoff`, whose full hypothesis quantifies over each degree, on `result`'s proof path.
3. **Proved, kernel-checked:** uniqueness of a normalized rational source needs only $M(n)\ge1$ for $n\ge2$. Evidence: private `source_unique`. Integrality uses the stronger three-case hypothesis of private `all_for_cutoff`; no arbitrary-cutoff integrality follows.
4. **Computed:** the experiment matches the first twelve coefficients including degree zero for A350410 and A350411, and the ten supplied positive-degree coefficients for A350412. It gives the first twelve positive-degree coefficients of A350412, checks each defining equation and each last-numerator divisibility for $n=2,\ldots,13$ in all three cutoffs (twelve checks per cutoff), and exits 0 with `ALL_CHECKS_OK`. Evidence: the experiment command and SHA-256 in Evidence. These finite readings are not the universal proof.
5. **Open:** integrality for arbitrary other cutoff schedules or arbitrary replacement exponents is not settled. No positivity, asymptotic growth or global analytic convergence assertion is made. No further source result depending on these conjectures was identified in the inspected records.

## ASSUMED-UNVERIFIED

Literature completeness and independent priority remain `ASSUMED-UNVERIFIED`. The source and literature checks attributed to the orchestrator are recorded in #27303. The unfinished escape audit is tracked in #27346 and is separate from the kernel-checked settlement. No conclusion about uninspected publications follows from the bounded screen.
