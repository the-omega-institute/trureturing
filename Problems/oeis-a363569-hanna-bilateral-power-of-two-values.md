---
slug: oeis-a363569-hanna-bilateral-power-of-two-values
bibkey: hanna2023bilateral
doi: null
url: https://oeis.org/A363569
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/HannaBilateral/OeisA363569PowerOfTwo.result
---

# Hanna's A363569 power-of-two coefficient formula

## Problem

Paul D. Hanna's [OEIS A363569](https://oeis.org/A363569) states:

> Expansion of g.f. A(x) = Sum_{n=-oo..+oo} x^n * (i + x^n)^(2*n), where i^2 = -1.

> a(2^n) = 1 for n > 0 (conjecture).

The binding coefficient convention and the exact claim are in [#18665](https://github.com/the-omega-institute/trureturing/issues/18665). Values are complex, and the bilateral expression is interpreted coefficientwise as finite sums of formal power-series coefficients.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Expansion of g.f. A(x) = Sum_{n=-oo..+oo} x^n * (i + x^n)^(2*n), where i^2 = -1. | `coeffA` in `D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo`; the source sequence `a` | Literal preregistered finite coefficient expression; complex formal power series, natural coefficient degree. |
| a(2^n) = 1 for n > 0 (conjecture). | `D5.S1.Recurrence.HannaBilateral.OeisA363569PowerOfTwo.claim` and `D5.S1.Recurrence.HannaBilateral.OeisA363569PowerOfTwo.result` | Every source quantifier and range is retained; `result` proves the entire claim. |
| Sequence parameter | `a` | $c=2,3,\sqrt{2},i$ for A363558, A363559, A363561, A363569, respectively. |
| Complex codomain and natural arithmetic | The types in `claim` | Integer expressions are cast to complex numbers; the half exponent in the two relevant prime formulas uses natural division. This is the binding convention, not an extra hypothesis. |

## Motivation

This tier-1 problem is preregistered as [#18665](https://github.com/the-omega-institute/trureturing/issues/18665). The settling declaration is `D5/S1/Recurrence/HannaBilateral/OeisA363569PowerOfTwo.result`; its Scribe carries this dossier's sole `OpenProblemResolutionClaim(Proved)`. The form is `deposit-uncovered`, with no atom or coverage edge. Admission basis: `open-problem-resolution (#18665; Proved)`; `generality: I`; `utility: none`.

## Gap

The preregistrations #18659–#18666 record readings of A363558, A363559, A363561 and A363569 and the related A260147 entry. Their literature screen names the Epoch OEIS benchmark, AlphaProof Nexus results, formal-conjectures, and Fried's papers arXiv:2410.07237, 2606.09913 and 2607.24832. No proof was found in that searched scope. Literature-screen completeness is ASSUMED-UNVERIFIED.

## Route

For positive degree $m$, the coefficient splits into sums over divisors, as proved by private `coeffA_divisors`. The positive divisor $n$ contributes $c^{2n-(m/n-1)}\binom{2n}{m/n-1}$. The negative divisor $k$ contributes $(-c)^{m/k-(2k-1)}\binom{m/k}{2k-1}$ when $2k-1\le m/k$, and zero otherwise.

At $m=2^N$ and $0\le i<N$, pair $n=2^i$ with $k=2^{N-1-i}$. Then $m/n=2k$ and $m/k=2n$. The two binomial coefficients are identical, while the common exponent $2n-2k+1$ is odd whenever that coefficient can be nonzero. Private `vals_pair` gives cancellation, including the zero-binomial case. The largest positive divisor contributes $c^{2^{N+1}}$; its negative counterpart vanishes. Public `coeffA_pow_two` states the resulting identity.

For prime $p>3$, the divisors are $1,p$. The positive term at $1$ vanishes because $p-1>2$, the positive term at $p$ contributes $c^{2p}$, the negative term at $1$ contributes $p c^{p-1}$ because $p-1$ is even, and the negative term at $p$ vanishes. Public `coeffA_prime` states this identity. The eight `result` theorems specialize these identities to the source parameters and normalize their powers.

## Falsifier

An index in the source range whose coefficient differs from the displayed formula would contradict `D5.S1.Recurrence.HannaBilateral.OeisA363569PowerOfTwo.result`. The claim refers to the explicitly defined coefficient sequence, so it makes no existence assumption about an analytic series.

## Evidence

- Lean: `D5/S1/Recurrence/HannaBilateral/OeisA363569PowerOfTwo.lean`; settling theorem `D5.S1.Recurrence.HannaBilateral.OeisA363569PowerOfTwo.result`.
- Blueprint: `Blueprint/D5/S1/Recurrence/HannaBilateral/OeisA363569PowerOfTwo.md`; source: `Library/RecurrenceComposition/hanna2023bilateral.md`.
- Every delivered theorem has `proof_shape: bind-only`, `escape_witness: none` after expansion. The exact external settlements supply admission; no escape-witness admission is asserted.
- All direct D5 dependencies are from this same delivery. There are no protected-base frozen dependencies, owner publications or owner re-pins.
- The four-slot escape audit is unfinished for the ten public theorems: [#19885](https://github.com/the-omega-institute/trureturing/issues/19885). A faithful source reconstruction, equivalence bridge, actual observational dependence and whole-family variation/sensitivity evidence for the guarded infinite coefficient families have not been compiled. No `declared_validated` status is asserted.

### Declaration classification

| Module | Declaration | proof_shape | escape_witness | Direct consumers | Direct frozen dependencies |
| --- | --- | --- | --- | --- | --- |
| OeisA363558PowerOfTwo | `D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo.coeffA` | definition | none | `D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo.a`, `D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo.coeffA_divisors`, `D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo.coeffA_pow_two`, `D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo.coeffA_prime`, `D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo.result`, `D5.S1.Recurrence.HannaBilateral.OeisA363558Prime.result`, `D5.S1.Recurrence.HannaBilateral.OeisA363559PowerOfTwo.a`, `D5.S1.Recurrence.HannaBilateral.OeisA363559PowerOfTwo.result`, `D5.S1.Recurrence.HannaBilateral.OeisA363559Prime.result`, `D5.S1.Recurrence.HannaBilateral.OeisA363561PowerOfTwo.a`, `D5.S1.Recurrence.HannaBilateral.OeisA363561PowerOfTwo.result`, `D5.S1.Recurrence.HannaBilateral.OeisA363561Prime.result`, `D5.S1.Recurrence.HannaBilateral.OeisA363569PowerOfTwo.a`, `D5.S1.Recurrence.HannaBilateral.OeisA363569PowerOfTwo.result`, `D5.S1.Recurrence.HannaBilateral.OeisA363569Prime.result` | none |
| OeisA363558PowerOfTwo | `D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo.coeffA_pow_two` | bind-only | none | `D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo.result`, `D5.S1.Recurrence.HannaBilateral.OeisA363559PowerOfTwo.result`, `D5.S1.Recurrence.HannaBilateral.OeisA363561PowerOfTwo.result`, `D5.S1.Recurrence.HannaBilateral.OeisA363569PowerOfTwo.result` | none |
| OeisA363569PowerOfTwo | `D5.S1.Recurrence.HannaBilateral.OeisA363569PowerOfTwo.a` | definition | none | `D5.S1.Recurrence.HannaBilateral.OeisA363569PowerOfTwo.claim`, `D5.S1.Recurrence.HannaBilateral.OeisA363569PowerOfTwo.result`, `D5.S1.Recurrence.HannaBilateral.OeisA363569Prime.claim`, `D5.S1.Recurrence.HannaBilateral.OeisA363569Prime.result` | none |
| OeisA363569PowerOfTwo | `D5.S1.Recurrence.HannaBilateral.OeisA363569PowerOfTwo.claim` | definition | none | `D5.S1.Recurrence.HannaBilateral.OeisA363569PowerOfTwo.result` | none |
| OeisA363569PowerOfTwo | `D5.S1.Recurrence.HannaBilateral.OeisA363569PowerOfTwo.result` | bind-only | none | settling result | none |

### Experiment

[Exact symbolic and arithmetic checker](https://github.com/the-omega-institute/trureturing-experiments/tree/1133ccd5c01a70de0997056d1ec6bdbb3c8b6a32/docs/reports/oeis-a363558-a363559-a363561-a363569-bilateral-power-sums), commit `1133ccd5c01a70de0997056d1ec6bdbb3c8b6a32`. Command in that directory: `python3 check.py 300 12`; exit 0. Script SHA-256: `b39e40018fd0826204c5ecc5d01373129e88b32b0b1556b44e8631c2b0431c04`. The divisor formula agrees with direct symbolic expansion through degree 14, the A363558 and A363569 source data agree, the dyadic identity holds symbolically for $1\le N\le12$, and the prime identity holds symbolically for $5\le p\le300$. Explicit checks of the four source parameters cover primes $5\le p<60$. These are computed finite readings.

## Triage

| Target item | Status | Evidence |
| --- | --- | --- |
| Exact source settlement #18659 (OeisA363558PowerOfTwo) | Proved, kernel-checked | `D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo.result`. |
| Exact source settlement #18660 (OeisA363558Prime) | Proved, kernel-checked | `D5.S1.Recurrence.HannaBilateral.OeisA363558Prime.result`. |
| Exact source settlement #18661 (OeisA363559PowerOfTwo) | Proved, kernel-checked | `D5.S1.Recurrence.HannaBilateral.OeisA363559PowerOfTwo.result`. |
| Exact source settlement #18662 (OeisA363559Prime) | Proved, kernel-checked | `D5.S1.Recurrence.HannaBilateral.OeisA363559Prime.result`. |
| Exact source settlement #18663 (OeisA363561PowerOfTwo) | Proved, kernel-checked | `D5.S1.Recurrence.HannaBilateral.OeisA363561PowerOfTwo.result`. |
| Exact source settlement #18664 (OeisA363561Prime) | Proved, kernel-checked | `D5.S1.Recurrence.HannaBilateral.OeisA363561Prime.result`. |
| Exact source settlement #18665 (OeisA363569PowerOfTwo) | Proved, kernel-checked | `D5.S1.Recurrence.HannaBilateral.OeisA363569PowerOfTwo.result`. |
| Exact source settlement #18666 (OeisA363569Prime) | Proved, kernel-checked | `D5.S1.Recurrence.HannaBilateral.OeisA363569Prime.result`. |
| For every complex $c$ and $N>0$, $\operatorname{coeffA}(c,2^N)=c^{2^{N+1}}$ | Proved, kernel-checked | `D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo.coeffA_pow_two`. |
| For every complex $c$ and prime $p>3$, $\operatorname{coeffA}(c,p)=p c^{p-1}+c^{2p}$ | Proved, kernel-checked | `D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo.coeffA_prime`. |
| Positive and negative divisor terms cancel at dyadic complementary indices; the largest positive divisor remains | Proved, kernel-checked | Private `vals_pair` and `dyadic_quotients`, used in `coeffA_pow_two`. |
| Prime indices retain two endpoint contributions | Proved, kernel-checked | `coeffA_prime` evaluates the two divisors using `Nat.Prime.divisors`. |
| Arbitrary complex parameter; $N>0$ and primality with $p>3$ retained | Proved, kernel-checked | The complete telescopes of the two generic theorems. |
| Formal power-series coefficients; no analytic-convergence claim | Scope of the definitions | `coeffA` uses finite coefficient sums in complex formal power series. |
| The inverse-series coefficient already uses $\binom{q}{2k-1}$; odd signs and zero binomials handle the cancellation | Proved, kernel-checked | Private `coeff_neg_mul` and `vals_pair`, using `PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos`, `Odd.neg_pow` and `Nat.choose_eq_zero_of_lt`. |
| Symbolic and numerical finite check | Computed | The pinned experiment above, with exactly its stated ranges. |
| Literature completeness and originality | Open: ASSUMED-UNVERIFIED | The scope-limited source and literature screen recorded in the eight preregistrations. |

### What the settlement shows

**Proved, kernel-checked:** `D5.S1.Recurrence.HannaBilateral.OeisA363569PowerOfTwo.result` settles the exact source formula. The two generic identities in `D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo` hold for every complex parameter. Their decisive mechanisms are complementary dyadic divisor cancellation and the two-divisor description of a prime.

**Proved in prose from the coefficient definition:** at degree one the coefficient is $c^2+1$, from the positive divisor $1$ and negative divisor $1$. Thus the dyadic formula cannot include $N=0$. At degree three it is $c^6+3c^2+1$: the positive divisor $1$ supplies the extra $1$. Thus the stated generic prime formula cannot include $p=3$. These boundary calculations are mathematical derivations, not separately asserted Lean theorems.

**Scope:** the eight source formulas are the settlement scope. No analytic convergence, new originality claim, or settlement of the related A260147 identity follows. Claims in other source entries require their own hypotheses and evidence.

## ASSUMED-UNVERIFIED

Literature completeness, first-publication priority and the informal source's identification with the explicit formal coefficient convention are outside the Lean kernel conclusion. The finite experiment does not prove an unbounded identity. The four-slot escape audit remains unfinished under #19885.
