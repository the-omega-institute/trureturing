---
slug: hanna365771-mod5
bibkey: hanna2023a365771
doi: null
url: https://oeis.org/A365771
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/HannaA365771
  - D5/S1/Recurrence/Residue/HannaA365771Two
  - D5/S1/Recurrence/Residue/HannaA365771Zero
---

# Hanna's three congruences for A365771

## Problem

OEIS A365771, revision 23, defines
$a(n)=\binom{2n+1}{n}/(2n+1)\cdot\binom{3n-1}{n}$ for $n\geq0$ and states:

> Conjectures: given A033042 is the sums of distinct powers of 5, then
> (1) a(5*A033042(n)) == 4 (mod 5) for n > 0,
> (2) a(5*A033042(n) + 1) == 2 (mod 5) for n > 0,
> (3) a(n) == 0 (mod 5) for n > 0 except when n or n-1 equals 5*A033042(k) for some k >= 0.

The problem is preregistered in [#18656](https://github.com/the-omega-institute/trureturing/issues/18656).
The three settlements are Proved. For every positive sum $m$ of distinct powers of five,
$a(5m)\equiv4\pmod5$ and $a(5m+1)\equiv2\pmod5$. For every positive $n$ outside
$n=5m$ or $n-1=5m$ with $m$ a sum of distinct powers of five (including zero), $a(n)\equiv0\pmod5$.
The companion statements are preregistered in [#18657](https://github.com/the-omega-institute/trureturing/issues/18657)
and [#18658](https://github.com/the-omega-institute/trureturing/issues/18658).

### Statement echo

| Source clause | Formal counterpart | Fidelity |
| --- | --- | --- |
| The formula for $a(n)$, including $n=0$ | `HannaA365771.a` | Literal natural-number binomial quotient and product; subtraction is truncated. |
| “Sums of distinct powers of 5.” | `HannaA365771.InA033042` | Every digit of `Nat.digits 5 m` is at most one, including the empty digit list at zero. |
| “for n > 0” in the enumeration | The positive-value hypothesis in `HannaA365771.claim` | A033042 starts at zero, so the positive enumeration indices select exactly its positive values. |
| Residue four at five times the selected value | `HannaA365771.result` | Proves the full `claim`, with no extra hypothesis. |

Unqualified formal names in this dossier belong to `D5.S1.Recurrence.Residue.HannaA365771`.
The companion settling declarations are `D5.S1.Recurrence.Residue.HannaA365771Two.result`
and `D5.S1.Recurrence.Residue.HannaA365771Zero.result`; their claims retain the positive-$m$
restriction for (2) and the negated existential, including $m=0$, for (3).
Natural division agrees with the displayed quotient because the first factor is an integer Catalan number.

## Motivation

The first congruence is one part of a complete base-five description of this Catalan-binomial sequence.
The settling declaration is `D5/S1/Recurrence/Residue/HannaA365771.result`.
Its source is acknowledged in `Library/Digit/hanna2023a365771.md`.

## Gap

The source labels the congruence a conjecture. The literature screen recorded in #18656 found no settlement in the
OEIS entries, the Epoch OEIS Open benchmark, AlphaProof Nexus results, the formal-conjectures repository,
or Fried's papers arXiv:2410.07237, 2606.09913 and 2607.24832. Search completeness is `ASSUMED-UNVERIFIED`.

## Route

Write $M(n)=\binom{3n}{n}\binom{2n}{n}$ as mathematical shorthand.
The private `lucas5` applies Mathlib's `Choose.choose_modEq_choose_mod_mul_choose_div_nat`.
The private `M_step_good` and `M_step_bad` analyze the last digit, and `M_mod` uses strong induction
through division by five to obtain the full digit indicator, including zero.
For positive $n$, the private `a_balance` proves $3(n+1)a(n)=2M(n)$.
Its private Catalan helper uses `Nat.succ_dvd_centralBinom` and `Nat.choose_mul_succ_eq`.
If the last digit is four, the private `a_mod_four` obtains zero directly from Lucas decomposition
of $\binom{3n-1}{n}$; otherwise the balance identity determines the residue.
The resulting public `residue_classification` gives `result` after appending a zero digit.
The valuation comparison from the source's explanation is unnecessary for this proof.

## Falsifier

A positive $m$ with all base-five digits at most one and $a(5m)\bmod5\ne4$ would falsify the source claim.
A mismatch between the natural-number definitions and the quoted source would invalidate the formal correspondence.

## Evidence

The Lean module is `D5/S1/Recurrence/Residue/HannaA365771.lean`; its settling theorem is `result : claim`.
Each of the three Scribe mirrors displays its whole claim and records a Proved resolution.
The companion dossiers are `Problems/hanna365771-mod5-two.md` and `Problems/hanna365771-mod5-zero.md`.
The module's admission basis is `open-problem-resolution (#18656; Proved)` and its utility classification is `none`:
the argument is symbolic and unbounded, with no retained numerical certificate.
The companion modules have admission bases `open-problem-resolution (#18657; Proved)`
and `open-problem-resolution (#18658; Proved)`, respectively, and utility `none`.
The shared module is same-delivery content rather than a previously frozen dependency.

Four-slot escape registration is unfinished for `digits_step`, `residue_classification`, `result`,
`HannaA365771Two.result` and `HannaA365771Zero.result`:
[issue #22018](https://github.com/the-omega-institute/trureturing/issues/22018).
No successful Reg registration is claimed.

### Independent finite computation

Experiment: [oeis-a365771-catalan-binomial-mod-five](https://github.com/the-omega-institute/trureturing-experiments/tree/83566d1f13edd7b294f423fc865cc3cd179bf84e/docs/reports/oeis-a365771-catalan-binomial-mod-five),
script `check.py`, immutable revision `83566d1f13edd7b294f423fc865cc3cd179bf84e`.
Command: `python3 /tmp/op-hanna365771/check.py 6000`.
Exit code: 0. Script SHA-256: `63334973c39e39270e57afc105b332ccb943469dbee57d215bee93c3f9802408`.
The checker reports `RESULT PASS`: agreement with the listed initial data at $0\leq n\leq9$; the scaled identity for $1\leq n<3000$;
the three conjectures on their applicable inputs with $1\leq n\leq6000$; the strict valuation comparison
when a digit is at least two for $1\leq n\leq6000$; and $M(n)\equiv1\pmod5$
for zero/one-digit inputs with $1\leq n\leq6000$.
These are finite computed readings.

## Triage

- **Proved, conjectures (1), (2) and (3):** kernel-checked
  `D5.S1.Recurrence.Residue.HannaA365771.result`,
  `D5.S1.Recurrence.Residue.HannaA365771Two.result` and
  `D5.S1.Recurrence.Residue.HannaA365771Zero.result` prove the three verbatim claims.
- **Proved, complete positive-index classification:** kernel-checked `residue_classification` gives
  $a(n)\bmod5=0$ outside the zero/one-digit set, and on that set gives four when $n\bmod5=0$ and two otherwise,
  for every $n>0$.
- **Proved, multinomial indicator including zero:** the kernel-checked private `M_mod` proves
  $M(n)\bmod5=1$ on the zero/one-digit set and zero off it for every $n\geq0$.
- **Computed, checker scope:** the experiment entry gives exit 0 through $n=6000$ and the scaled identity for
  $1\leq n<3000$, with the pinned script, command and SHA-256 above.
- **Open, further arithmetic:** higher powers of five and other primes have no formal claim here.
  The stronger Kummer valuation comparison is computed only in the stated finite range and has no Lean theorem here.

### What the settlement shows

The decisive invariant is the multinomial digit indicator under division by five, rather than a general
valuation estimate. It combines with the exact balance identity and the separate last-digit-four case to give
all positive-index residues modulo five. The classification supplies both companion results, and also explains residue two at $n=1$; the source's positive-$m$ restriction for (2)
excludes that value. Zero is handled by the indicator theorem but excluded from the classification;
the literal formula gives $a(0)=1$. No other source theorem is invoked through an assumed conjecture.

## ASSUMED-UNVERIFIED

Literature-search completeness and first-publication priority are `ASSUMED-UNVERIFIED`.
The source-to-definition identification is a source reading; kernel verification concerns the Lean statements.
The strict valuation comparison beyond the finite checker range, higher prime powers and other primes remain open here.
