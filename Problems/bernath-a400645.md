---
slug: bernath-a400645
bibkey: oeis2026a400645
doi: null
url: https://oeis.org/A400645
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/OEISA400645.result
---

# Bernáth's OEIS A400645 consecutive-ratio conjecture

## Problem

Bence Bernáth's OEIS A400645, revision 21, NAME field states:

> a(n+1) = round(sqrt(a(n)^2 + a(n-1)^2 + a(n-2)^2 - a(n-3)^2)).

The complete conjectural COMMENTS paragraph states:

> Numerical evidence suggests that the ratio of consecutive terms (a(n+1)/a(n)) tends to 1.3122819079... (sqrt(A289917)) which is the largest real root of the asymptotic equation of this sequence: x^8-x^6-x^4-x^2+1. This is related to A116732 where the asymptotic equation is y^4-y^3-y^2-y+1 via y=x^2.

The Mathematica initialization is $a_1=a_2=a_3=0$, $a_4=1$. Subtraction in the radicand is signed integer subtraction. The recurrence applies for $n\ge4$; index zero is unused. Set

$$r=\frac{1+\sqrt{13}+\sqrt{2\sqrt{13}-2}}4,\qquad \alpha=\sqrt r.$$

The assertion is existence of a natural-valued source sequence and, for every such sequence, eventual positivity and $a_{n+1}/a_n\to\alpha$, together with $\alpha^8-\alpha^6-\alpha^4-\alpha^2+1=0$ and maximality among all real roots.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Signed four-square radicand | `radicand` | Exact integer expression; predecessor indices use natural subtraction. |
| Four initial values and nearest rounding | `IsSourceSequence` | Exact values, $n\ge4$, nonnegative radicand and integer rounding equality. |
| A289917 radical and its square root | `squaredLimit`, `limitingRatio` | Exact radicals. |
| Consecutive-ratio convergence | `claim`, `result` | Universal epsilon statement, positive denominator and a natural threshold at least four. |
| Largest real octic root | `claim`, `result` | Equation and upper bound for every real root. |
| Nonvacuity and defined square root | Existence conjunct and radicand nonnegativity | Explicit domain conditions; neither assumes the desired limit. |

Names in this dossier without an owner prefix belong to `D5.S1.Recurrence.OEISA400645`. The positive-index convention and the five public definition bodies agree with the preregistered binding conventions in #22857.

## Motivation

This is the external tier-1 problem preregistered in https://github.com/the-omega-institute/trureturing/issues/22857. The settlement is **Proved**, on `D5/S1/Recurrence/OEISA400645.result`, with `admission_basis: open-problem-resolution (#22857; Proved)`, generality I and utility none. There is no digestion atom. The Scribe resolution claim names this dossier and this settling declaration.

## Gap

The source reports numerical evidence. A finite prefix or the homogeneous characteristic polynomial alone does not imply the infinite ratio law for a rounded, forced recurrence. The proof controls the entire rounding-error tail and excludes a zero dominant coefficient.

The bounded literature assessment is the one in #22857: OEIS source/history, arXiv, zbMATH, OpenAlex, MathDB, journal/formalization corpora and repository searches did not identify a settlement of this exact signed recurrence in the inspected scope. Its completeness is **ASSUMED-UNVERIFIED**. The related Sirvent article, DOI `10.1051/ita/2026034`, was available only as metadata and abstract in that assessment; its full text remains unread. A400644 has three positive squares and different initial data, so its existing theorem does not settle this problem.

## Route

`seq_spec` constructs a source sequence and `source_unique` identifies every source sequence at positive indices. Monotonicity gives positivity and the Fibonacci upper bound. The growth scale $s=5/3$ is strictly smaller than $r>17/10$.

Writing $b_n=a_{n+23}^2$, the signed forcing is $e_n=b_{n+4}-b_{n+3}-b_{n+2}-b_{n+1}+b_n$. Its absolute value is bounded by $4a_{26}s^n$. The projection

$$T_n=b_{n+3}+(r-1)b_{n+2}+(r^2-r-1)b_{n+1}-b_n/r$$

satisfies $T_{n+1}=rT_n+e_n$ and $T_n>(7/17)b_{n+3}$. The exact seed $a_{26}=324$ and $r-s>1/30$ give a normalized projection limit $U>73872/17>0$. The weighted three-coordinate contraction gives $b_n/r^n\to L>0$. Division of successive normalized squares and continuity of the square root yield the ratio law.

The proof directly reuses `OEISA400644.sourceRound`, its published `sourceRound_round` and `sourceRound_ge_sqrt`; the beta-thirteen algebraic declarations; and `ComplementaryGoldenRatioLimit.vanishing_affine_error`. It adds no rounding owner. The companion A400644 source changes only by publication of its existing rounding identity and its mirror.

## Falsifier

A source sequence violating the epsilon-limit clause, or a larger real root of the octic, would contradict `result`. A finite prefix is not a falsifier or certificate for the infinite limit. A prior published settlement of this exact statement would change the novelty assessment without changing the kernel-checked theorem.

## Evidence

The Lean source is `D5/S1/Recurrence/OEISA400645.lean`, with its Scribe and emitted mirror under `Blueprint/D5/S1/Recurrence/`. The designated theorem is `result : claim`; its assertion includes existence, convergence and largest-root maximality.

The independent finite checker is [the experiments directory at commit 9cfc9a4c03fadd43487edc9fb74b7b753fea6d3f](https://github.com/the-omega-institute/trureturing-experiments/tree/9cfc9a4c03fadd43487edc9fb74b7b753fea6d3f/docs/reports/oeis-a400645-rounded-norm-ratio). File `check.py` has SHA-256 `20c3145f200623eb7391931d874188e0849f111bfec84370212d01bcd3a00a10`. Executing its exact committed bytes with `python3 /Users/auric/.sshx/2991fcd1903d7c7b9748d64b/attempt-1/experiment-check.py` exits 0 and ends in `ALL_CHECKS_OK`.

Its scope is the 51 source terms; recurrence, positivity, midpoint and error checks for $4\le n\le4095$; 263965 relative-envelope checks with $4\le m\le4096$ and $0\le k\le\min(64,4096-m)$; exact algebraic and projection identities; tail-envelope checks for $0\le j\le4069$; and a rational ratio enclosure for $128\le n\le4095$. These are computed finite/algebraic results, independent of the infinite-limit proof.

Escape registration is unfinished for `OEISA400645.result` and the newly public `OEISA400644.sourceRound_round`: https://github.com/the-omega-institute/trureturing/issues/24271. No declared_validated registration is asserted. The missing typed source-selection/reconstruction and intervention/sensitivity evidence are identified there.

## Triage

### What the settlement shows

| Item | Status | Evidence kind and scope |
| --- | --- | --- |
| A real three-step recurrence with vanishing forcing and coefficient absolute values bounded by $1/2$, $1/5$, $1/8$ tends to zero. | proved | Kernel-checked private `stable_three`, consumed by `square_asymptotic`. |
| The signed fourth lag preserves monotonicity for this source; all terms from index four are positive. | proved | Kernel-checked private `source_mono` and `source_pos`. |
| For every $m\ge4$ and $k\ge0$, $a_{m+k}\le2a_m(5/3)^k$. | proved | Kernel-checked private `source_growth`. |
| The normalized dominant projection has limit $U>73872/17$; normalized squares have a positive limit, yielding the ratio law. | proved | Kernel-checked private `dominant_limit`, `square_asymptotic`, `ratio_limit`, and public `result`. |
| The source radical is the largest real root of the stated octic. | proved | Kernel-checked private `algebraic_clauses` and public `result`. |
| The independent checker reproduces the 51 source terms and ends in `ALL_CHECKS_OK`. | computed | Exact committed experiment, command, exit 0, SHA-256 and finite scopes given in Evidence. |
| A general theorem for arbitrary initial seeds or other signed rounded recurrences. | open | Requires separate monotonicity, spectral-gap and positive-projection hypotheses. |
| Optimal seed thresholds, sharper rates and an $O((5/3)^n)$ remainder. | open | The proof establishes the exact limit; none of these stronger quantitative assertions is delivered. |

The decisive mechanism is a rounding-error growth scale below the dominant squared-sequence root and a strictly positive infinite-tail projection certificate. The abstract stability helper extends to the coefficient box stated in its row; the source-specific positivity and seed arguments do not establish a theorem for arbitrary seeds. No other source result is asserted to follow from this settlement, and the source's other results or dependent claims remain outside the delivered theorem.

## ASSUMED-UNVERIFIED

Literature completeness, the unread full text of Sirvent's related article, and the absence of unpublished settlements remain unverified. Escape registration remains unfinished under #24271. General seeds, other signed recurrences, optimal thresholds and quantitative remainders remain open. The finite experiment does not certify any unbounded convergence claim.
