---
slug: oeis-a301420-positive-newton-sums
bibkey: wojnar2018a301420
doi: null
url: https://oeis.org/A301420
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums.result
---

# A301420: positive monomial coefficients for five data

## Problem

Gregory Gerard Wojnar's [OEIS A301420](https://oeis.org/A301420), NAME and COMMENTS, defines the sequence by:

> for a family of 5 data, the sum of the positive coefficients in these polynomials is a(n).

The FORMULA field states:

> G.f.: (-x*(x+1)^4+1)/(x^6+4*x^5+5*x^4-5*x^2-6*x+1); this denominator equals (1-x)*(2-(x+1)^5) (conjectured).

It also states:

> a(n+14) = 7*a(n+13) - a(n+12) - 6*a(n+11) + 2*a(n+10) - a(n+9) + 4*a(n+8) + a(n+7) + 4*a(n+5) + 2*a(n+4) - a(n+3) - 5*a(n+2) - 4*a(n+1) - a(n) (conjectured).

The source snapshot is A301420 revision #28; the full generating-function conjecture occurs in revision #2 and the recurrence is explicitly conjectural in revision #16. The published offset is 1,2. The shift and the universal recurrence domain $n\ge1$ are explicit interpretations accepted in [#23723](https://github.com/the-omega-institute/trureturing/issues/23723), rather than printed source quantifiers. The [Library note](../Library/RecurrenceComposition/wojnar2018a301420.md) gives the source and coefficient normalization.

For $k\ge1$ and $m=(m_1,\ldots,m_5)\in\mathbb N_0^5$ of weighted degree $\sum_{i=1}^5 i m_i=k$, put $r=\sum_i m_i$ and define

$$
c_m=\frac{k}{5r}(-1)^{k+r}\frac{r!}{\prod_i m_i!}\prod_{i=1}^5\binom5i^{m_i},\qquad
a(k)=\sum_{\sum i m_i=k,\ c_m>0}c_m.
$$

These are definitions, using equation (2) of Wojnar, Wojnar and Brin, [arXiv:1706.08381v2](https://arxiv.org/abs/1706.08381v2), pp. 3–4. Each distinct monomial contributes separately, before substituting data values. No $a(0)$ is defined.

The exact target is the conjunction of the rational identity

$$
F(X)=\sum_{k\ge1}a(k)X^{k-1}
=\frac{1-X(1+X)^4}{(1-X)(2-(1+X)^5)}\quad\text{in }\mathbb Q[[X]]
$$

and the displayed recurrence for every integer $n\ge1$.

### Statement echo

| Source clause | Formal counterpart | Scope |
| --- | --- | --- |
| Five distinct variables and weights 1 through 5 | `Multiplicity`, `count`, `degree`, `multiplicities` | All nonnegative multiplicity vectors of a fixed weighted degree, each once. |
| Normalized Girard–Waring coefficient | `literalCoefficient` | The displayed factorial, binomial and sign factors. |
| Sum of positive coefficients | `positiveCoefficient` | Strict per-monomial positivity, before valuation. |
| Offset-one generating function | `positiveSeries`, first conjunct of `result` | Coefficient at degree $j$ is $a(j+1)$. |
| Printed recurrence | `recurrence`, second conjunct of `result` | Every positive index, with all signs and coefficients as printed. |

## Motivation

The conjecture relates an unbounded monomial positivity filter to a rational formal series. A coefficient table cannot establish this relation or its all-index recurrence.

## Gap

A301417 revision #42 supplies the normalized elementary-symmetric variables. A301420 revision #28 and A302764 revision #15 were inspected in the source authentication recorded in #23723. A302764 asserts the same whole-family numerator and denominator, including five data; the inspected passages contain no proof or proof reference. That assertion is disclosed as prior knowledge of the formula, not counted as a new formula prediction.

The recorded bounded arXiv metadata search authenticated 1706.08381v2 but did not constitute a global full-text search. Primary paper coverage includes pp. 3–4, 14 and 23 and keyword passages, not the entire paper. No prior whole proof was identified within that inspected scope. Global proof novelty and continued external open status are ASSUMED-UNVERIFIED. The coefficient formula is the formal sequence definition; a separate theorem identifying it with a roots-based polynomial presentation is not claimed.

## Route

Set $P=(1+X)^5-1$ and use the formal logarithm $\log(1+X)$. Multinomial expansion groups multiplicity vectors by their factor count. For each positive degree, the coefficients of $-\log(1-P)/5$ aggregate unsigned weights, while those of $-\log(1+P(-X))/5$ aggregate signed weights. The identity $2\max(c,0)=|c|+c$ converts their derivatives into the shifted positive-coefficient series.

Formal logarithmic differentiation gives the two derivative equations; cancellation and combination yield the rational identity. The recurrence annihilator factors as the displayed denominator times $1-X+X^3-X^4+X^5+X^8$. Its product with $F$ has degree at most thirteen, so coefficient extraction at degree $n+13$ gives the printed recurrence for every $n\ge1$.

## Falsifier

A discrepancy between the displayed literal coefficient sum and either formal identity at any allowed index would contradict `result`. A different normalization, valuation before coefficient filtering, an index-zero value or a roots-based interpretation without its bridge lies outside this exact event.

## Evidence

`D5.S3.Combinatorics.PowerSeries.PositiveNewtonSums.result` proves both conjuncts. Its admission basis is `open-problem-resolution (#23723; Proved)`, its generality is G, and its utility is none. The live derivation uses the all-degree multinomial/logarithm bridge, not a finite cutoff or an assumed generating function. The public definitions are definitions and are mirrored as such.

The same-delivery Reg mirror compiles a dependent source-family registration attempt retaining the sequence readout and both laws. Its four-slot binding is unfinished: [#23747](https://github.com/the-omega-institute/trureturing/issues/23747). The current scoped producer records `declared_unresolved`, `IE-C050 ClosedTruthReadout`, `source.residual_requires_open`, with a null certificate and continuation `.unknown`. This is not a validated registration. Delivery uses CLAUDE §3.9's linked-issue exception.

## Triage

| Item | Status and evidence kind | Scope |
| --- | --- | --- |
| Registered literal-coefficient generating function | Proved, kernel-checked `D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums.result` | Exact shifted series in $\mathbb Q[[X]]$, all positive degrees. |
| Registered order-fourteen recurrence | Proved, kernel-checked the same `result` | Every $n\ge1$, with the printed signs, missing degree-six term and constants unchanged. |
| Mathematical mechanism | Proved, kernel-checked private `unsigned_log_bridge`, `signed_log_bridge`, `positive_series_bridge`, `rational_equation`, `annihilated`, `recurrence_proof` in the same module | Multinomial extraction, sign splitting, formal differentiation and coefficient annihilation. |
| Source interpretation and prior formula | Literature reading and declared interpretation | Named revisions and accepted offset/domain interpretations above; A302764 is a bare prior assertion in the inspected source. Global proof novelty remains open. |
| Four-slot Reg audit | Open, current scoped producer and #23747 | `declared_unresolved`; no certificate or `declared_validated` claim. |

### What the settlement shows

The kernel-checked `result` establishes the complete registered conjunction for the literal five-data coefficient definition. The mechanism removes the positivity filter through signed and unsigned logarithmic aggregates. The proof applies to every positive index and requires no simple-root hypothesis or finite bound.

A parameter-family extension, a formal bridge to roots-based polynomial presentations, the asymptotic ratio, the whole A301420 entry and companion A301421 remain outside the theorem. No additional source claim depending on this conjunction has been established here. The A302764 family assertion does not by itself provide a formally proved extension. No additional problem credit follows from these related statements.

## ASSUMED-UNVERIFIED

Global literature completeness, global proof novelty, continued external open status and the bridge from the chosen literal formula to any alternative roots-based presentation. The accepted shift and positive recurrence domain are stated interpretations. The four-slot Reg audit remains unfinished under #23747. This dossier supplies no strict research settlement or solved-problem KPI credit.
