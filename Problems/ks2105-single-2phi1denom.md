---
slug: ks2105-single-2phi1denom
bibkey: kimstanton2021qlommel
doi: 10.48550/arXiv.2105.10096
url: https://arxiv.org/abs/2105.10096v3
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/MotzkinHankel/KimStantonSingleDenominator.result
---

# Kim–Stanton Conjecture 8.4: integer polynomial denominators

## Problem

Kim and Stanton, *Three families of q-Lommel polynomials*, arXiv:2105.10096v3, Section 8, Conjecture 8.4.

Let $R=\mathbb Z[a,b,c,q]$ and $K=\operatorname{Frac}(R)$. The formal series is
$F(A,B;C;q,z)=\sum_{r\ge0}(A;q)_r(B;q)_r z^r/((C;q)_r(q;q)_r)$, where
$(u;q)_r=\prod_{j=0}^{r-1}(1-uq^j)$. Put
$D_n=\prod_{k=0}^n(1-cq^k)^{\lfloor(n+1)/(k+1)\rfloor}$.

Define $\gamma_n=[z^n](F(aq,b;cq;q,z)/F(a,b;c;q,z))$. The assertion is
$\forall n\in\mathbb N\;\exists P_n\in R:\;\gamma_n/(1-c)=P_n/D_n$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| The standard basic hypergeometric series | `KimStantonDenominatorCore.F` and `qShiftedFactorial` | Both lower products, including $(q;q)_r$, are present. |
| The displayed contiguous quotient | `KimStantonSingleDenominator.gamma` | The upper and lower parameter shifts are literal. |
| Every natural coefficient index | `KimStantonSingleDenominator.claim` | The quantifier includes zero. |
| An integer polynomial in all four variables | The existential `MvPolynomial (Fin 4) ℤ` binder | The variables are ordered $a,b,c,q$. |
| The prescribed floor exponent product | `KimStantonDenominatorCore.D` | Natural division is floor division. |
| The claimed identity | `KimStantonSingleDenominator.result` | No additional hypotheses. |

## Motivation

The frozen declaration `D5/S3/Combinatorics/MotzkinHankel/KimStantonSingleDenominator.result` supplies the numerator for every degree.

## Gap

[Preregistration #21469](https://github.com/the-omega-institute/trureturing/issues/21469) records the source and literature screen. No settlement was found in its screened sources. Its citation inventory and journal-version comparison are incomplete; literature completeness is `ASSUMED-UNVERIFIED`.

## Route

The recurrence puts quotient coefficients in $R[(1-cq^k)^{-1}:k\in\mathbb N]$. Pole onset and the reciprocal coefficient induction give the floor envelope. Multiplication by $D_n$ and division by $1-c$ give an element regular at every inverted prime. Finite prime cancellation places it in $R$.

## Falsifier

A coefficient outside that integral localization, a pole exceeding the stated envelope, or a failure of the source-to-series correspondence would invalidate this route. The settlement concerns the formal fraction field; singular parameter evaluations are outside its statement.

## Evidence

`D5/S3/Combinatorics/MotzkinHankel/KimStantonSingleDenominator.result` proves the full claim. Its supporting content is `KimStantonDenominatorCore.denominator_from_localization` and the recurrence coefficient theorem. The finite checks below are consistency evidence.

Escape audit unfinished: [#21724](https://github.com/the-omega-institute/trureturing/issues/21724). No four-slot registration is claimed validated.

## Triage

1. **Proved, kernel-checked:** the private `KimStantonDenominatorCore.inverse_floor_bound` and `ratio_floor_bound` establish the inverse and ratio floor envelopes for arbitrary fields and subrings. Their hypotheses specify the input bounds and normalized constant coefficient.
2. **Proved, kernel-checked:** `KimStantonDenominatorCore.localization_descent`, `quotient_coefficients_mem`, `cleared_ratio_local` and `heine_contiguous` give prime localization descent, recurrence coefficient membership, the specialized pole envelope and Heine's contiguous identity, respectively. Private declarations are identified by their source names; no independent public API is claimed for them.
3. **Proved in prose:** both degree-zero numerators can be $P_0=1$. Each factor product at index zero is empty, so each $F$ has constant coefficient one. Thus each formal quotient has constant coefficient one. Since $D_0=1-c$, the asserted identity at $n=0$ is $1/(1-c)=1/(1-c)$.
4. **Computed:** the experiment below checks both symbolic denominator assertions for $n=0,\ldots,4$, Heine fidelity for $n=0,\ldots,4$, and both continued fractions for $n=0,\ldots,12$ on five exact rational tuples. Its exit code is 0 and its terminal reading is `ALL_CHECKS_OK`. These finite computations do not prove a uniform extension.
5. **Open:** denominator minimality or sharpness, numerator positivity, singular-divisor specializations and further parameter shifts.
6. **Proved, kernel-checked:** `KimStantonSingleDenominator.result` and `KimStantonSimultaneousDenominator.result` establish Conjectures 8.4 and 8.3 for every natural degree in the fraction-field conventions above.

### What the settlement shows

The two results supply integer polynomial numerators for the prescribed common denominator. The decisive estimate is that a denominator factor whose first possible pole occurs in degree $k+1$ can occur in an inverse coefficient of degree $n$ to order at most $\lfloor n/(k+1)\rfloor$. The numerator shift changes the envelope at $k>0$ to $\lfloor(n+1)/(k+1)\rfloor$; the factor at $k=0$ is handled separately. The continued-fraction recurrence supplies integral localization membership, and prime cancellation descends to the integer polynomial ring. This explanation does not assert the denominator is reduced.

The generic bound allows arbitrary fields and subrings under its stated hypotheses; the public settlements retain the algebraically independent four-variable integer polynomial setting. Both zero-degree cases are included. No claim of positive numerators, denominator optimality or extension across singular divisors follows. The source's two denominator conjectures are settled in this setting; no change to its other theorem statements is asserted.

### Experiment

[Exact finite checker](https://github.com/the-omega-institute/trureturing-experiments/tree/99ab5231d2f634d43e8b411a0f3c2fd7c95cd88f/docs/reports/ks2105-2phi1denom).
Execution from the experiments repository: `git show 99ab5231d2f634d43e8b411a0f3c2fd7c95cd88f:docs/reports/ks2105-2phi1denom/check.py | python3 -u`; exit 0.
The SHA-256 of `check.py` is `cbc58a8f87008b61661833849eae8460427b2caf6121d4da9fe428d143cedf80`.
The measured scope is exactly item 4; symbolic numerator term counts are $[1,6,34,209,678]$ for 8.3 and $[1,4,24,162,530]$ for 8.4. The final reading is `ALL_CHECKS_OK`.

## ASSUMED-UNVERIFIED

Literature completeness and equivalence with an unavailable journal version are unverified. The binding source is arXiv v3. Positivity, sharpness, singular specializations and further shifts remain open. Escape registration is unfinished as described in issue #21724.
