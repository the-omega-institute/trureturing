---
slug: hanna-a271960-dyadic-vanishing
bibkey: hanna2016a271960
doi: null
url: https://oeis.org/A271960
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/PowerSeries/HannaA271960DyadicVanishing.result
---

# Hanna’s OEIS A271960 dyadic vanishing conjecture

## Problem

Paul D. Hanna’s [OEIS A271960](https://oeis.org/A271960), COMMENTS (unpaginated), states:

> Conjecture: [x^(2^n-2^k)] (x/A(x))^(2^n) = 0 for k = 0..n-2 and n >= 2. - _Paul D. Hanna_, Jan 16 2026

Its NAME is:

> G.f. A(x) satisfies: A(x)^2 = A( (x + 2*A(x)^2)^2 ).

The OFFSET is 1 and the EXAMPLE begins $A(x)=x+2x^2+9x^3+50x^4+312x^5+\cdots$.
The [Library note](../Library/RecurrenceComposition/hanna2016a271960.md) records the source.
Preregistration: [#19138](https://github.com/the-omega-institute/trureturing/issues/19138).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| The defining equation | `IsGF A` | Literal rational power-series equation, with `PowerSeries.subst u f` meaning $f(u)$. |
| Offset and leading coefficient | First two conjuncts of `IsGF` | Constant coefficient zero and linear coefficient one. |
| $x/A(x)$ | `xOverA A` | Inverse of the series with coefficient $[x^{n+1}]A$ at index $n$. |
| $n\ge2$, $0\le k\le n-2$ | Natural binders and the two bounds in `claim` | Natural subtraction is exact under the bounds. |
| Coefficient and power | Universal conjunct of `claim` | $[x^{2^n-2^k}](x/A(x))^{2^n}=0$. |
| Existence | Existential conjunct of `claim` | Additional conclusion; it does not restrict the universally quantified solutions. |
| Every normalized solution | Universal $A$ with `IsGF A` | No selected solution replaces the source’s equation. |

## Motivation

The coefficient pattern is a support restriction propagated by compositional inversion and repeated halving of the degree and exponent. It is not a finite table assertion.

## Gap

The source and literature checks recorded in #19138 found no settlement in the linked OEIS entries A271959, A386667, A376224 and A378247, the searched MathOverflow, Mathematics Stack Exchange and Zenodo results, the formal-conjectures catalogue, or the screened literature. The screen includes Kallat’s arXiv:2610.15849v1, Gessel’s arXiv:1609.05988, and the classical generating-function references named in #19138. Two classical papers were not accessed. Literature completeness and continued external open status are `ASSUMED-UNVERIFIED`.

## Route

Let $B$ be the compositional inverse of $A$ and put $H=B+2X^2$. Substitution into the defining equation yields $H^2=B(X^2)$. Reflection preserves the square, and the linear coefficient of $H$ is one, so $H(-X)=-H(X)$.

Expanding $(H-2X^2)^r$ at an even degree eliminates odd powers of $H$. Even powers reduce via $H^2=B(X^2)$. Induction then gives $[X^N]B^r=0$ when $2r<N$, $2^s\mid N-2r$ and $r<2^s$. Lagrange inversion, supplied by `NonnestingOneThreeTwoTwo.lagrange_coefficient`, transfers this to the required coefficients at $N=2^n$, $r=2^k$, $s=k+1$.

Existence is obtained by stabilization of the iteration $F\mapsto F+(F(X^2)-F^2-2X)/2$ from one, followed by reversion. The coefficient-agreement steps use the original `SignedCatalanCubicSubstitutionModThree.square_linear` and `subst_two_agree`; its `inverse_exists` supplies the two-sided inverse. These declarations occur in the elaborated proof dependency path.

## Falsifier

A normalized rational solution with a nonzero coefficient in the specified range would contradict `result`. A series with a different constant or linear coefficient falls outside the source-to-formalization bridge and the displayed hypotheses.

## Evidence

`D5.S3.Combinatorics.PowerSeries.HannaA271960DyadicVanishing.result` proves the complete `claim`, including existence. Its admission basis is `open-problem-resolution (#19138; Proved)`; generality is G and utility is none. The three original owner declarations are published with their statements and proofs preserved.

The four-slot escape audit is unfinished for `result` and the published `square_linear`, `subst_two_agree` and `inverse_exists`: [#19172](https://github.com/the-omega-institute/trureturing/issues/19172). The infinite power-series and arbitrary-ring telescopes need faithful source-family reconstruction, equivalence, observational dependence, variation and sensitivity evidence. No compiled registration or `declared_validated` finding is claimed.

### Experiment

The prescribed experiment is [docs/reports/oeis-a271960-hanna-dyadic-vanishing at dbec0fc04793e93bacc5804d9b69298518661c49](https://github.com/the-omega-institute/trureturing-experiments/tree/dbec0fc04793e93bacc5804d9b69298518661c49/docs/reports/oeis-a271960-hanna-dyadic-vanishing).
Command: `python3 docs/reports/oeis-a271960-hanna-dyadic-vanishing/check.py` in that repository; exit 0, RESULT PASS. Script SHA-256: `858a2e813619eff1f42e93b6d01fb8f6da11344725fd47d0217466ec58c3f7f2`.
At order 520 it checks all 21 pairs with $2^n\le128$ exactly and all 36 pairs with $2^n\le512$ modulo each of 67108859 and 67108837. It verifies the defining equation modulo both primes and the twelve example coefficients exactly.

## Triage

| Item | Status and evidence kind | Scope |
| --- | --- | --- |
| General inverse-power support | Proved, kernel-checked private `dyadic_vanishing` | Every $s,N,r\in\mathbb N$ under its displayed $B,H$ hypotheses, $2r<N$, $2^s\mid N-2r$ and $r<2^s$. The conjecture is the power-of-two specialization in `result`. |
| Prescribed checker | Computed, the pinned experiment above | RESULT PASS for 21 exact pairs through $2^n\le128$ and 36 pairs modulo two primes through $2^n\le512$, at order 520. |
| Excluded boundary | Computed, the pinned experiment above | At $k=n-1$, the coefficients for $n=2,\ldots,7$ are $4,-60,-1340,-15724860,284540130262724,987872032806775979918826979012$, all nonzero. Universal boundary nonvanishing is open. |
| Rational parameter and A386667 | Open, ASSUMED-UNVERIFIED | Neither the analogous rational-parameter extension nor transfer to A386667 is formalized here. |

### What the settlement shows

Proved in this module: `dyadic_vanishing` gives the stronger support restriction for every $s,N,r$ satisfying its hypotheses. The decisive mechanism is oddness plus coefficient decimation, with the positive gap $N-2r$ halved at each induction step. The existence conjunct is proved by the stabilized construction; the settlement applies to every normalized solution.

Computed: the listed boundary coefficients show that enlarging the range to include $k=n-1$ for every $n$ is false. They do not establish a universal nonvanishing theorem. Open: a parameter-family formalization, the exact comparison with A386667, and universal boundary nonvanishing. The source screen identifies no further result whose validity depends on this conjecture; no consequence for an unread source is asserted.

## ASSUMED-UNVERIFIED

Literature-screen completeness and continued external open status; the rational-parameter extension; transfer to A386667; and universal boundary nonvanishing. The four-slot escape audit is unfinished under #19172. Computation is finite evidence and does not supply the unbounded theorem.
