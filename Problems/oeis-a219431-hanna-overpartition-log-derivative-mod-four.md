---
slug: oeis-a219431-hanna-overpartition-log-derivative-mod-four
bibkey: hanna2012a219431
doi: null
url: https://oeis.org/A219431
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Partitions/OverpartitionSquareLogDerivativeModFour.result
---

# Hanna's overpartition logarithmic derivative congruences

## Problem

Paul D. Hanna's OEIS A219431 has Name “Logarithmic derivative of the g.f. of the overpartitions of n^2 (A219430).” Its Comment states: “Conjecture: a(2*n+1) == 2 (mod 4), a(2*n) == 0 (mod 4).” The offset is one. OEIS A219430 states: “Number of overpartitions of n^2; a(n) = A015128(n^2).”

Let $\bar p(m)$ be the coefficient of $q^m$ in $\prod_{k\geq1}(1+q^k)/(1-q^k)$, and put $G(x)=\sum_{n\geq0}\bar p(n^2)x^n$. The settlement proves that every positive-degree coefficient $a(m)=[x^m]xG'(x)/G(x)$ is an integer, with $a(m)\equiv 2$ for odd $m$ and $a(m)\equiv0$ for even $m$, modulo four. Preregistration: [#18874](https://github.com/the-omega-institute/trureturing/issues/18874).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Overpartition generating product | `pbar` | At degree $m$, factors with $k>m$ have no effect; the finite product uses $1\leq k\leq m$. |
| Square-indexed coefficients, including index zero | `G` | `PowerSeries.mk` with coefficient `pbar` at $n^2$. |
| Logarithmic derivative, offset one | `logDerivative` | $xG'(x)G(x)^{-1}$ over the rationals. |
| Every index at least one | `claim` | All natural $m$ with $1\leq m$. |
| Integer coefficients and two congruences | `claim`, `result` | One integer witness equals the rational coefficient and satisfies both parity implications. Integrality is an explicit strengthening, with no additional hypothesis. |

The four public definitions retain the expressions of the preregistration. Their parameters, coefficient rings and modulus are unchanged. The positive geometric tail and the divisibility-indicator geometric series are reused from their existing owners rather than declared again.

## Motivation

`D5/S3/Combinatorics/Partitions/OverpartitionSquareLogDerivativeModFour.result` proves Hanna's stated conjecture with integrality. The module has `generality: I`, `utility: none`, and `admission_basis: open-problem-resolution (#18874; Proved)`. It is frozen by `deposit-uncovered`, with no anchor atom.

## Gap

The source and literature screen in #18874 found no proof or refutation in the OEIS entry and links, the cited OEIS proof collections, the OEIS Open catalogue, Kallat's catalogue, or the repository. The GPT Pro literature reading is recorded in that issue. This is a bounded literature reading; completeness is `ASSUMED-UNVERIFIED`. The attribution of the standard overpartition congruence is also `ASSUMED-UNVERIFIED`.

## Route

All unqualified declaration names here belong to `D5.S3.Combinatorics.Partitions.OverpartitionSquareLogDerivativeModFour`. The private integer lift `pbarZ` uses geometric factors with integer coefficients; `pbarZ_cast` identifies its rational image with `pbar`.

The finite-product identity `product_mod_four` eliminates every product containing two factors of two. Consequently `pbarZ_mod_four` proves $\bar p(m)\equiv2d(m)\pmod4$ for $m>0$, where $d(m)$ is the divisor count. The private `square_divisors_odd` and `pbarZ_square` show that positive square inputs give residue two. Thus `GZ_mod_four` identifies the integer series modulo four with $1+2H$, where $H=\sum_{n\geq1}x^n$.

The integer inverse exists because `GZ_zero` gives constant coefficient one. The private `logZ_cast` connects its logarithmic derivative to the rational source expression. In characteristic four, $(1+2H)^{-1}=1-2H$ and $(1+2H)'=2H'$, so `logZ_mod_four` gives $\operatorname{logZ}\equiv2xH'$. The coefficient theorem `logZ_coeff_mod_four` gives residue $2m$; `result` converts it to the two parity implications.

The proof uses the imported owner declarations `LinearExponentDyadicSupport.derivative_map`, `BilateralQuarticPowerThetaModFour.map_inv` and `BilateralQuarticPowerThetaModFour.four_zero` through `OpenPrivate`. The series owners are `AndrewsElBachraouiDefs.geom` and `ScaledReversionCongruence.geometric`.

## Falsifier

A counterexample would be an index $m\geq1$ with a nonintegral logarithmic coefficient or a coefficient violating its parity residue modulo four. The theorem quantifies over all such indices. The finite experiment alone does not establish that quantifier.

## Evidence

Formal source: [OverpartitionSquareLogDerivativeModFour.lean](../D5/S3/Combinatorics/Partitions/OverpartitionSquareLogDerivativeModFour.lean). The axiom closure of every public declaration is contained in `{propext, Classical.choice, Quot.sound}`.

The sole public theorem `D5.S3.Combinatorics.Partitions.OverpartitionSquareLogDerivativeModFour.result` has `proof_shape: bind-only`, `escape_witness: none`, and admission basis `open-problem-resolution (#18874; Proved)`. Every private theorem has `proof_shape: bind-only` and a named consumer on the proof of `result`; none is claimed as an escape witness.

Experiment: [pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/c5dabc62c062deabf41b961b6a7a47aca6874db7/docs/reports/oeis-a219431-overpartition-square-logderivative-mod4). Command: `python3 check.py 200 b219431.txt`, run on the files read from this commit; exit 0. Script SHA-256: `52cc09dfca497d5014fa9995aef360c7ce08964ab224f945d900d3a91532a2bb`. The product-defined overpartition congruence and its independent theta recursion agree for $1\leq m\leq3000$; square-input residues, equality with the OEIS b-file and logarithmic coefficient residues hold for $1\leq n\leq200$. These are finite computations.

The four-slot escape audit for `result` is unfinished: [#19996](https://github.com/the-omega-institute/trureturing/issues/19996). The scoped report decodes no registration. A faithful guarded universal-existential realization, its source reconstruction, bridge, variation, sensitivity and actual observational-dependence evidence are missing. No `declared_validated` registration is claimed.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Result and boundary |
| --- | --- | --- |
| Residue information suffices after `GZ_mod_four` | Proved, kernel-checked: `logZ_mod_four`, `logZ_coeff_mod_four`, `result` | The remaining coefficient argument uses $G\bmod4=1+2H$ and its integer lift; it does not use the sizes of $\bar p(n^2)$. This is the dependency and reduction statement for this series, not a separate universally quantified Lean theorem. |
| Positive-square sampling sequences $s(0)=0$, $s(n)>0$ a square for $n>0$ | Open; candidate for later formalization | The same reduction suggests the same residues. No theorem for arbitrary $s$ is asserted by this module. |
| Congruences modulo eight | Open | Not addressed by the characteristic-four argument. |
| Standard congruence attribution | Literature reading; `ASSUMED-UNVERIFIED` | The kernel checks $\bar p(m)\equiv2d(m)\pmod4$ in `pbarZ_mod_four`; its original bibliographic attribution is unverified. |
| Numerical check | Computed | Exactly the ranges and comparisons in the pinned experiment entry above. |
| Consequences for the source | Proved, kernel-checked: `result` | Both residue assertions in OEIS A219431 hold at every positive index, with integrality. No further source theorem depending on the conjecture is supplied by the cited entry. |
| Literature completeness | Literature reading; `ASSUMED-UNVERIFIED` | The searched scope is listed in #18874; no global completeness claim. |

## ASSUMED-UNVERIFIED

The literature screen's completeness and the original attribution of the standard overpartition congruence are unverified. The broader square-valued sampling statement and modulo-eight congruences remain open here. The escape audit remains unfinished under #19996. Search misses establish absence only in the searched scope.
