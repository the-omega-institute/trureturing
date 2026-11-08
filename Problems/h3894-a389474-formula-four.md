---
slug: h3894-a389474-formula-four
bibkey: hanna2025a3894congruences
doi: null
url: https://oeis.org/A389474
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/HannaCompositionSquareModNine
---

# Hanna A389474: FORMULA (4)

## Problem

Paul D. Hanna's OEIS A389474, FORMULA (4), states:

> (4) [x^n] A(x)^(3*k) - A(x^3)^k == 0 (mod 3) for n >= 1 and k >= 1 (conjecture).

Preregistration: [#21671](https://github.com/the-omega-institute/trureturing/issues/21671). The source is the OEIS entry, not an arXiv paper.

The source equation is $A(x^2+2x^3+2A(x)^2)=3A(x)^2$, with $A(0)=0$ and $[x]A=1$. A normalized rational solution exists. For every such solution and all natural $n,k\ge1$, the coefficient $[x^n](A(x)^{3k}-A(x^3)^k)$ is three times an integer. Integrality is proved rather than added as a hypothesis.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Normalized composition equation | `HannaCompositionSquareModNine.IsGF` | the same predicate used for FORMULA (3) |
| $n\ge1$ and $k\ge1$ | `FormulaFour.claimFour` | both natural indices retain their lower bounds |
| Congruence modulo three | `FormulaFour.claimFour` | rational coefficient equals $3m$ for an integer $m$ |
| Implicit source series | existence conjunct and universal quantifier over normalized solutions | nonvacuous, with no chosen-solution restriction |

## Motivation

The settling declaration is `D5.S1.Recurrence.Invariants.HannaCompositionSquareModNine.FormulaFour.resultFour`. FORMULA (3) has its own resolution claim in [the family dossier](h3894-congruences.md); this dossier identifies FORMULA (4) separately.

## Gap

The source labels the assertion conjectural. The preregistration's source and literature screen found no settlement in its searched scope. Rate-limited indexes and unread citing full texts leave literature completeness and publication priority ASSUMED-UNVERIFIED.

## Route

The module's `exists_integral` constructs an integral normalized solution by triangular lifting: the residual coefficient diagonal is $-2$, and reduction modulo two makes each numerator even. `solution_unique` and `rational_identification` identify every normalized rational solution with that integral construction.

Apply `HannaTripleSquareFrobeniusModThree.integral_frobenius` to this integral series. Reduction in characteristic three gives $A^3=A(x^3)$; raising both sides to $k$ and extracting coefficient $n$ gives an integer multiple of three for $A^{3k}-A(x^3)^k$. The Frobenius theorem is reused, with the equation-specific integrality supplied by the construction. The modulo-nine conclusion is not needed for this deduction.

## Falsifier

A normalized rational source solution and natural $n,k\ge1$ whose indicated coefficient is not three times an integer would contradict `FormulaFour.resultFour`. The claim includes existence and the full unbounded ranges.

## Evidence

Kernel evidence is `HannaCompositionSquareModNine.FormulaFour.resultFour`. Its axiom closure is contained in {propext, Classical.choice, Quot.sound}.

The [family dossier's experiment entry](h3894-congruences.md#evidence) identifies the immutable program, revision, command, SHA-256 and exit code. Finite agreement is supporting evidence, separate from the unbounded theorem. Escape audit is unfinished under [#22693](https://github.com/the-omega-institute/trureturing/issues/22693); no complete four-slot registration is claimed.

## Triage

1. **Proved (kernel-checked).** `FormulaFour.resultFour` settles FORMULA (4) for every normalized rational source solution and all natural $n,k\ge1$, including normalized existence.
2. **Proved (kernel-checked).** The reused `integral_frobenius` covers every integral series and all natural coefficient indices and exponents, including zero. The source result uses its stated positive ranges.
3. **Computed.** The family experiment checks this congruence through degree 403 for $k=1,\ldots,135$; larger powers vanish in that truncation by order. This finite check does not prove the all-indices assertion.
4. **Open.** A classification of other equations or primes and exhaustive publication priority are not established.

## ASSUMED-UNVERIFIED

Literature completeness, unread citing full texts, bibliographic API failures and publication priority remain unverified. Four-slot escape registration is unfinished under #22693. The finite experiment has only the stated scope.
