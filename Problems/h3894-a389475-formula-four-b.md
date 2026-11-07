---
slug: h3894-a389475-formula-four-b
bibkey: hanna2025a3894congruences
doi: null
url: https://oeis.org/A389475
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/HannaTripleSquareFrobeniusModThree
---

# Hanna A389475: FORMULA (4.b)

## Problem

Paul D. Hanna's OEIS A389475, FORMULA (4.b), states:

> (4.b) A(x)^2 == x^2 + 2*A(x^3) (mod 3) (conjecture).

Preregistration: [#21673](https://github.com/the-omega-institute/trureturing/issues/21673). The source is the OEIS entry, not an arXiv paper.

The source equation is $A(3x^2)=2x^2+A(x)^2-2A(x)^3$, with $A(0)=0$ and $[x]A=1$. A normalized rational solution exists. For every such solution and every natural $n$, including zero, $[x^n](A(x)^2-x^2-2A(x^3))$ is three times an integer. The source predicate adds no integrality assumption.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Normalized triple-substitution equation | `HannaTripleSquareFrobeniusModThree.IsGF` | the same predicate used for FORMULA (4.a) |
| Coefficientwise square congruence | `FormulaFourB.claimFourB` | every natural coefficient, including zero |
| Modulus three | integer multiplier in the rational coefficient equality | integrality is included |
| Implicit source series | existence conjunct and universal quantifier over normalized solutions | nonvacuous, with no chosen-solution restriction |

## Motivation

The settling declaration is `D5.S1.Recurrence.Invariants.HannaTripleSquareFrobeniusModThree.FormulaFourB.resultFourB`. FORMULA (4.a) retains its own resolution claim in [the triple-substitution dossier](h3894-triple-square-frobenius-mod-three.md); this dossier identifies FORMULA (4.b) separately.

## Gap

The source labels the assertion conjectural. The preregistration's source and literature screen found no settlement in its searched scope. Literature completeness and publication priority remain ASSUMED-UNVERIFIED; unavailable indexes and unread full texts are not negative results.

## Route

The module's `exists_integral` constructs an integral normalized solution by triangular lifting with coefficient diagonal $-2$. Modulo two the residual is $A(x^2)-A^2$, so each triangular numerator is even. `solution_unique` and `rational_identification` identify every normalized rational solution with the integral construction.

Since the integral solution has constant coefficient zero, $A(3x^2)$ vanishes coefficientwise modulo three. The source equation reduces to $A^2=x^2+2A^3$ in characteristic three. Frobenius replaces $A^3$ by $A(x^3)$; `integral_mod_three` lifts this equality to integer divisibility. `FormulaFourB.resultFourB` transfers the conclusion to every normalized rational solution.

## Falsifier

A normalized rational source solution with any natural coefficient of $A^2-x^2-2A(x^3)$ that is not three times an integer would contradict `FormulaFourB.resultFourB`. No finite truncation replaces the coefficient quantifier.

## Evidence

Kernel evidence is `HannaTripleSquareFrobeniusModThree.FormulaFourB.resultFourB`, through private `integral_mod_three`. Its axiom closure is contained in {propext, Classical.choice, Quot.sound}.

The [family dossier's experiment entry](h3894-congruences.md#evidence) identifies the immutable program, revision, command, SHA-256 and exit code. Escape audit is unfinished under [#22693](https://github.com/the-omega-institute/trureturing/issues/22693); no complete four-slot registration is claimed.

## Triage

1. **Proved (kernel-checked).** `FormulaFourB.resultFourB` settles FORMULA (4.b) at every natural coefficient of every normalized rational source solution, with existence included.
2. **Proved (kernel-checked private declarations).** `exists_integral`, `solution_unique` and `rational_identification` establish integral normalized existence and identification; `integral_mod_three` proves the square-congruence identity for the integral construction.
3. **Computed.** The family experiment checks the equation and congruence through degree 403 and matches all 23 displayed A389475 terms. At degree four the square-congruence difference is 15, with remainder 6 modulo nine. This is a finite computation, not a Lean refutation of a stronger modulus.
4. **Open.** A classification of other equations or primes and exhaustive publication priority are not established.

## ASSUMED-UNVERIFIED

Literature completeness, unread citing full texts, bibliographic API failures and publication priority remain unverified. Four-slot escape registration is unfinished under #22693. Finite experimental agreement is separate from the unbounded theorem.
