---
slug: h3894-congruences
bibkey: hanna2025a3894congruences
doi: null
url: https://oeis.org/A389474
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/HannaCompositionSquareModNine
---

# Hanna's composition-series congruences

## Problem

Paul D. Hanna's OEIS A389474, FORMULA (3), states:

> (3) [x^n] A(x)^2 == 0 (mod 9) for n > 3 (conjecture).

The source equation is $A(x^2+2x^3+2A(x)^2)=3A(x)^2$, with $A(0)=0$ and $[x]A=1$. For every normalized rational solution and every natural $n>3$, the coefficient $[x^n]A^2$ is an integer multiple of nine. Existence is part of the claim.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Composition equation | `HannaCompositionSquareModNine.IsGF` | literal equation in rational formal power series |
| Expansion starts $x+x^2$ | `IsGF` fixes constant coefficient zero and linear coefficient one | source normalization |
| $n>3$ | `claim` quantifies natural $n$ with $3<n$ | unchanged range |
| Congruence modulo nine | `claim` requires equality to $9m$, $m\in\mathbb Z$, in $\mathbb Q$ | includes integrality |
| Implicitly defined source series | `claim` asserts existence and the conclusion for every normalized solution | nonvacuity and no chosen-solution weakening |
| A389474 FORMULA (4) | `FormulaFour.claimFour` and `FormulaFour.resultFour` | same `IsGF`, all natural $n,k\ge1$, integer multiples of three |

The source is the OEIS entry, not an arXiv paper. Preregistrations are #21670 and #21671. The family also includes A389475 (#21672, #21673) and A389472 (#21674).

## Motivation

The settling GID is `D5/S1/Recurrence/Invariants/HannaCompositionSquareModNine.result`. The companion power congruence is `D5/S1/Recurrence/Invariants/HannaCompositionSquareModNine.resultFour`. The construction proves existence rather than assuming an integral source series.

## Gap

The source labels these lines conjectural. The preregistration's OEIS, arXiv, MathOverflow, bibliographic-index and third-party Lean screens located no settlement in the searched scope. Rate-limited indexes and unread citing full texts prevent a completeness or priority claim. Literature completeness is ASSUMED-UNVERIFIED.

## Route

For the residual $E(f)=f(X^2+2X^3+2f^2)-3f^2$, changing coefficient $a_n$ changes coefficient $n+1$ of $E$ by $-2a_n$. Reduction modulo two makes the triangular numerator even, so the frozen general lifting construction supplies an integral normalized solution. The private `solution_unique` proves uniqueness over a commutative ring without zero divisors whenever $2\ne0$; `rational_identification` identifies every rational source solution with the integral construction.

Write $A=X+X^2Q$, $D=X^2+2X^3$ and $H=D+2A^2$. Then $A(H)=H+H^2Q(H)=3A^2$. Set $U=1+HQ(H)$. Its constant coefficient is one, so it has an integral inverse $V$. Consequently $H=3A^2V$ and $A^2-D=H^2Q(H)=9(A^2V)^2Q(H)$. This is the private `integral_mod_nine` identity; `result` extracts the coefficients beyond degree three. The companion result uses the integral Frobenius theorem from `HannaTripleSquareFrobeniusModThree.integral_frobenius`.

## Falsifier

A normalized rational source solution with some $n>3$ for which $[x^n]A^2$ is not nine times an integer would contradict `result`. The normalization, rational coefficient ring and unbounded index range are included in that theorem's claim.

## Evidence

Kernel evidence is `HannaCompositionSquareModNine.result` and `FormulaFour.resultFour`. The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}.

Experiment: [hanna-a3894-mod3 at ce9022cf0c3f59beba20cf693ad322eae0186d5c](https://github.com/the-omega-institute/trureturing-experiments/tree/ce9022cf0c3f59beba20cf693ad322eae0186d5c/docs/reports/hanna-a3894-mod3). Command: `python3 docs/reports/hanna-a3894-mod3/check.py`; exit 0; script SHA-256 `b2e554248dbdf2612923d6fd061a5e3306622a27061f9f27ab5f8fbf92fe1e0d`; final result `ALL_CHECKS_OK`. The immutable script was extracted with `git show ce9022cf0c3f59beba20cf693ad322eae0186d5c:docs/reports/hanna-a3894-mod3/check.py` and executed with Python 3.14.8. No experiment program is embedded here.

Escape audit unfinished: [#22693](https://github.com/the-omega-institute/trureturing/issues/22693). The nine targets are the five settling theorems across the three family modules, HannaTripleSquareFrobeniusModThree.integral_frobenius, and the three published HannaPrimeSubstitutionIntegrality coefficient-order owners. No four-slot registration is claimed complete.

## Triage

1. **Proved (kernel-checked private declarations).** Both nonlinear equations have integral normalized solutions: each module's `exists_integral`. Each `solution_unique` proves uniqueness over every commutative ring without zero divisors where $2\ne0$; each `rational_identification` identifies rational solutions with the mapped integral construction. The nonzero coefficient diagonal is $-2$.
2. **Proved (kernel-checked).** `HannaTripleSquareFrobeniusModThree.integral_frobenius` proves $3\mid[x^n](f^{3k}-f(X^3)^k)$ for every integral series and all natural $n,k$, including zero. This extends A389474 (4)'s range; A389475 (4.a) is its $k=1$ case.
3. **Proved (kernel-checked private declaration).** `HannaCompositionSquareModNine.integral_mod_nine` proves the stronger integer-series identity $A^2-(X^2+2X^3)=9Q$ for some integral $Q$.
4. **Proved (kernel-checked).** `HannaTripleSquareFrobeniusModThree.FormulaFourB.resultFourB`, through private `integral_mod_three`, proves every coefficient of $A^2-X^2-2A(X^3)$ is a multiple of three. The explanation is reduction of the equation to $A^2=X^2+2A^3$ in characteristic three, followed by Frobenius.
5. **Proved (kernel-checked).** `SquareCubeSubstitutionThreeIndexModThree.result`, using private `descent`, proves the A389472 residue class $m\equiv2\pmod3$ is divisible by three for $m\ge5$. The existing odd-index parity theorem remains at `SquareCubeSubstitutionOddIndexParity.result`; it is not on this module's proof dependency path.
6. **Computed.** The experiment entry checks the equations and congruences through degree 403; A389474 (4) uses $k=1,\ldots,135$, with larger exponents vanishing in that truncation by order. It checks 403 A389472 target indices $n=2,\ldots,404$ through coefficient 1211 and matches 24/23/41 displayed source terms for A389474/A389475/A389472. Finite tests do not prove the unbounded assertions.
7. **Computed from the exact source coefficients.** At degree four, A389474 has $[x^4]A^2=9$ with remainder 9 modulo 27; A389475 has $[x^4](A^3-A(X^3))=3$ with remainder 3 modulo 9, and $[x^4](A^2-X^2-2A(X^3))=15$ with remainder 6 modulo 9. A389472 has $a(5)=6$ with remainder 6 modulo 9. The experiment entry's command (exit 0, the same script SHA-256) verifies the exact source coefficients. With $a_1=a_2=1$ and $a_3=4$ for A389474, $[x^4]A^2=2a_1a_3+a_2^2=9$. For A389475, $a_1=a_2=1$ and $a_3=7$ give $[x^4]A^2=15$ and $[x^4]A^3=3$; $A(X^3)$ has zero coefficient in degree four. The verified A389472 source list has $a(5)=6$. Exact integer remainder calculations give the values stated above. They are finite computations, not Lean refutations of stronger moduli.
8. **Open.** No general classification for other Hanna composition equations or other primes is established. Broader publication priority remains ASSUMED-UNVERIFIED.

### What the settlement shows

The decisive mechanism is an integral unit factor: divisibility of $H$ by three squares to divisibility of $A^2-D$ by nine. The theorem covers every normalized rational solution and every requested index. The private identity also retains the exceptional low-degree terms exactly. The characteristic-three Frobenius theorem applies to arbitrary integral series and all natural exponents, while equation-specific integrality is proved for each source series. The finite values in item 7 rule out the indicated immediate stronger moduli. The source's reversion formula is not used or settled here; no other source result is asserted to depend on these conjectures.

## ASSUMED-UNVERIFIED

Completeness of the external literature screen, unread citing full texts, bibliographic API failures, publication priority and a uniform classification of other equations or primes remain unverified. Four-slot escape registration is unfinished under #22693. The finite experiment is supporting evidence within its stated scope only.
