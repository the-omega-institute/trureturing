---
slug: h3894-square-cube-three-index
bibkey: hanna2025a3894congruences
doi: null
url: https://oeis.org/A389472
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Parity/SquareCubeSubstitutionThreeIndexModThree
---

# Hanna A389472: congruences modulo three

## Problem

OEIS A389472 states:

> Conjecture: a(3*n-1) = 0 (mod 3) for n > 1.

`claim` states this divisibility for every natural $n>1$ using the existing integer sequence `SquareCubeSubstitutionOddIndexParity.a`. Its generating equation is $X^2(A+1)=A(X^2+X^3)$ and its seeds include $a(0)=0$, $a(1)=a(2)=1$. The source equation alone does not fix $a(2)$; the displayed expansion does.

Preregistration: #21674. The source is OEIS, with no identified arXiv source.

## Motivation

The settling GID is `D5/S1/Recurrence/Parity/SquareCubeSubstitutionThreeIndexModThree.result`. The family and its clause-level statement echo are documented in [Hanna's composition-series congruences](h3894-congruences.md). This module settles an unbounded coefficient assertion.

## Gap

The preregistration's source and literature screen located no settlement in its searched scope. Completeness and publication priority are ASSUMED-UNVERIFIED; rate-limited indexes and unread full texts are not negative results.

## Route

The existing coefficient recurrence expresses $a(m)$ by binomial-weighted earlier terms. For $m\equiv2\pmod3$, Lucas congruences kill upper indices not congruent to two. Strong induction kills earlier indices congruent to two once they are at least five. The remaining index two has a zero binomial coefficient. The private `descent` proves this for every $m\ge5$ in the residue class, and `result` substitutes $m=3n-1$.

## Falsifier

A source-normalized coefficient violating the stated modulo-three congruence would contradict `result`. No finite truncation replaces the natural-number quantifiers.

## Evidence

Kernel evidence is `SquareCubeSubstitutionThreeIndexModThree.result`. The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}.

The [family dossier's experiment entry](h3894-congruences.md#evidence) identifies the immutable program, revision, command, SHA-256, exit code and finite tested scope. Escape audit unfinished: [#22693](https://github.com/the-omega-institute/trureturing/issues/22693); no four-slot registration is claimed complete.

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

The existing coefficient recurrence expresses $a(m)$ by binomial-weighted earlier terms. For $m\equiv2\pmod3$, Lucas congruences kill upper indices not congruent to two. Strong induction kills earlier indices congruent to two once they are at least five. The remaining index two has a zero binomial coefficient. The private `descent` proves this for every $m\ge5$ in the residue class, and `result` substitutes $m=3n-1$.

The finite computations in item 7 exclude the listed immediate stronger moduli. A classification of other equations or primes remains open. The existing parity theorem is a related result; it is not on the modulo-three module's dependency path.

## ASSUMED-UNVERIFIED

Literature completeness, publication priority and broader classifications remain unverified. Four-slot escape registration is unfinished under #22693. The exact finite experiment scope is separate from the kernel-checked unbounded claims.
