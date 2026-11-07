---
slug: oeis-a320949-hanna-mod-three
bibkey: hanna2018a320949
doi: null
url: https://oeis.org/A320949
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/HannaA320949ModThree.result
---

# Hanna's OEIS A320949 modulo-three conjecture

## Problem

Paul D. Hanna's OEIS A320949 revision 12 (2018-11-25) gives the generating equation

$$\sum_{j\ge 0}\frac{(1+x)^{j^2}}{(1+A(x))^{j+1}}=1$$

and states that $a(n)=[x^n]A(x)$ satisfies $a(n)=0\pmod 3$ for every $n>0$. The formal statement includes existence of a rational power series $A$ with constant coefficient $1$, the coefficientwise rational summation of the displayed equation, and the integer divisibility witness for each positive coefficient.

### Statement echo

| source clause | Lean counterpart |
| --- | --- |
| $A\in\mathbb Q[[x]]$ | `D5/S1/Recurrence/Invariants/HannaA320949ModThree.term` and `claim` |
| $A(0)=1$ and the coefficientwise generating equation | `IsGF` |
| existence of a rational solution | the existential conjunct of `claim` |
| every rational solution is covered | the universal implication in `claim` |
| $n\in\mathbb N$ with $0<n$ | the positive-index binder in `claim` |
| an integer $z$ with $[x^n]A=3z$ | the divisibility witness in `claim` |
| the complete published assertion is proved | `result : claim` |

The named `term` and `IsGF` definitions retain the source expressions; the auxiliary transform is private and is used only in the proof of `result`.

## Motivation

Issue [#21890](https://github.com/the-omega-institute/trureturing/issues/21890) records the source statement, proof route, and literature screen. The settling declaration is `D5/S1/Recurrence/Invariants/HannaA320949ModThree.result` and its resolution is Proved.

## Gap

The source supplied a conjectural divisibility assertion without an unbounded proof. The missing bridge was a proof that the coefficientwise equation is equivalent to an integral normalized fixed-point transform and that the transform is zero in positive degree after reduction modulo $3$.

## Route

Finite Newton expansion expresses the even integer-valued polynomial $t\mapsto\binom{t^2}{k}$ with integral forward-difference coefficients. Reciprocity of the associated geometric transform gives the finite congruence modulo $3$. The normalized coefficient transform is contractive in degree and has a unique fixed point over every commutative coefficient ring. Mapping its integral solution to $mathbb Q$ proves the source equation; uniqueness over `ZMod 3` forces every positive coefficient to vanish there.

## Falsifier

A rational solution of the displayed equation with a positive coefficient not equal to an integer multiple of three, a failure of the finite reciprocity congruence under its stated evenness and integrality hypotheses, or two distinct normalized fixed points for the transform would falsify the settlement route.

## Evidence

The kernel-checked declaration `D5/S1/Recurrence/Invariants/HannaA320949ModThree.result` proves `claim`. Its axiom closure is contained in `{propext, Classical.choice, Quot.sound}`. The source note is `Library/ArithUnits/hanna2018a320949.md`; literature completeness is `ASSUMED-UNVERIFIED` because the source is OEIS-only and no arXiv or journal settlement was identified in the recorded screen.

The independent computation is pinned to [`the-omega-institute/trureturing-experiments`](https://github.com/the-omega-institute/trureturing-experiments/tree/a38c39678a6f290beeb472aea660fd223601fc6a/docs/reports/hanna-a320949-mod3/) at commit `a38c39678a6f290beeb472aea660fd223601fc6a`. The command `python3 docs/reports/hanna-a320949-mod3/check.py` exits `0`; the script SHA-256 is `01b8e6e3f4106131672f1b930f639be577702990e79945704dd69d3f198df561`; the final line is `ALL_CHECKS_OK`.

## Triage

| item | status | evidence |
| --- | --- | --- |
| Evenness forces the finite Newton mass to vanish modulo $3$ in every positive row, and integral fixed-point uniqueness forces positive coefficients to vanish over `ZMod 3`. | proved | `result`, through `even_newton_congruence`, `newtonCoeff_mod_three`, and `normalized_exists_unique` |
| The generic finite Newton-mass congruence holds for every integral finite binomial expansion satisfying the explicit evenness hypothesis in `even_newton_congruence`. | proved | `even_newton_congruence` |
| `normalized_exists_unique` works over any commutative coefficient ring for the displayed finite transform; the source solution is obtained by mapping its integral instance to $mathbb Q$. | proved | `normalized_exists_unique`, `normalizedStep_map`, and `result` |
| The 325 geometric-moment/Newton pairs with $k+r\le24$ agree; the first 25 source coefficients match the OEIS b-file; all 24 positive checked coefficients are divisible by three. | computed | `python3 docs/reports/hanna-a320949-mod3/check.py`, exit `0`, script SHA-256 `01b8e6e3f4106131672f1b930f639be577702990e79945704dd69d3f198df561` |
| Other moduli, other exponent families, positivity, and exact three-adic valuations are not settled. | open | outside the quantified claim and the tested computation range |

### What the settlement shows

The decisive mechanism is the finite reciprocity congruence combined with degreewise uniqueness of the normalized transform. The generic congruence applies to every integral finite binomial expansion satisfying the stated evenness condition, and the fixed-point uniqueness applies over arbitrary commutative coefficient rings. The proof does not establish positivity, other moduli, other exponent families, or exact three-adic valuations.

## ASSUMED-UNVERIFIED

The literature screen is incomplete: the source is an OEIS entry without an arXiv identifier, and no exhaustive search for an independent published settlement is claimed. The finite computation is evidence for the stated finite range only and does not replace the kernel-checked infinite conclusion.
