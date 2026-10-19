---
slug: hanna-a274479-a377100-mod-three
bibkey: hanna2016a274479
doi: null
url: https://oeis.org/A274479
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/HannaGeometricSquareSubstitutionModThree.result
---

# Hanna's A274479 coefficient congruence

## Problem

Paul D. Hanna, [OEIS A274479](https://oeis.org/A274479), Name and Comments (unpaginated), as quoted in [the source note](../Library/RecurrenceComposition/hanna2016a274479.md).

> G.f. satisfies: A(x)^2 = A( x^2/(1 - 2*x - 4*x^2) ).

> a(n) = 1 (mod 3) for n>=1 (conjecture).

For $A(x)=x+\sum_{n\ge2}a(n)x^n$, the equation is
$A(x)^2=A\!\left(\frac{x^2}{1-2x-4x^2}\right)$.
The resolution is **Proved**: a normalized rational power-series solution exists, and every normalized solution has integral coefficients $a(n)\equiv1\pmod3$ for all $n\ge1$.
Preregistration: [#18850](https://github.com/the-omega-institute/trureturing/issues/18850). The other Hanna problem is separately preregistered and has its own resolution claim.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| The displayed generating equation | `HannaGeometricSquareSubstitutionModThree.IsGF` | Literal preregistered equation over rational power series, with the denominator inverse interpreted in that ring. |
| The example begins $x+x^2+\cdots$ | Constant coefficient zero and coefficient one at $X$ in `IsGF` | The normalization is explicit. |
| $a(n)$ for $n\ge1$ | `coeff n A`, with the hypothesis `1 ≤ n` | Every positive natural index. |
| Integral coefficients congruent to one modulo three | Integer witness equal to `coeff n A` and `Int.ModEq 3 m 1` in `claim` | Coercion into the rationals is explicit. |
| A generating function is defined by the equation | Existence conjunct in `claim` | Excludes a vacuous universal statement. |

## Motivation

The published entry explicitly states this coefficient congruence as a conjecture. The formal result settles that named clause under its normalization. The shared normalized-contraction theorem also supports the companion settlement #18851.

## Gap

The source and literature screen recorded in #18850 found no proof or refutation in the searched scope. It included the OEIS entry, the OEIS Open benchmark, formal-conjectures, the OEIS proof papers by Fried, and the Kallat catalogue. GPT Pro literature seat `s7999-gptpro-lit-hanna4` and the orchestrator supplied these readings. Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

The integral construction first solves the normalized reversion equation. Frobenius modulo two makes every coefficient division by two exact. Compositional inversion recovers an integral solution of the source equation. Over $\mathbb F_3$, the geometric series $x/(1-x)$ satisfies the equation. Normalized uniqueness identifies the reduction of the integral solution with this series, so all its positive coefficients are one modulo three.

The literal source predicates are `HannaGeometricSquareSubstitutionModThree.IsGF` and `HannaGeometricSquareSubstitutionModThree.claim`; the settling theorem is `HannaGeometricSquareSubstitutionModThree.result`.

## Falsifier

A normalized rational solution with a positive coefficient that is not an integer congruent to one modulo three would refute the claimed universal statement. Failure of existence would refute the existence conjunct. Finite coefficient agreement alone cannot exclude a later counterexample.

## Evidence

The Lean owner is [the settling module](../D5/S1/Recurrence/Invariants/HannaGeometricSquareSubstitutionModThree.lean); the complete statement is rendered in its [Blueprint](../Blueprint/D5/S1/Recurrence/Invariants/HannaGeometricSquareSubstitutionModThree.md). `result` proves `claim` without extra hypotheses. The shared supplier is `PowerSeriesNormalizedContraction.exists_unique_fixed`.

The axiom closure of every public declaration is contained in {`propext`, `Classical.choice`, `Quot.sound`}. Escape registration is unfinished for the new public theorems and the published suppliers: [#19089](https://github.com/the-omega-institute/trureturing/issues/19089). No validated four-slot registration is claimed.

## Triage

### What the settlement shows

**Proved, kernel-checked:** `HannaGeometricSquareSubstitutionModThree.result` establishes existence, integrality and the residue-one conclusion for every positive index and every normalized source solution.

The decisive mechanisms are the parity of the reversion residual and uniqueness after reduction modulo three. Integrality is not inferred merely from the rational recursion, which divides by two: the integral reversion supplies it. The uniqueness theorem extends to commutative domains with $2\ne0$; no characteristic-two uniqueness is claimed. Changing the parameters requires separate preservation of integrality and the reduced equation.

Neither source asymptotic claim follows from the residue result. No dependent source theorem is asserted to acquire a stronger conclusion.

### Scope of the formal results

- **Proved, kernel-checked:** `PowerSeriesNormalizedContraction.exists_unique_fixed` constructs a unique normalized fixed point over every commutative ring. Both Hanna results use it. For the distinct linear recurrence $f=1+Xf$, the constant-term law and the one-degree agreement gain follow from `UnitReversionSquareParity.agree_X`; the same theorem gives existence and uniqueness and comparison of the coefficient of $X$ gives one. This is an application of the general theorem, not another delivered theorem.
- **Proved, kernel-checked:** `HannaGeometricSquareSubstitutionModThree.equation_unique` gives normalized-solution uniqueness over a commutative domain in which $2\ne0$. No uniqueness assertion in characteristic two is made.
- **Proved, kernel-checked:** `HannaCubeSquareQuotientModThree.equation_unique` gives uniqueness among series with constant coefficient zero and linear coefficient one for the polynomial equation over every commutative ring. `HannaCubeSquareQuotientModThree.isGF_iff` connects it to the original Laurent quotient over $\mathbb Q$, with constant coefficient zero and linear coefficient one.
- **Computed:** the experiment below checks A274479 coefficients $1\ldots159$ and A377100 coefficients $1\ldots160$. It proves neither infinite congruence.
- **Open as additional formalization:** the $c,d$ parameter family for A274479 and the $+3H$ perturbation family for A377100 are not additional delivered theorems. Their conditional arguments are stated in the preregistrations; the full formalization is a separate candidate.
- **Open:** neither source asymptotic claim nor the A274478 and A274484 sibling equations is settled here.

### Experiment

[Exact finite coefficient check](https://github.com/the-omega-institute/trureturing-experiments/tree/2c5f17e977c9a3b357d84212950304c544c82383/docs/reports/oeis-a274479-a377100-hanna-mod3-geometric).
Command: `python3 /Users/auric/trureturing-experiments/docs/reports/oeis-a274479-a377100-hanna-mod3-geometric/check.py 160`; exit 0; `check.py` SHA-256 `3dc64d2201eb69e78c86686f75905b5d53d6aab3f72b08dc4bf592aace701cc0`.
The check verifies the first twelve published coefficients, integrality and residue one modulo three for A274479 indices $1\ldots159$ and A377100 indices $1\ldots160$, the equations to those respective orders, and the geometric solution modulo three. For A274479 it also checks exact division by two in the reversion recursion for $n<159$ and compositional inversion to order $158$. The tested range is finite.

## ASSUMED-UNVERIFIED

Literature-screen completeness and the absence of an unpublished or unindexed proof remain unverified. The source and literature readings are attributed to the preregistration's producers. The finite experiment does not certify an unbounded assertion. No result on the sibling equations, asymptotics or the additional parameter and perturbation families is claimed here.
