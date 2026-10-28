---
slug: hanna-a377100-mod-three
bibkey: hanna2024a377100
doi: null
url: https://oeis.org/A377100
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/HannaCubeSquareQuotientModThree.result
---

# Hanna's A377100 coefficient congruence

## Problem

Paul D. Hanna, [OEIS A377100](https://oeis.org/A377100), Name and Comments (unpaginated), as quoted in [the source note](../Library/RecurrenceComposition/hanna2024a377100.md).

> G.f. A(x) satisfies A(x) = A(x^3)/A(x^2) + A(x)^2.

> Conjecture: a(n) == 1 (mod 3) for n >= 1, which has been verified for the initial 2305 terms.

For $A(x)=x+\sum_{n\ge2}a(n)x^n$, the equation is
$A(x)=\frac{A(x^3)}{A(x^2)}+A(x)^2$.
The resolution is **Proved**: a normalized rational power-series solution exists, and every normalized solution has integral coefficients $a(n)\equiv1\pmod3$ for all $n\ge1$.
Preregistration: [#18851](https://github.com/the-omega-institute/trureturing/issues/18851). The other Hanna problem is separately preregistered and has its own resolution claim.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| The displayed generating equation | `HannaCubeSquareQuotientModThree.IsGF` | Literal preregistered equation over rational power series; the A377100 quotient is in Laurent series. |
| The example begins $x+x^2+\cdots$ | Constant coefficient zero and coefficient one at $X$ in `IsGF` | The normalization is explicit. |
| $a(n)$ for $n\ge1$ | `coeff n A`, with the hypothesis `1 ≤ n` | Every positive natural index. |
| Integral coefficients congruent to one modulo three | Integer witness equal to `coeff n A` and `Int.ModEq 3 m 1` in `claim` | Coercion into the rationals is explicit. |
| A generating function is defined by the equation | Existence conjunct in `claim` | Excludes a vacuous universal statement. |

## Motivation

The published entry explicitly states this coefficient congruence as a conjecture. The formal result settles that named clause under its normalization. The shared normalized-contraction theorem also supports the companion settlement #18850.

## Gap

The source and literature screen recorded in #18851 found no proof or refutation in the searched scope. It included the OEIS entry, the OEIS Open benchmark, formal-conjectures, the OEIS proof papers by Fried, and the Kallat catalogue. GPT Pro literature seat `s7999-gptpro-lit-hanna4` and the orchestrator supplied these readings. Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

Writing $A=XB$ with $B(0)=1$ gives a strict coefficient contraction with integral operations and unit denominator $B(X^2)$. It constructs an integral fixed point. Over $\mathbb F_3$, Frobenius gives $1-X^3=(1-X)^3$, and the geometric series satisfies the polynomial equation. Uniqueness identifies the reduced integral solution with that series. The original quotient is recovered in the Laurent-series field over $\mathbb Q$.

The literal source predicates are `HannaCubeSquareQuotientModThree.IsGF` and `HannaCubeSquareQuotientModThree.claim`; the settling theorem is `HannaCubeSquareQuotientModThree.result`.

## Falsifier

A normalized rational solution with a positive coefficient that is not an integer congruent to one modulo three would refute the claimed universal statement. Failure of existence would refute the existence conjunct. Finite coefficient agreement alone cannot exclude a later counterexample.

## Evidence

The Lean owner is [the settling module](../D5/S1/Recurrence/Invariants/HannaCubeSquareQuotientModThree.lean); the complete statement is rendered in its [Blueprint](../Blueprint/D5/S1/Recurrence/Invariants/HannaCubeSquareQuotientModThree.md). `result` proves `claim` without extra hypotheses. The shared supplier is `PowerSeriesNormalizedContraction.exists_unique_fixed`.

The axiom closure of every public declaration is contained in {`propext`, `Classical.choice`, `Quot.sound`}. Escape registration is unfinished for the new public theorems and the published suppliers: [#19089](https://github.com/the-omega-institute/trureturing/issues/19089). No validated four-slot registration is claimed.

## Triage

### What the settlement shows

**Proved, kernel-checked:** `HannaCubeSquareQuotientModThree.result` establishes existence, integrality and the residue-one conclusion for every positive index and every normalized source solution.

The decisive mechanism is a division-free normalized contraction followed by uniqueness modulo three. The polynomial-equation uniqueness statement extends to every commutative ring. The Laurent quotient is interpreted over $\mathbb Q$ in the formal source statement. Algebraic rearrangements in formulas (2) and (3) are not counted as further conjectures. A $3H$ perturbation requires its own preservation and contraction arguments and is not an additional delivered theorem.

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
