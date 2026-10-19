---
slug: hanna-a372527-square-composition-mod-four
bibkey: hanna2024a372527
doi: null
url: https://oeis.org/A372527
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/HannaSquareCompositionModFour
---

# Hanna's square-composition congruence for OEIS A372527

## Problem

Paul D. Hanna's [OEIS A372527](https://oeis.org/A372527) defines its generating function by:

> Expansion of g.f. A(x) satisfying A( A(x)^2 ) = x*A(x)/(1 - 2*A(x)).

Its conjecture reads:

> Conjecture: a(2^k + 1) == 2 (mod 4) for k >= 0, and a(n) == 0 (mod 4) for n > 0 when n is not of the form 2^k + 1.

The offset is one and the data start with $a(1)=1$. Accordingly, the zero-residue clause is asserted for $n>1$, as specified in [#18859](https://github.com/the-omega-institute/trureturing/issues/18859). The literal clause for every $n>0$ is false at $n=1$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| The displayed generating equation | `IsGF` | The literal rational formal-power-series equation, with the formal inverse of $1-2A$. |
| Offset one, first coefficient one | `IsGF` requires constant coefficient zero and degree-one coefficient one | These are the source's normalization. |
| Existence of the generating series | First conjunct of `claim`, proved by `result` | Explicit existence excludes vacuity. |
| Every $k\ge0$, coefficient at $2^k+1$ congruent to two | First universal residue clause in `claim` | An integer witness equals the rational coefficient and is congruent to two modulo four. |
| Other indices | Second residue clause in `claim`, with $n>1$ and no shifted-power representation | An integer witness equals that coefficient and is congruent to zero modulo four. |
| A selected generating series | Universal quantification over all series satisfying `IsGF` | Private `exists_integral_solution` also proves uniqueness; universality strengthens the assertion. |

The two public definitions are the expressions registered in #18859. Coefficient agreement and the power-of-two series use existing owners rather than new forwarding definitions.

## Motivation

This is a first-tier externally stated OEIS conjecture. The settling declaration is `D5/S1/Recurrence/Invariants/HannaSquareCompositionModFour.result`, with admission basis `open-problem-resolution (#18859; Proved)`. The source note is `Library/RecurrenceComposition/hanna2024a372527.md`.

## Gap

The literature screen in #18859 read the entry and its links, searched its A-number, equation and residue statement, checked the OEIS Open catalogue and the formal-conjectures repository, and searched the cited OEIS-conjecture papers, including Fried's papers and Kallat's catalogue. The GPT Pro literature seat and the orchestrator's text searches found no proof or refutation in that scope. Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

Write $A=XB$. Clearing the denominator gives
$B(1-2XB)B(X^2B^2)=1$ with constant coefficient one. The private transformation `step` takes the normalized inverse of the last two factors. `step_agree` improves coefficient-prefix agreement by one degree. The private `approximation_stable` proves agreement of the iterates at stages $d\le j$ below degree $d+1$; `normalized_agree` and `normalized_fixed` construct their diagonal integer-series limit and its fixed-point equation. `integral_equation` connects this construction to the cleared equation, and `exists_integral_solution` proves rational existence and uniqueness.

The compiled proof uses `UnitReversionSquareParity.agree_iff`, `agree_pow`, `agree_mul`, `agree_X`, `subst_inner_agree`, `subst_outer_agree` and `subst_constant`, together with its `Agree` definition. It uses `NegativePowerDiagonalModPrime.inverse_difference` for inversion. These are statements over commutative coefficient rings with the displayed coefficient or constant-term hypotheses.

For residues, let $S=\sum_{k\ge0}X^{2^k}$ over $\mathbb Z/2\mathbb Z$ and double its coefficients into $\mathbb Z/4\mathbb Z$, obtaining $d$. The used `CubicFifteenSubstitutionParity.powerTwoSeries`, `prime_power_subst`, `power_two_zero` and `thue_series_equation` give the coefficient construction and its substitution identity; `AlternatingDyadicReversionModFour.four_zero` supplies characteristic four. The private `doubleLift_annihilate` proves $2d=0$ and $d^2=0$, while `second_digit_equation` proves $d(X^2)=d-2X$. The series $X(1+d)$ therefore satisfies the cleared equation (`residue_equation`). Uniqueness identifies it with the reduction of the integer solution (`mod_four_solution`), and `residue_coefficient` gives the two classes of indices used by `result`.

## Falsifier

A rational normalized solution with a nonintegral coefficient at an index above one, a wrong residue at a shifted power of two, or a nonzero residue at any other index above one would contradict `result`. Nonexistence would contradict its first conjunct. Finite coefficient checks alone do not exclude these unbounded alternatives.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/HannaSquareCompositionModFour.lean`; public theorem `D5.S1.Recurrence.Invariants.HannaSquareCompositionModFour.result`.
- Scribe: `Blueprint/D5/S1/Recurrence/Invariants/HannaSquareCompositionModFour.scribe.cs`; the result node renders the full claim and carries one `OpenProblemResolutionClaim` of kind `Proved`.
- The nine published owner theorems retain their statements and proofs and have complete Scribe theorem nodes at their owners.
- Escape audit unfinished: [#19133](https://github.com/the-omega-institute/trureturing/issues/19133). Its targets are `result`, `NegativePowerDiagonalModPrime.inverse_difference`, `UnitReversionSquareParity.agree_iff`, `agree_X`, `subst_inner_agree`, `subst_outer_agree`, `subst_constant`, `CubicFifteenSubstitutionParity.prime_power_subst`, `power_two_zero`, and `AlternatingDyadicReversionModFour.four_zero`. No four-slot registration is claimed `declared_validated`.

### Experiment

[Exact coefficient and residue check](https://github.com/the-omega-institute/trureturing-experiments/tree/17308bdeaf5bca41113dd3b71246d281a6931cec/docs/reports/oeis-a372527-hanna-square-composition-mod4).

Command, in the pinned directory: `python3 check.py 160 b372527.txt`. Exit code: 0. Script SHA-256: `e102302b4bdb40f6665ba242db476d0aa3da06767e8e04d058d493c180a2b6b8`.

The computation verifies the equation through order 160, agreement of $a(1),\ldots,a(160)$ with the b-file, both residue clauses for $2\le n\le160$, and $a(1)=1$. It checks the equation for $X$ modulo two, and the second-digit identities $C(X^2)=XC+X^3$ and $C=\sum_{k\ge0}X^{2^k+1}$ modulo two through that same order. These are computed finite readings; the universal congruences are established by `result`.

## Triage

| Item | Status | Evidence kind |
| --- | --- | --- |
| Binding settlement for $n>1$, including existence and integer coefficient witnesses | Proved | Kernel-checked `result`. |
| $a(1)=1$ and failure of the literal zero-residue clause there | Proved in prose | The second conjunct of `IsGF` is $a(1)=1$, and $1$ is not zero modulo four; `result` supplies a solution. |
| Parameter $c\equiv2\pmod4$ in place of two | Open as a formal generalization | #18859 gives a paper argument using the division-free recursion and the same second-digit equation. No parameterized Lean theorem is delivered. |
| Residues modulo eight | Open | No theorem or numerical assertion for this modulus is delivered. |
| Separate modulo-two theorem | Open as a separate interface | The delivered statement and helper inventory contains no `mod_two_solution`; the finite modulo-two readings are computed only in the pinned experiment. |
| Formulas (2) and (3) of the entry | Open as separate claims | #18859 describes them as consequences of the generating equation; this delivery does not state or independently certify them. |
| Literature completeness | ASSUMED-UNVERIFIED | The bounded source and literature screen in #18859. |

### What the settlement shows

The decisive proved mechanism is coefficient contraction of the normalized inverse transformation, followed by uniqueness of the cleared equation over the commutative rings used in the proof. Its characteristic-four solution has a second binary digit supported exactly on shifted powers of two; this settles every index above one, without a truncation or resource bound. The endpoint $n=1$ is excluded by the defining normalization itself.

Replacing two by an integer congruent to two modulo four preserves the formal residue calculation in the paper argument of #18859, but a parameterized construction and theorem are not delivered. The modulo-eight classification remains open here. The entry's related formulas are not used as additional conjectural hypotheses. No other source result is claimed settled without a corresponding statement.

## ASSUMED-UNVERIFIED

Literature completeness and publication priority are not established by the bounded search. The $n>1$ interpretation is the explicit source-data correction registered in #18859. Formal power series do not assert analytic convergence. The four-slot escape evidence in #19133 is unfinished and is independent of the kernel proof.
