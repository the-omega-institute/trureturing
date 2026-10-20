---
slug: hanna-bilateral-reversion-parity
bibkey: hanna2024a379202
doi: null
url: https://oeis.org/A379202
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/HannaBilateralReversionParity.result
---

# Hanna's bilateral reversion parity conjecture

## Problem

P. D. Hanna's [OEIS A379202](https://oeis.org/A379202), Name section, states:

> G.f. A(x) satisfies 1/x = Sum_{n=-oo..+oo} A(x)^n * (A(x)^n + 2)^(n+1).

Its Comments section states:

> Conjecture: a(n) is even for n > 1.

The offset is one and the first coefficient is one. The formal solution is
$A\in\mathbb Q[[X]]$ with $A(0)=0$ and $[X]A=1$. Integer powers and inversion
are taken in the field $\mathbb Q((X))$. For each natural $j$, the coefficient
at degree $j-1$ is the sum over $-j-2\le n\le j+2$; all omitted summands
have zero coefficient at that degree. The source is recorded in the
[Library note](../Library/RecurrenceComposition/hanna2024a379202.md).
Preregistration: [#18876](https://github.com/the-omega-institute/trureturing/issues/18876).

### Statement echo

All Lean names below belong to
`D5.S1.Recurrence.Invariants.HannaBilateralReversionParity`.

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| $A^n(A^n+2)^{n+1}$ for integer $n$ | `term` | Literal Laurent-series integer powers. |
| Sum over all integer indices | `bilateralSum` | Coefficientwise finite window; `outside_window` and `literal_finite_window` prove that omitted coefficients vanish. |
| $1/X$ equals the bilateral sum | `IsGF` | Literal Laurent inverse of $X$. |
| Offset one, first entry one | Two normalization conjuncts of `IsGF` | Zero constant coefficient and linear coefficient one. |
| Coefficient $a(n)$ for every $n>1$ | Natural binder and strict inequality in `claim` | Index one is excluded. |
| Integer, even coefficient | Integer witness and `Even` in `claim` | Witness is cast to the rational coefficient. |
| Generating series exists | Existential conjunct of `claim` | An additional conclusion, with no added hypothesis. |
| Uniqueness in the preregistered settlement statement | Private `solution_unique` | Every normalized solution equals the same rational image of the integral inverse. |
| Any generating series satisfying the equation | Universal series binder and `IsGF` hypothesis | No selected solution replaces the source's solution class. |

No source clause is dropped. The full proposition appears at both the
`claim` and `result` Blueprint nodes.

## Motivation

Bilateral Laurent summation connects the source equation to an integral
power-series reversion problem. Pairing the integer indices retains their
common generating series and exposes a characteristic-two cancellation.
The settling node is
`D5/S1/Recurrence/Invariants/HannaBilateralReversionParity.result`.

## Gap

The source and literature screen recorded in #18876 found no proof or
refutation of this conjecture. The screen includes the entry and its links,
OEIS-proof papers, the OEIS Open benchmark, formal-conjecture catalogues,
and a GPT Pro literature search. Completeness is `ASSUMED-UNVERIFIED`.
The settlement uses the literal rational Laurent-series conventions above.

## Route

For $n=-m<0$, factor $A^{-m}+2=A^{-m}(1+2A^m)$. The summand becomes
$A^{m^2-2m}(1+2A^m)^{1-m}$. Isolate the pole at $n=-1$ and pair $n=k$
with $n=-k-2$. Both members reduce to $A^{k(k+2)}$ modulo two, so their
sum vanishes. Thus $S(X)=X^{-1}T(X)$ for an integral series $T$ with
$T(0)=1$ and $T\equiv1\pmod2$.

The integral series $B=X/T$ has linear coefficient one. Its integral
compositional inverse reduces to $X$ modulo two. Laurent normalization
identifies every rational solution of the source equation with this inverse.
The proof uses `CompositionalIterateCongruence.agree_subst`,
`QuotientThetaCompositionModFour.map_inverse`,
`BilateralProductModFour.ofSeries_inverse`, and
`ContinuedFractionOddSquare.inverse_one` on its elaborated dependency path.
The latter is an existing public owner on dev, with its publication audit in
[issue #19167](https://github.com/the-omega-institute/trureturing/issues/19167).

## Falsifier

A normalized solution with a noninteger coefficient, or an odd coefficient
at any index greater than one, contradicts `result`. A different interpretation
of the bilateral sum or of the zero and linear coefficients changes the
source-to-formalization correspondence and is outside this statement.

## Evidence

`D5.S1.Recurrence.Invariants.HannaBilateralReversionParity.result` proves
`claim`: a solution exists, and every normalized solution has integer, even
coefficients for all $n>1$. The private `solution_unique` identifies every
such solution with the rational image of the integral compositional inverse.
The module's admission basis is `open-problem-resolution (#18876; Proved)`;
its declarations are classified as bind-only, with consumed private helpers
and no escape witness. The external named-problem settlement supplies the
admission basis. The axiom closure of every public declaration is contained
in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The four-slot escape audit is unfinished under
[issue #19114](https://github.com/the-omega-institute/trureturing/issues/19114).
Its targets are this `result`,
`CompositionalIterateCongruence.agree_subst`, and
`BilateralProductModFour.ofSeries_inverse`. The published predicate
`CompositionalIterateCongruence.Agree` is also included in the requested
publication audit; as a definition it is outside the machine theorem-registration
selection. Its complete defining formula is mirrored in its owner Scribe.
Faithful reconstruction of their complete source families, lawful enrolled
readouts, and variation/dependence evidence are not supplied by this delivery.
No `declared_validated` registration is claimed.

### Experiment

[Published checker and data](https://github.com/the-omega-institute/trureturing-experiments/tree/2837dd62974ead653edc8f27ee76b66361b331e3/docs/reports/oeis-a379202-hanna-bilateral-reversion-parity).
Command in the pinned directory: `python3 check.py 160 b379202.txt`; exit 0,
`RESULT PASS`. The pinned `check.py` SHA-256 is
`de4cf6358a81c1cbf2aec250444a05e7f192f36bc3ae4d2583d8bac6e9638f9c`.
Literal and folded negative summands agree for $1\le m\le6$.
The computed truncations have integral $T\equiv1\pmod2$ and $B\equiv X\pmod2$;
$B(A)=X$ holds through degree 160, the coefficients agree with the source
b-file for $1\le n\le160$, and $X S(A)=1$ holds through degree 159.
Evenness is checked for $1<n\le160$. These are finite computations, separate
from the uniform kernel-checked result.

## Triage

### What the settlement shows

| Item | Status | Evidence |
| --- | --- | --- |
| Pair $n=k$ with $n=-k-2$ after isolating the $n=-1$ pole; cancel modulo two before reversion | Proved, kernel-checked | Private `negative_fold`, `normalized_sum`, `pair_mod_two`, `T_mod_two`, `integralA_mod_two`, and public `result`. |
| Replace $2$ by an arbitrary even integer $c$ | Open; `ASSUMED-UNVERIFIED`, not formalized | The displayed factorization suggests the same argument when $c\equiv0\pmod2$; only the binding $c=2$ proposition is proved here. |
| Separate mod-four observation involving A028309 | Open; not addressed | The source Comments section makes this separate observation; no mod-four conclusion is asserted. |

The decisive mechanism is equality of the two exponents modulo two before
composition is inverted. This proves the source's evenness conjecture for
all $n>1$. The separate mod-four observation receives no additional evidence
from this settlement. No further source theorem dependent on the conjecture
is identified by the literature screen recorded in #18876; that screen's
completeness remains `ASSUMED-UNVERIFIED`.

## ASSUMED-UNVERIFIED

Literature-search completeness and the absence of an external settlement
outside the searched material are `ASSUMED-UNVERIFIED`. The arbitrary-even-$c$
extension is not formalized. The A028309 mod-four observation is open.
The unfinished escape audit does not supply registration validation.
