---
slug: hardin-a235281-diagonal-recurrence
bibkey: hardin2014a235281
doi: null
url: https://oeis.org/A235281
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235281DiagonalRecurrence.result
---

# Hardin's seven-lag recurrence for constant-stress square arrays

## Problem

OEIS A235281 counts literal indexed $(m+1)\times(m+1)$ arrays over
$\{0,1,2,3\}$ for which every contiguous $2\times2$ block has absolute
difference four between its diagonal and antidiagonal sums. Its offset
is `1,1`. Let $a(m)$ denote the count at the positive index $m$. The
empirical formula, with the source's left-hand index written as $m+7$, is

$$
a(m+7)=a(m+6)+9a(m+5)-9a(m+4)-26a(m+3)+26a(m+2)+24a(m+1)-24a(m)
\qquad (m\ge1).
$$

The exact source lines are in the [Library note](../Library/Automata/hardin2014a235281.md).

### Statement echo

| Source clause | Lean counterpart |
| --- | --- |
| Literal indexed squares over four symbols | The two arguments of the predecessor's `T` are equal. At index `m`, its grid is `Fin (m + 1) → Fin (m + 1) → Fin 4`. |
| Every contiguous block has absolute diagonal difference four | The predecessor's `Legal` tests each upper left corner with `Int.natAbs` of the difference of the two integer sums. |
| Literal cardinality and signed lags | The predecessor's `T` casts the cardinality of the legal subtype to integers. The diagonal `result` uses the seven coefficients $1,9,-9,-26,26,24,-24$ in descending lagged-index order. |
| Positive offset | The base index has type `Nat` and hypothesis `1 ≤ m`. The left side starts at index eight. |

## Motivation

The published empirical assertion is a relation among square counts.
The rectangular count gives a literal representation of these squares as
its diagonal, and transposition relates the dependence on the two varying
dimensions. [Preregistration #34242](https://github.com/the-omega-institute/trureturing/issues/34242)

## Gap

The OEIS formula is empirical in revision 9. The preregistration's bounded
literature screen found no proof of the full diagonal recurrence.
The catalogued rectangular result supplies the profile sum and the
transposition identity used here. [Preregistration source screen](https://github.com/the-omega-institute/trureturing/issues/34242)

## Route

A row with prescribed adjacent sums is determined by a single cell.
Bounding the complementary fiber sizes at each edge leaves three positive
pairs for nonconstant profiles. The constant profiles supply the three
other contributions. Let $C(k)$ and $D(k)$ count the nonconstant pairs
$(1,1)$ and $(1,2)$ among profiles of width $k+2$. Complementation pairs
$(1,2)$ with $(2,1)$. The rectangular count at indices $(n+1,k+1)$ is
$2(U(n)+C(k)+D(k)V(n))$, where $U$ gives the constant-profile count
and $V$ is the combined row product for the last two nonconstant types.

Transposing the width-two family eliminates $C(k)$. Transposing against
width three gives $2D(k)=D(1)(V(k)-4)$. On the diagonal the count is
$4U(n)-2U(0)+D(1)(V(n)-4)^2$. Its summands have two-step multipliers
two, three or four, or are constant. The polynomial
$(E-1)(E^2-2)(E^2-3)(E^2-4)$ annihilates their sum for the forward
shift $E$.

## Falsifier

An exact legal square count that violates the signed identity at any
positive base index $m$ would refute the published recurrence.

## Evidence

The settling declaration is
`D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235281DiagonalRecurrence.result`.
Its axiom closure is `propext`, `Classical.choice` and `Quot.sound`.
The Lean statement uses the exact predecessor count and all seven signed
terms. [Mathematical settlement of #34242](https://github.com/the-omega-institute/trureturing/issues/34242#issuecomment-7174298147)

## Triage

### What the settlement shows

The width comparisons determine the coefficient needed on the diagonal
from the width-three coefficient. The diagonal argument uses the
rectangular profile sum and transposition. The rectangular six-lag theorem
applies to slices with one index fixed. The seven-lag identity applies
when both indices increase together. Minimal order and alphabet extensions
are separate questions.

## ASSUMED-UNVERIFIED

The preregistration leaves global literature coverage, the complete
citation graph and unavailable publisher material unverified.
