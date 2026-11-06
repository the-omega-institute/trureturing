---
slug: hardin-a206981-width-two-recurrence
bibkey: hardin2012a206981
doi: null
url: https://oeis.org/A206981
triage: theorem
motivation_gids:
  - D5/S1/Words/AdmissibleWords/HardinWidthTwoRecurrence.result
---

# Hardin's width-two array recurrence and generating function

## Problem

R. H. Hardin's OEIS A206981, revision 17, states in its NAME:

> Number of n X 2 0..1 arrays avoiding the patterns 0 1 0 or 1 0 1 in any row, column, diagonal or antidiagonal.

Its first FORMULA states:

> Empirical: a(n) = 2*a(n-1) + 2*a(n-2) - a(n-3). G.f.: -4*x*(-1-2*x+x^2) / ( (1+x)*(x^2-3*x+1) ).

Its OFFSET is `1,1`. The source has no DOI or arXiv identifier. The source
note is `Library/Automata/hardin2012a206981.md`; preregistration is
[#24139](https://github.com/the-omega-institute/trureturing/issues/24139).

For the actual source-array count $a(n)$, the proved assertion is

$$
\forall n\ge4,\quad a(n)=2a(n-1)+2a(n-2)-a(n-3),
$$

and, with $G(X)=\sum_{n\ge1}a(n)X^n$ as an integer formal power series,

$$
G(X)(1-2X-2X^2+X^3)=4X+8X^2-4X^3.
$$

The denominator equals $(1+X)(X^2-3X+1)$ and has constant coefficient
one. Thus clearing the denominator preserves the source's rational
formal-series assertion. It imposes no analytic convergence assumption.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Binary $n\times2$ arrays | `Fin n → Fin 2 → Bool` in `a` | All heights; ordinary rectangles without wraparound. |
| Patterns 010 and 101 | `Forbidden` | Both literal Boolean triples. |
| Row, column, diagonal, antidiagonal | `StraightTriple` and `Avoids` | Four unit steps; every cell stays in bounds; coordinates use integers. |
| Number of arrays | `a` | `Nat.card` of the actual finite subtype, independent of a recurrence. |
| Recurrence | First conjunct of `claim` | Every $n\ge4$; count subtraction in integers and guarded natural lag indices. |
| OFFSET 1,1 | `gf` | Constant coefficient zero; positive coefficients are the actual counts. |
| Generating function | Second conjunct of `claim` | Exact denominator-cleared equality in `PowerSeries ℤ`. |
| Both assertions hold | `result` | No additional hypothesis. |

## Motivation

The settling GID is
`D5/S1/Words/AdmissibleWords/HardinWidthTwoRecurrence.result`.
The complete source assertion is proved for the literal finite array
family. The module's admission basis is
`open-problem-resolution (#24139; Proved)`, with `generality: G` and
`utility: none`. Its only public theorem is `result`; its helpers are
private and used by the settlement. Their proof shape is bind-only,
using existing enumeration and reconstruction laws with normalization.

## Gap

The literature screen in #24139 located no proof of the actual-array
assertion in its inspected scope. The related Fibonacci-square sequences
and numerical programs do not by themselves identify the source arrays.
The source-array correspondence is the obligation closed here.

The screen includes the OEIS source and related entries, inspected
secondary papers, public Lean and sequence-program searches, MathOverflow,
Zenodo and arXiv metadata searches. Blake's run-length paper and Falcon's
product-of-Fibonacci paper were not available in full text; the complete
citation graph and global arXiv full-text exclusion remain
`ASSUMED-UNVERIFIED`. This is a scoped literature result, not a universal
priority claim. The second empirical FORMULA of the entry is outside this
settlement.

## Route

In width two, an in-bounds length-three source segment must be vertical.
Consequently the array subtype is the product of two independent legal
column subtypes. For a positive-length column, retain its first bit and
record adjacent XOR switches. The patterns 010 and 101 occur exactly
when two successive switches are true. This is the existing predicate
`AdmissibleCount.Adm`.

The proof uses `AdmissibleCount.adm_iff_no_adjacent_true` and
`AdmissibleCount.admissibleWord_card_eq_fib` from its direct D5 import.
Mathlib's `Fin.partialSum_right_neg` and `Fin.partialSum_left_neg`
reconstruct a Boolean column from its first bit and switches. Transporting
cardinalities gives $2F(n+1)$ legal columns and $4F(n+1)^2$ arrays for
$n\ge1$. The Fibonacci recurrence and polynomial normalization give the
order-three recurrence. Formal-series coefficient comparison, using
initial counts $4,16,36$, gives the generating-function equality.

## Falsifier

A counterexample is an actual source array or count for which either
conjunct of `claim` fails, with the same direction, boundary and offset
conventions. The all-height conclusion is kernel-checked, not extrapolated
from finite numerical agreement. Width three is outside its hypotheses:
horizontal forbidden triples already exist at height one.

## Evidence

The kernel-checked public theorem is
`D5.S1.Words.AdmissibleWords.HardinWidthTwoRecurrence.result`.
Its axiom closure is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
The Scribe renders the expanded conjunction and has one
`OpenProblemResolutionClaim` of kind `Proved` on that theorem.

The published finite experiment is
[the Hardin experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/b0800bd338881bb5a780e123697f113469827cfa/docs/reports/hardin-a206981),
at commit `b0800bd338881bb5a780e123697f113469827cfa`, program
`docs/reports/hardin-a206981/check.py`, SHA-256
`08e9f38ca2fe193dbc5fbafd8f06260e6159eca0391fbc789c0bab24fa0e40d8`.
The immutable program was extracted from that commit and run with
`python3 /Users/auric/.sshx/7130f7d87b2e4002356ccf3c/attempt-1/experiment-check.py`,
exit 0, final result `ALL_CHECKS_OK`. Its scope is literal array counts at
heights $1,\ldots,8$; row-state dynamic counts, the Fibonacci-square identity
and OGF coefficients through height/degree $210$; the recurrence for
$n=4,\ldots,210$; and both switch inverse checks and pattern equivalence
on all $2,046$ binary words of lengths $1,\ldots,10$.
These are finite computations, separate from the all-height proof.

The escape audit for `result` is unfinished:
[#26280](https://github.com/the-omega-institute/trureturing/issues/26280).
The enrolled dependent-family template requires a compiled faithful source
realization, source-occurrence selection, actual observational dependence,
and its binding checks. No successful Reg registration is delivered.

## Triage

| Item | Status and evidence |
| --- | --- |
| Width-two source constraints factor into independent legal columns at every height. | Proved, kernel-checked private `straight_iff`, `avoids_iff` and `arrayEquiv`, used by `result`. |
| At positive height $n$, $a(n)=4F(n+1)^2$ and each column has count $2F(n+1)$. | Proved, kernel-checked private `column_card` and `array_count`, used by `result`. |
| Literal counts through height 8, dynamic counts and identity through 210, both switch inverse checks on 2,046 words, and OGF coefficients through 210. | Computed, the immutable experiment and exit-0 command in Evidence, at exactly those scopes. |
| At width three and height one there are six valid rows, versus eight under independent columns; the height-zero width-two array count is one. | Proved in prose by the finite derivation below; these boundary claims are not delivered Lean theorems. |
| Wider-array recurrence or all-width enumeration. | Open. Horizontal and diagonal constraints must be retained; this theorem supplies no such enumeration. |

### What the settlement shows

The decisive mechanism is independence of the two columns and the switch
representation of a legal column, not a recurrence assumed in the
count's definition. The all-height cardinality formula and the source
recurrence and generating function are proved in the module as named
above. There is no extra positivity, generic-position or convergence
hypothesis.

For the finite neighbouring boundary, a single row of width three has
$2^3=8$ binary fillings and precisely one in-bounds horizontal triple.
Exactly 010 and 101 are excluded, leaving the six rows
$000,001,011,100,110,111$. Independent columns would allow all eight.
This is a complete finite derivation, so the boundary is recorded as
proved in prose rather than dependent on an unpublished computation.
At height zero the domain of an array is empty; there is exactly one
function from that domain, and it vacuously avoids every triple.
The actual count $a(0)=1$ is therefore compatible with the separately
defined offset-one series having constant coefficient zero.

The width-two argument does not extend unchanged to width three, and
supplies no all-width recurrence. It settles both parts of the first
FORMULA and removes their empirical status within these conventions.
It neither establishes the entry's second empirical formula nor settles
claims about wider arrays. Those remain independent questions.

## ASSUMED-UNVERIFIED

Literature completeness, global priority, unread Blake and Falcon full
texts, the full citation graph and a global arXiv full-text screen remain
`ASSUMED-UNVERIFIED`. The source's meaning and its correspondence with the
formal conventions are fidelity claims; the Lean kernel proves statements
about those explicit conventions. Escape-registration completion is not
claimed and is tracked by #26280.
