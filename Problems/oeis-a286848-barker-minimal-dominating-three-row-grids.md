---
slug: oeis-a286848-barker-minimal-dominating-three-row-grids
bibkey: barker2017a286848
doi: null
url: https://oeis.org/A286848
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.whole_identity
---

# Barker's complete minimal-domination series for three-row grids

## Problem

Colin Barker's first generating-function conjecture in OEIS A286848 concerns
**every** labelled inclusion-minimal dominating vertex subset of the ordinary
open grid $P_3\mathbin{\square}P_n$, for every $n\ge1$.
The source note is [barker2017a286848](../Library/RecurrenceComposition/barker2017a286848.md),
and the immutable original question is preregistered in
[#22395](https://github.com/the-omega-institute/trureturing/issues/22395).
The exact settling declaration is
`D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.whole_identity`.

Let $V_n=\{1,2,3\}\times\{1,\ldots,n\}$, with adjacency exactly at Manhattan
distance one. A subset dominates if every vertex is selected or adjacent to a
selected vertex. It is inclusion-minimal if none of its proper subsets dominates.
Let $a(n)$ count all such actual labelled subsets, each once. The complete
original identity is

$$\sum_{n\ge1}a(n)x^n=P(x)Q(x)^{-1}\quad\text{in }\mathbb Q[[x]],$$

where the source's leading factor and all coefficients are

$$P(x)=x\bigl(2 + 3x - 2x^{2} - x^{3} + 4x^{4} + 10x^{5} - 14x^{6} - 32x^{7} - 29x^{8} - 2x^{9} - 21x^{10} - 140x^{11} - 140x^{12} + 126x^{13} + 80x^{14} + 127x^{15} + 143x^{16} + 695x^{17} + 401x^{18} + 462x^{19} + 582x^{20} - 8x^{21} - 490x^{22} - 660x^{23} - 721x^{24} - 960x^{25} - 714x^{26} - 925x^{27} + 25x^{28} + 206x^{29} + 255x^{30} + 494x^{31} + 155x^{32} + 443x^{33} - 118x^{34} + 80x^{35} - 71x^{36} - 172x^{37} + 78x^{38} - 105x^{39} + 79x^{40} + 7x^{41} - 28x^{42} + 33x^{43} - 7x^{44} - 4x^{45} + 3x^{46} - x^{47}\bigr),$$

$$Q(x)=1 - 2x - 2x^{2} - 4x^{3} + 8x^{4} - 2x^{5} - 2x^{6} - 23x^{7} + 14x^{8} + 31x^{9} + 31x^{10} - 45x^{11} + 50x^{12} + 83x^{13} + 122x^{14} - 141x^{15} - 54x^{16} - 105x^{17} + 36x^{18} - 85x^{19} - 275x^{20} - 222x^{21} + 63x^{22} + 90x^{23} - 140x^{24} + 253x^{25} + 399x^{26} + 234x^{27} + 190x^{28} - 87x^{29} + 59x^{30} - 219x^{31} - 222x^{32} - 189x^{33} - 270x^{34} + 152x^{35} + 56x^{36} + 123x^{37} + 158x^{38} - 41x^{39} + 75x^{40} - 62x^{41} - 12x^{42} + 21x^{43} - 30x^{44} + 7x^{45} + 4x^{46} - 3x^{47} + x^{48}.$$

Both polynomials have degree $48$; $P(0)=0$, $[x]P=2$, $[x^{48}]P=-1$,
$Q(0)=1$ and $[x^{48}]Q=1$. The inverse is a formal power-series inverse.
No analytic convergence hypothesis is involved.

### Statement echo

| Original clause | Lean counterpart |
| --- | --- |
| Actual row and column labels with open ends | `Encoding.Vertex n = Fin 3 × Fin n` and `Encoding.grid n`; labels are shifted by one |
| Closed domination, including self | Existing `SimpleGraph.IsDominating` |
| No proper dominating subset | `Encoding.MinimalDominating` quantifies over every proper finite subset |
| Each actual subset exactly once | `minimalSets`, `actualCount`, `subsetWordEquiv` and `minimalWordEquiv` |
| Every positive width | `Transfer.actualCount_one` and `Paths.actualCount_fullOrbit` at every `k`, covering widths `k+2` |
| Constant series coefficient zero | `Series.actualSeries`; the raw width-zero `actualCount` definition is unchanged |
| Every numerator and denominator coefficient | Literal `Series.numerator` and `Quotient.denominator`, with `Series.P` and `Series.Q` |
| Complete identity in rational formal series | Unconditional `Series.whole_identity : actualSeries = P * Q⁻¹` |

The count is neither minimum cardinality, independent or total domination,
cyclic boundary conditions, a symmetry quotient, nor a count of witness choices.

## Motivation

A finite-state method becomes a proof of the external identity only when it
counts the actual family without multiplicity and determines every coefficient.
The declaration above supplies that all-width identity. The local
private-neighbour characterization is established literature, credited to
[Gangloff–Talon, Proposition 1](../Library/Automata/gangloff2019dominating.md).
The particular all-state quotient, orbit certificates and complete series
assembly are repository derivations; no priority claim is made.

## Gap

The bridges are actual subsets to accepted mask words, mask words to an exact
full-state count with both open ends, the complete full-state count to a weighted
quotient orbit, and that orbit to every coefficient of the literal rational
expression. Finite agreement, rationality alone and an eventual recurrence omit
parts of this question. The six Lean modules establish these bridges without
assuming any count identity.

## Route

`Encoding.minimal_iff_closed_private` retains domination and an existential
closed private witness for every selected vertex. Its column criterion uses
five columns: a witness is at horizontal distance at most one from its selected
vertex, and any selected competitor at distance at most two. `Transfer` proves
the equivalence with numeric masks and distinguishes a real empty column from
an absent column. `Paths` sums all appended mask words once and checks both final
real centres, including the shortest two-column boundary case. Width one is
proved separately to have count two.

The resulting full transfer has $4672$ states. The $59$-class partition has a
certificate on all $73\times64$ states, including unreachable states.
Successor-list permutations preserve multiplicities. With $T$ the full operator,
$B$ the quotient operator and $R$ the lift, `Series.intertwines` proves
$TR=RB$ for every quotient vector. The terminal and initial certificates identify
the full terminal vector and the functional summing all $64$ starts. Thus
`Series.actualCount_quotient` identifies every width $k+2$ count with the
integer quotient orbit's evaluation.

The terminal-vector annihilator propagates to every orbit shift. Initial
convolutions cover degrees $0$ through $49$, including the zero degree-$49$
residual; shifted annihilation covers every degree at least $50$.
`quotientSeries_mul_Q` proves the full product identity, `Q_constant` supplies
constant coefficient one, and `whole_identity` combines the quotient formula
with the independently defined actual-subset series.

## Falsifier

A positive width with an actual labelled minimal-dominating-subset count
different from the corresponding coefficient would refute the original
identity. A failed full-state certificate or counting bijection would invalidate
that proposed proof route rather than establish a counterexample. The
unconditional kernel-checked identity rules out coefficient mismatches for the
stated graph and predicate.

## Evidence

The formal sources are
`BarkerMinimalGridEncoding`, `BarkerMinimalGridTransfer`,
`BarkerMinimalGridQuotient`, `BarkerMinimalGridPaths`,
`BarkerMinimalGridPartition` and `BarkerMinimalGridSeries`, under
`D5/S3/Combinatorics/Graph/Domination/`, with their Blueprint Scribes.
The axiom closure of every public declaration is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
The settling statement has no hypotheses. The actual subset family is defined
independently of the published polynomial data. The finite certificates are
Lean proofs; no experiment or external program output is a proof premise.

All $31$ public theorem escape audits remain **unfinished** under the exact
[target disclosure](https://github.com/the-omega-institute/trureturing/issues/22395#issuecomment-6421674861).
No Reg mirror or `declared_validated` claim is supplied. Missing evidence includes
lawful source-bound enrolled-template readout/application, realization,
source selection and reconstruction, actual-positive law, whole-family
intervention, variation and sensitivity, actual observational dependence and
current compiled bindings. This does not replace any kernel, axiom or frozen
statement check.

## Triage

| Mechanism or boundary | Status and evidence | Consequence |
| --- | --- | --- |
| Actual-subset fidelity | Proved: `Encoding.validWord_iff`, `minimal_iff_column_tests`; `Transfer.local_paddedWindow_iff` | Every labelled subset is tested for the original closed-domination and all-proper-subset minimality predicate; existential witnesses add no multiplicity |
| Local private window and open ends | Proved: `Encoding.minimal_iff_column_tests`, `Paths.runWeight_iff_tests`, `accepted_cons_iff` | Five-column information suffices for the stated graph; absent padding and both terminal real centres remain explicit |
| Every positive width | Proved: `Transfer.actualCount_one`, `Paths.actualCount_fullOrbit` | Width one has count two; widths `k+2` are covered for every natural `k` |
| All-state equitable quotient | Proved: `Partition.row_certificate`, `terminal_certificate`, `initial_certificate`; `Series.intertwines`, `lift_orbit`, `initial_sum` | All $4672$ states and their transition and start multiplicities reduce to $59$ weighted classes while retaining actual labelled counts |
| Terminal-vector and coefficient mechanism | Proved: `Quotient.finite_annihilator`, `shifted_annihilator`; `Series.initial_convolutions`, `all_later_convolutions` | Exact initial degrees $0$–$49$ and every later degree are covered; no claim that the polynomial annihilates the full matrix is needed |
| Complete original expression | Proved: `Series.quotientSeries_mul_Q`, `quotientSeries_identity`, `actualCount_quotient`, `whole_identity` | The entire literal rational formal series equals the independently defined actual-subset series |
| Scope beyond this settlement | Open: no extension theorem is supplied | Other heights, cyclic grids and other domination predicates are outside this result; minimality of the $59$-class representation and asymptotic consequences are not asserted |
| Literature priority | Unverified beyond the bounded source and searches in the source note | No exhaustive literature census or world-first claim follows from a source labelled conjectured |

## ASSUMED-UNVERIFIED

The mathematical endpoint has no unproved count assumption or additional axiom.
Equivalence between the published prose and the formal definitions remains a
source-fidelity review responsibility. The bounded literature checks do not
certify absence of every external solution. The $31$ escape audits remain
unfinished as disclosed above; their completion is not implied by successful
Lean or CI checks.
