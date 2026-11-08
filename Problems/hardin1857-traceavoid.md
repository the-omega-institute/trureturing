---
slug: hardin1857-traceavoid
bibkey: hardin2011tracearrays
doi: null
url: https://oeis.org/A185761
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185761Recurrence.result
  - D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185762Recurrence.result
  - D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185763Recurrence.result
  - D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185764Recurrence.result
---

# Trace-avoiding binary arrays and the A185761–A185764 recurrences

## Problem

R. H. Hardin's four OEIS entries A185761–A185764 count labeled binary arrays of widths two, three, four and five whose contiguous $2\times2$ blocks have unequal traces at horizontally or vertically neighboring origins. The entries publish recurrences and formal generating functions; A185761 also publishes a quadratic-root closed form. The settlement proves the four formulas on their printed domains, with the literal array counts and open boundaries.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Labeled binary arrays of widths two through five | `HardinA185761Recurrence.count`, `HardinA185762Recurrence.count`, `HardinA185763Recurrence.count`, and `HardinA185764Recurrence.count` count functions into `Fin 2` through the literal matrix predicates | Literal objects and dimensions |
| Unequal traces at horizontal and vertical neighboring contiguous blocks | Each module's `valid` predicate compares `Matrix.trace (block …)` at origins differing by one row or one column | Literal adjacency and trace condition |
| Published initial values and recurrence thresholds | Each module's `claim` gives its initial count conjuncts and its recurrence implication with the printed lower bound | Same thresholds and integer arithmetic |
| Published formal generating functions | Each module's `claim` gives the corresponding identity for `PowerSeries` coefficients | Same numerator and denominator |
| A185761 quadratic-root expression for every $n\ge1$ | `HardinA185761Recurrence.claim` includes the real closed-form conjunct with `Real.sqrt 17` | Same domain and positive real square root |

## Motivation

The external assertions are preregistered in [issue #21313](https://github.com/the-omega-institute/trureturing/issues/21313) and its companion registrations #21314, #21315 and #21316. The source acknowledgement is `Library/Certificates/hardin2011tracearrays.md`. The four settling results are `HardinA185761Recurrence.result`, `HardinA185762Recurrence.result`, `HardinA185763Recurrence.result` and `HardinA185764Recurrence.result`.

The canonical Scribe resolution for this shared problem is the named set hosted by `HardinA185761Recurrence.result`, with the other three results as additional members. It maps the external questions as follows:

| External question | OEIS entry | Resolution member |
| --- | --- | --- |
| [#21313](https://github.com/the-omega-institute/trureturing/issues/21313) | A185761 | `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185761Recurrence.result` |
| [#21314](https://github.com/the-omega-institute/trureturing/issues/21314) | A185762 | `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185762Recurrence.result` |
| [#21315](https://github.com/the-omega-institute/trureturing/issues/21315) | A185763 | `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185763Recurrence.result` |
| [#21316](https://github.com/the-omega-institute/trureturing/issues/21316) | A185764 | `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185764Recurrence.result` |

## Gap

The OEIS formula fields describe these recurrences and generating functions as empirical. The missing argument is a proof that the literal finite-array counts are transported by a finite transfer matrix and therefore satisfy the displayed identities for every allowed length. Literature-search completeness remains `ASSUMED-UNVERIFIED`.

## Route

`TransferMatrix.arrayOKIffGood` identifies the neighboring-trace predicate with the local row conditions. `TransferMatrix.cardMatrix` establishes the finite-state counting identity under weighted lumping for an arbitrary finite row carrier, pair predicate, triple predicate, classifier, matrix and initial distribution. Each width-specific module encodes a binary row by a finite integer, proves the row-pair and row-triple certificate tables, identifies the literal array count with the transfer count, and propagates the tabulated matrix relation. The resulting polynomial relation yields the recurrence and coefficient comparison yields the formal generating function. The A185761 module additionally proves the quadratic-root closed form from the same recurrence and initial values.

## Falsifier

A binary array satisfying the stated predicate and violating one of the claimed initial values, recurrence identities or generating-function coefficients would contradict the corresponding `result`. For A185761, a positive index violating the displayed quadratic-root identity would contradict the same result. Width six and larger are outside the settled scope.

## Evidence

The kernel declarations are the four `result` theorems named above and the shared declarations `TransferMatrix.arrayOKIffGood`, `TransferMatrix.cardMatrix`, `TransferMatrix.scalarRelationShift` and `TransferMatrix.tabulatedPowers`. Their axiom closures are contained in `{propext, Classical.choice, Quot.sound}`. The independent checker is pinned to [commit `4aacaa6dcac239db3faa47e926b414bd36926b9b`](https://github.com/the-omega-institute/trureturing-experiments/tree/4aacaa6dcac239db3faa47e926b414bd36926b9b/docs/reports/hardin-2011-trace-avoiding-binary-arrays) at `docs/reports/hardin-2011-trace-avoiding-binary-arrays/check.py`; its SHA-256 is `b0b3e420b409da7ffd019866e25ae1caacffe313fdf72eb785056424bf5eb979`.

## Triage

1. **Proved (kernel-checked):** all four published recurrences and formal OGFs hold on their exact printed domains for the literal labeled arrays, by `HardinA185761Recurrence.result`, `HardinA185762Recurrence.result`, `HardinA185763Recurrence.result` and `HardinA185764Recurrence.result`.
2. **Proved (kernel-checked):** A185761 has the displayed quadratic-root closed form for every $n\ge1$, by the final conjunct of `HardinA185761Recurrence.claim` and its `result` proof.
3. **Proved (kernel-checked):** the common finite-state counting theorem applies to every finite row carrier, pair/triple admissibility predicates and classifier satisfying the weighted-lumping and initial-distribution hypotheses, by `TransferMatrix.cardMatrix`.
4. **Proved (kernel-checked):** the A185763 threshold $n\ge7$ is sharp: the preceding count is $75192$, while the recurrence expression at $n=6$ is $75200$; the A185764 threshold $n\ge10$ is sharp: the preceding count is $60758008$, while the recurrence expression at $n=9$ is $60757864$. The counts are the kernel-checked initial conjuncts in the corresponding `claim` definitions, and the displayed arithmetic is the finite threshold check.
5. **Computed:** the independent checker matches all 200 published terms per entry, literal small-array enumerations, exact certificate residuals and 142 applicable parent-table cells. Command: `python3 /Users/auric/trureturing-experiments/docs/reports/hardin-2011-trace-avoiding-binary-arrays/check.py`; exit code `0`; final line `ALL_CHECKS_OK`; script SHA-256 `b0b3e420b409da7ffd019866e25ae1caacffe313fdf72eb785056424bf5eb979`.
6. **Computed:** the source-certificate check matches all four Lean matrices, initial multiplicities and classifiers on valid full row pairs; the recorded widths have complement-orbit state counts $3$, $8$, $20$ and $52$, and full pair-state counts $16$, $40$, $104$ and $264$.
7. **Open:** no exact recurrence or denominator is settled here for width six or larger. The checker reports 132 complement-orbit states at width six, outside the finite certificates delivered here.

### What the settlement shows

The recurrence mechanism is a finite transfer relation: a polynomial annihilates the propagated continuation vector after the certificate burn-in, and the cardinality bridge identifies its scalar readout with the literal array count. The width-specific threshold is the first index after the certificate data; the A185763 and A185764 preceding counts show that their thresholds cannot be lowered. The same mechanism proves the four formal generating functions, and the A185761 initial values determine its quadratic-root expression. The argument applies to any finite carrier satisfying the shared weighted-lumping hypotheses, while no uniform width-six statement follows from these certificates.

## ASSUMED-UNVERIFIED

The literature screen found no published exact settlement in the searched scope; completeness and worldwide priority are unverified. The transfer-matrix method is standard, and the new result is the exact proof of the four literal-source formulas. No claim is made for width six or larger.
