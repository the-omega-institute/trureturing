[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

# Candidate source rows for eight-prime cores missing 3 or 5

This note records an exact arithmetic audit for three minimal proxy cores whose
prime support omits 3, 5, or both. It is a **candidate source-row and budget
calculation only**. It is not a core theorem and does not settle the
unrestricted Erdős--Selfridge problem.

The producer
[`missing_anchor_source_certificate.py`](../frontier/cover-geometry/missing_anchor_source_certificate.py)
and its pinned output
[`missing_anchor_source_certificate.json`](../frontier/cover-geometry/missing_anchor_source_certificate.json)
reuse the Chapter 30 ordinary geometry, the Chapter 31 source helper, and the
six-child conditional-kernel rows. Run:

```text
python3 -I docs/reports/erdos7-odd-covering/frontier/cover-geometry/missing_anchor_source_certificate.py
```

The checker verifies the four input SHA-256 values before evaluating exact
rational arithmetic. Its scope is intentionally narrower than the claimed
covering problem: it does not reprove the source transport, the block-cut root
orientation, the attachment/gluing argument, or the extension from the proxy
tuples to every possible core.

## Source rows

The source geometry has two anchor coordinates and six later coordinates. The
candidate target anchor pairs and exact later-prime rows are:

| case | target core proxy | source anchor image | later row | thresholds |
| --- | --- | --- | --- | --- |
| missing 3 | (\{5,7,11,13,17,19,23,29\}) | ((5,7)) | ((11,13,17,19,23,29)) | ((2,4,4,8,8,12)) |
| missing 5 | (\{3,7,11,13,17,19,23,29\}) | ((3,7)) | ((11,13,17,19,23,29)) | ((4,4,4,8,8,12)) |
| missing 3 and 5 | (\{7,11,13,17,19,23,29,31\}) | ((7,11)) | ((13,17,19,23,29,31)) | ((2,4,4,8,8,12)) |

Here “source anchor image” records the intended finite random prefix
transport. The checker records the map but does not prove that this transport
preserves every target cylinder and all source marginal bounds; that is a
separate obligation.

For the three rows the unnormalised source masses (m), joint cap (D), and
(m/D) are:

\[
\begin{array}{c|c|c|c}
\text{case}&m&D&m/D\\ \hline
\text{missing 3}&\displaystyle\frac{7332516433}{56250000000}
  &\displaystyle\frac{99}{8}
  &\displaystyle\frac{666592403}{63281250000}\\[2mm]
\text{missing 5}&\displaystyle\frac{164282173}{1171875000}
  &\displaystyle\frac{33}{2}
  &\displaystyle\frac{14934743}{1757812500}\\[2mm]
\text{missing 3,5}&\displaystyle\frac{229603051201}{1350000000000}
  &\displaystyle\frac{264}{35}
  &\displaystyle\frac{1607221358407}{71280000000000}
\end{array}
\]

All three rows have the same worst basic source vertex
((2,4,1,-1,1,0,0,0,-1)). This is a diagnostic of the pinned finite source
calculation, not a proof that the corresponding transported target source is
available.

## Budget arithmetic

The inherited root expense constant is

\[
F_* = \frac{1493}{3072},
\]
with fees (f(5)=7/24, f(7)=1/8, f(11)=1/24, f(13)=1/48), and
(f(p)=2^{-(p-1)/2}) for (p\ge17). Subtracting the non-root core fees gives

\[
E_{\text{missing 3}}=\frac7{16384},\qquad
E_{\text{missing 5}}=\frac{14357}{49152},\qquad
E_{\text{missing 3,5}}=\frac{28711}{98304}.
\]

For the missing-3 row, all displayed non-core minima begin at 31. The exact
sum of the pinned conditional-kernel rows for minima (31,37,41,43,47,53),
plus the all-large tail (2^{-28}), is the field
`large_attachment_budget_from_31` in the JSON. Its subtraction from (m) is
strictly positive (approximately (0.1303558433)). This is only the large
attachment arithmetic; it does not address where an omitted prime can occur
in the rooted block tree.

For the rows omitting 5, the Chapter 31 missing-5 placement form was evaluated
with

\[
\rho=\max_r \alpha_r c_r=\frac13.
\]

The strict-descendant and absent placements use respectively

\[
E-(1-\rho)f(5),\qquad E-f(5).
\]

For an immediate outside root block, the exact six-child proxy has cutoff 1.
The two rows are:

| case | outside proxy | (K_S) | smallest margin (m-(E-f(5)+K_S)) |
| --- | --- | --- | --- |
| missing 5 | ((5,31,37,41,43,47)) | (0.1380079614\ldots) | (0.0017522467\ldots>0) |
| missing 3 and 5 | ((5,37,41,43,47,53)) | (0.1308090193\ldots) | (0.0388705863\ldots>0) |

The JSON retains the exact fractions for (K_S), all (Z)-residuals used by
the kernel recurrence, and all three placement margins. In particular, the
positive margins are not being used as a global noncoverage claim.

## Open proof obligations

The audit leaves four independent obligations before these numbers could be
promoted to a conditional core result:

1. Prove the finite prefix transport for the intended target anchor images,
   including pullback of every original cylinder and preservation of the
   marginal caps. The source helper's numerical row alone does not establish
   this.
2. Exhaust the block-cut root orientations. A core omitting 3 or 5 can lie
   above or below those primes, and an omitted 5 can be a strict descendant,
   an immediate child of another root block, or belong to another component.
   The selected proxies must be shown to dominate every actual child minimum
   in the relevant orientation.
3. Prove one-family attachment budgets and gluing at the same transported core
   word. Independently optimised source or child laws cannot be combined.
4. Prove coordinatewise transport/monotonicity for all larger later-prime
   tuples and all skipped-prime budgets. The three rows are minimal proxies,
   not an enumeration of arbitrary eight-prime cores.

Until these obligations are discharged, the exact positive margins are useful
source evidence and regression anchors only. They do not establish a theorem
for arbitrary eight-prime cores, let alone unrestricted Erdős--Selfridge #7.
