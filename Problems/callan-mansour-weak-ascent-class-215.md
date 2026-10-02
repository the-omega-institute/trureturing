---
slug: callan-mansour-weak-ascent-class-215
bibkey: callan2025ascent
doi: 10.5281/zenodo.17144266
url: https://math.colgate.edu/~integers/z80/z80.pdf
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/WeakAscent/WeakAscentClass215.result
---

# Weak Ascent Sequences Avoiding {100, 101, 110, 201} and {021, 101, 201, 210}

## Problem

David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of
Length-3 Patterns*, Integers 25 (2025), #A80, Section 1 and Table 2:

> Theorem 2. The number WAS4 of WA-Wilf-equivalence classes among quadruples of length-3 patterns is
> either 228 or 229. The slight ambiguity in Theorem 2 is because the status of Class 215 is left open in
> Table 2 below.

Table 2 lists Class 215 as the pair {100, 101, 110, 201} and {021, 101, 201, 210}, marked "Open".

## Motivation

The theorem `D5/S3/Combinatorics/WeakAscent/WeakAscentClass215.result` establishes that the two sets are
WA-Wilf-equivalent: for every n, equally many weak ascent sequences of length n avoid each set. With the
rest of the classification this gives WAS4 = 228. The common generating function A(z), including the empty
sequence, is the unique power series with A = 1 + zA^2/(1 − z^2A^2).

## Gap

Pre-registration issue 11771 records the literature screen: no located later paper, OEIS entry or public
repository settles Class 215. This is a bounded negative finding.

## Route

1. The append criteria of both classes are determined exactly; for the left class a stack of closed
   intervals spanned by inversions, together with the largest repeated value, decides which letters can be
   appended.
2. The left class is encoded by an exact stack generating tree; pure histories give an invertible
   decomposition, and a renewal at old steps eliminates the stack variable.
3. The right class has a separate two-label generating tree, which is solved with the same series, so both
   generating functions satisfy A = 1 + zA^2/(1 − z^2A^2).

## Falsifier

The statement would fail if either append criterion misclassified a letter, if a decomposition missed or
repeated a sequence, or if the two series differed in some coefficient.

## Evidence

Two independently implemented counters agree through length 14, and every avoiding prefix through length
11 was checked against the structural lemmas.

## Triage

`theorem`; the statement is the open Class 215 of Callan and Mansour's classification and is quantified
over every n.

## ASSUMED-UNVERIFIED

The literature screen is limited to the citation and full-text searches, the OEIS entries and the GitHub
and repository checks recorded above.
