---
slug: mo516232-zero-sum-count-characterization
bibkey: johnc2026mo516232r2
doi: null
url: https://mathoverflow.net/questions/516232/when-does-the-zero-sum-sign-count-s-nd-varepsilon-in-dn-sum-vare
triage: theorem
motivation_gids:
  - D5/S0/Observation/PowerTraceCharacteristicPolynomialSaturation.power_trace_characteristic_polynomial_saturation
---

# The full zero-sum prefix-count characterization

## Problem

For every positive integer sequence satisfying a constant integer recurrence,
let $P$ be the characteristic polynomial of its minimal recurrence. For
every finite $D\subset\mathbb Z$, count the ordered original-coordinate
assignments $S_n(D)=\#\{d\in D^n:\sum d_i a_i=0\}$. The assertion is
that all these count sequences are C-finite if and only if $P$ has no
unit-circle roots, all its expanding roots are simple, and all ratios of
two expanding roots are roots of unity. The target is the entire displayed
iff of MathOverflow 516232 revision 2.

## Motivation

Cayley–Hamilton makes observations of powers of one finite matrix satisfy a
fixed recurrence. The issue is whether exact prefix counts have such a
representation under the proposed root restrictions.

## Gap

The source's sequence class includes alternating growth scales. Positive
terms need not increase, and repeated equal weights retain distinct digit
coordinates. A fixed-base word count alone does not identify these prefix
counts.

## Route

For $a_{2k-1}=4^k$, $a_{2k}=2^k$, regroup the actual prefix
coordinates by binary exponent and count their ordered local assignments.
Bounded carries give finite integer transfer matrices. Adding four to the
prefix length adds the lower pair of transfer factors on the left and the
upper pair on the right. Vectorization and a four-phase state turn that
evolution into a single integer matrix recurrence.

## Falsifier

One positive integer recurrence sequence whose exact counts are C-finite
for every finite integer digit set, and whose actual minimal polynomial
violates one asserted root clause, refutes the whole characterization.

## Evidence

The versioned source is John C's question 516232 revision 2, revision GUID
`583B6E92-78BD-4BC4-89F2-21EB26E02150`, under CC BY-SA 4.0. The corresponding
library note states the source and literature limits. The polynomial for
the displayed alternating sequence is $(X^2-4)(X^2-2)$; the ratio
$2/\sqrt2$ has modulus greater than one.

## Triage

`theorem`. The proposed resolution is a refutation of the entire iff by
falsifying its only-if direction. A replacement classification is a
separate question.

### What the settlement shows

Proved by `D5/S1/Recurrence/MoZeroSumCountRefutation.result`: the full
characterization is false. The decisive bridge retains every ordered
original coordinate while grouping weights by binary exponent. Its
multiplicity word grows by fixed factors on both ends, giving a finite
integer matrix evolution after vectorization and phase synchronization.
The proof includes every finite integer digit set, empty sets, and all
positive prefix lengths. A replacement classification, extensions to
other alternating sequences, and consequences for any other source
conjectures remain open; no such extension is asserted here.

## ASSUMED-UNVERIFIED

Historical priority and complete prior coverage by Frougny's original
1992 article remain UNKNOWN. No global openness, literature absence,
historical originality, or new-solution credit follows from the pinned
question or from bounded source retrieval.
