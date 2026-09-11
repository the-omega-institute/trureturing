---
slug: oeis-a068012-correction-recurrence
bibkey: oeis2025a068012
doi: null
url: https://oeis.org/A068012
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/SubsetSums/ModSixResidueCounts
---

# Corneth's second recurrence for OEIS A068012

## Problem

Let a(n) count subsets of {1,...,n} whose element sum is zero modulo six.
David A. Corneth's September 13, 2025 FORMULA contribution states:

> a(3*k+1) = 2*a(3*k) - 2^(k-1), k >= 1, 3*k + 1 = n.

## Motivation

This is the second recurrence of a first-tier recent OEIS conjecture selected
in the orchestrator's v3 bind-first brief. Its reported finite verification
through 2000 does not prove the universal statement.

## Gap

PR #6434 resolved only the doubling recurrence, with the frozen module
`D5/S1/Recurrence/Parity/SubsetSumModSixDoubling`. The correction recurrence
requires the exact difference of counts at successive indices. This module
imports that owner and uses its C, a, and count_succ directly.

## Route

Prove the full residue table for every m >= 3 by natural-number induction
from m=3, propagating all six residues with the frozen count_succ. Write
q=m div 3. In phase m mod 3=1 the residues 2 and 5 satisfy
6*C(m,r)+2*2^q=2^m, and the other residues satisfy 6*C(m,r)=2^m+2^q.
In the other phases residues 0 and 3 satisfy 6*C(m,r)=2^m+2*2^q,
and the other residues satisfy 6*C(m,r)+2^q=2^m.

Apply the table at residue zero for 3k and 3k+1. With k>=1,
2^k=2*2^(k-1); cancellation gives
a(3k+1)+2^(k-1)=2*a(3k). This also implies the source subtraction form.

## Falsifier

A k>=1 for which a(3k+1)+2^(k-1) differs from 2*a(3k) would contradict
the theorem about the frozen subset count.

## Evidence

- Module: `D5/S1/Recurrence/SubsetSums/ModSixResidueCounts.lean`.
- Theorem: `corneth_step`.
- Full residue table: `count_closed_form`.
- Definitions and insertion recurrence belong to the frozen doubling module.
- Both theorem statements are unbounded; there is no public finite regression.

## Triage

`theorem`. The second recurrence is proved for every k>=1. The doubling
result belongs to #6434 and is not claimed as new here.

## ASSUMED-UNVERIFIED

The OEIS quotation and attribution are supplied by the orchestrator's brief
and prior source inspection. This Stage-A worker has no network and did not
repeat that inspection or third-party literature searches. First-publication
priority, exhaustive literature coverage, and OEIS revision history are not
established. The source identification is documentary; the kernel checks the
explicit mathematical statement. Stage-B emission, Scribe compilation, and
repository admission remain for the orchestrator.
