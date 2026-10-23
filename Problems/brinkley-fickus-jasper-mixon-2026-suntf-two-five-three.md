---
slug: brinkley-fickus-jasper-mixon-2026-suntf-two-five-three
bibkey: brinkley2026incoherent
doi: 10.48550/arXiv.2610.05302
url: https://arxiv.org/abs/2610.05302v1
triage: theorem
motivation_gids:
  - D5/S3/QuantumBounds/Designs/StratifiedTightFrameTwoFiveThree.result
---

# A SUNTF_R(2, 5, 3) exists

## Problem

W. J. Brinkley, M. Fickus, J. Jasper and D. G. Mixon, *Incoherent filter banks*,
arXiv:2610.05302v1, Section 4, Example 4.4, asks whether a SUNTF_R(2, 5, 3)
exists. The last paragraph states:

> We do not yet know whether a SUNTF_R(2, 5, 3) exists, and we leave this for future research.

Definition 3.2 requires each of the R layers to be a unit norm tight frame in
dimension D and requires the averaged squared inner products between every two
distinct columns to be constant.

## Motivation

The present result settles the concrete real instance by an explicit exact
construction.

## Gap

Example 4.4 records the SUNTF_R(2, 5, 3) case as open. The formalization uses
the real field and the definitions in the paper, including repeated vectors
within a layer.

## Route

Set u = √(3/8) and v = √(5/8). The three layers have columns
(1,0), (u, s_{r,1}v), (u, s_{r,2}v), (u, s_{r,3}v), (u, s_{r,4}v), with sign
words (+,−,−,+), (+,−,+,−), and (+,+,−,−). Each layer is unit norm and tight
with frame bound 5/2. Across the three layers, the sign words of the four
non-anchor columns, namely (+,+,+), (−,−,+), (−,+,−), (+,−,−) (each of length
three), agree pairwise in exactly one position, so the averaged squared inner
products are 3/8 for every pair of distinct columns.

## Falsifier

The construction would fail if a layer were not unit norm tight or if any
ordered pair of distinct columns had an averaged squared inner product other
than 3/8. The Lean proof checks all finite cases exactly.

## Evidence

Lean source: `D5/S3/QuantumBounds/Designs/StratifiedTightFrameTwoFiveThree.lean`.
The theorem `result : ¬ claim` is equivalent to the existence statement in
the encoded claim. Its proof uses only pinned Mathlib declarations and has no
additional axioms beyond the standard Lean environment.

## Triage

`theorem`; settlement `Proved`.

### What the settlement shows

- **Proved (Lean):** a SUNTF_R(2,5,3) exists.
- **Proved (mathematical consequence):** with the paper's SUNTF_R(2,5,2),
  SUNTF_R(2,5,5) and stacking (Theorem 4.1(d)), SUNTF_R(2,5,R) exists exactly
  for R ≥ 2. R = 1 is an ETF_R(2,5), excluded by Gerzon's bound. Thus the
  threshold of Problem 4.3 for (R,2,5) is 2, not 4.
- **Computed:** across the three layers, the four non-anchor columns have
  sign words (+,+,+), (−,−,+), (−,+,−), (+,−,−), each of length three. These
  agree pairwise in exactly one position, a code with constant distance 2.
  This makes the layer averages flat.
- **Open:** Problem 4.3 in general for other D and N over R is not settled by
  this result.

## ASSUMED-UNVERIFIED

The general classification beyond the stated (D,N)=(2,5) instance is not
claimed here. The interpretation of the stacking result and Gerzon's bound is
the mathematical consequence recorded above; only the concrete existence
statement is kernel-checked in this module.
