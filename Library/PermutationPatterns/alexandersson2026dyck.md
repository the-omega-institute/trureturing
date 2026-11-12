---
bibkey: alexandersson2026dyck
authors: Per Alexandersson
year: 2026
title: "The Narayana distribution of Dyck-word peaks (RealRooted DyckStatistics)"
doi: null
url: https://github.com/PerAlexandersson/RealRooted/blob/27276f93bbaf6b46bce689bca110bbacab1bba6b/RealRooted/Mathlib/Combinatorics/Enumerative/DyckStatistics.lean
claim: "Actual Mathlib Dyck-word peak fibers have Narayana cardinality, with explicit zero-peak exceptions."
strata_touched:
  - D5/S3/Combinatorics/OrdinaryAscent/DyckNarayana
license: Apache-2.0
triage: anchor
---

# Alexandersson, Dyck-word Narayana statistics

The exact supplier is RealRooted commit 27276f93bbaf6b46bce689bca110bbacab1bba6b,
`RealRooted/Mathlib/Combinatorics/Enumerative/DyckStatistics.lean`, SHA256
0421ff0edbddb5c6616719282832e3cb1081be0cea91b1a29b19ddd6d2f6708b.
Copyright 2026 Per Alexandersson. The Apache 2.0 copyright notice, proof credit
to Aristotle (Harmonic), complete license, corrected hypotheses and excluded-case
theorem are retained in the adapted Lean source. Adaptations are limited to the
project header, exposing the two step-count helpers for the actual ordinary-word
consumer, and embedding the license. No package dependency or toolchain upgrade
is introduced. The supplied source and manifest use the same Lean 4.35.0 and
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.

`DyckWord.card_semilength_peakCount` assumes not (n=1 and k=0);
`Nat.narayana_mul` assumes n is nonzero and k is nonzero. A separate theorem gives
zero for the actual n=1,k=0 fiber. Natural subtraction in k-1 makes the unguarded
quotient unsuitable at zero peaks. The ordinary-word consumer discharges these
hypotheses using 0 <= r < n and k=n-r. The statistic is adjacent UD in an actual
Mathlib DyckWord. This supplier alone proves no ordinary-avoider equivalence,
statistic transport, peak polynomial equation or Lagrange formula over Q[y].
