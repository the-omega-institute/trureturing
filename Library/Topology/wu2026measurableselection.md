---
bibkey: wu2026measurableselection
authors: KT. Wu
year: 2026
title: The Kuratowski–Ryll-Nardzewski measurable selection theorem
doi: null
url: https://github.com/LeanPool/lean-pool/blob/7d5e94f7172d47c78cac7f23c0dd01cef1665e42/LeanPool/BicausalOT/BicausalOT/DescriptiveSetTheory/MeasurableSelection.lean
claim: A weak-measurable multifunction with nonempty closed values in a complete separable metric space admits a measurable selection.
strata_touched:
  - D5/S3/Topology/Selection
  - D5/S3/Topology/Measures
license: Apache-2.0
triage: anchor
---

# Source and reuse

The inspected Lean source belongs to LeanPool/lean-pool at commit
7d5e94f7172d47c78cac7f23c0dd01cef1665e42, path
LeanPool/BicausalOT/BicausalOT/DescriptiveSetTheory/MeasurableSelection.lean.
Its SHA256 is
a7f86e5daa9a7a200064e77f77a0e7d1f2dd2d99314b80ee5456b8892d7fb2d7.
The source credits KT. Wu and uses the Apache 2.0 license, whose text is
also the repository LICENSE. Its toolchain is Lean 4.35.0-rc3; the project
port targets pinned Lean and Mathlib 4.35.0.

The project Selection/Measurable module adapts the actual upstream proof:
a dense sequence, measurable least-index choices, geometric approximate
selectors, a Cauchy limit, measurable pointwise convergence and closed-value
membership. The approximation helpers are private and consumed by the
public selection theorem. Namespaces, module visibility and explicit
implicit-variable settings follow this project's source conventions.
The theorem includes an empty source type and requires no chosen target
inhabitant in that case. This is a port of a classical theorem and an
externally authored proof, with no mathematical novelty claim.

The compact metric quotient application and signed-measure lift bridge are
project derivations using this selector and pinned Mathlib pushforward and
total-variation results. They are not attributed to the upstream file.
Neither these bridges nor the selection theorem settle Talagrand's CH
recursion or Kania–Kąkol Problem 8.2.

## NOTICE attribution

The fixed upstream [NOTICE](https://github.com/LeanPool/lean-pool/blob/7d5e94f7172d47c78cac7f23c0dd01cef1665e42/NOTICE)
contains the following attribution relevant to this port:

> Lean Pool
>
> Copyright the Lean Pool contributors and the respective project authors.
>
> Lean Pool is licensed under the Apache License, Version 2.0. See the LICENSE
> file for the full license text.

Its entry under “Projects originally licensed under the Apache License,
Version 2.0” identifies `LeanPool/BicausalOT` and its original repository,
<https://github.com/maxwellapexlab/bicausalot-palomar>. That section states
that these projects are redistributed under the same Apache 2.0 license.
The per-file KT. Wu attribution and the repository's full Apache 2.0
LICENSE accompany this relevant NOTICE excerpt.

## Retirement criterion

Under spec A17.2, retire the KRN port when the Mathlib revision actually
pinned and adopted by this repository supplies the full measurable-selection
statement with its complete quantifiers, independent source and target
universes, empty-carrier case, equal-or-weaker assumptions and the same
conclusion. Verify this against that pinned revision, migrate consumers
under frozen protection to cite the upstream declaration directly, and
retire the corresponding port and approximation helpers. Retain any still
useful project measurable-section and signed-lift bridges; the availability
of KRN alone does not make those bridges redundant.
