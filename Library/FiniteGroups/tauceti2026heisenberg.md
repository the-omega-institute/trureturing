---
bibkey: tauceti2026heisenberg
authors: The Tau Ceti contributors
year: 2026
title: The Heisenberg group over a ring
doi: null
url: https://github.com/TauCetiProject/TauCeti/blob/29b9cc14af71b7c058316535d555c9bbf64b2df7/TauCeti/GroupTheory/SpecificGroups/Heisenberg.lean
claim: "Generic Heisenberg triples, group laws, cardinality, natural powers, native commutator formula and derived-axis equality."
strata_touched:
  - D5/S3/FiniteGroups/Heisenberg/Basic
license: Apache-2.0
triage: anchor
---

# Generic Heisenberg APIs

## Verified locator

https://github.com/TauCetiProject/TauCeti/blob/29b9cc14af71b7c058316535d555c9bbf64b2df7/TauCeti/GroupTheory/SpecificGroups/Heisenberg.lean

Source SHA-256:
`463ecf30758118dfaf714cda9a0af728ddfaf4806547aa5cf9ea8a22b79e0be7`.

The declarations `HeisenbergGroup`, `equivProd`, `card_eq`, `pow_eq`,
`commutatorElement_eq`, `zAxis`, `commutatorElement_mem_zAxis` and
`commutator_eq_zAxis` supply the consumed generic subset. Their coordinate
multiplication is (x,y,z)(X,Y,Z)=(x+X,y+Y,z+Z+xY).
The native commutator is x*y*x inverse*y inverse. Its convention is related
to the commuting-graph source by reparameterizing both generators by inversion.

Copyright 2026 The Tau Ceti contributors. Apache License, Version 2.0.
The full license terms are retained in the repository's `LICENSE`.
The pinned upstream tree contains no NOTICE file. Only the consumed subset
is ported; no upstream dependency or repository pin is changed. This port
is replaced when equivalent APIs occur in the repository's pinned Mathlib.
No determinant-incidence bijection or solution of commuting-graph Q4 is
supplied by the upstream file.
