---
bibkey: kytola2025virasoro
authors: Kalle Kytölä
year: 2025
title: VirasoroProject, Sugawara.lean
doi: null
url: https://github.com/kkytola/VirasoroProject/blob/5ff4245383b2cdd4eea7a0524bc1274c32041eb4/VirasoroProject/Sugawara.lean
claim: The pinned Lean source proves the bosonic Sugawara commutators from Heisenberg relations and local truncation, including the Virasoro central charge one.
strata_touched: []
license: citation-only
triage: anchor
---

<!-- GID: D5/L/VertexAlgebra/kytola2025virasoro -->

# Bosonic Sugawara formalization

Kytölä's `Sugawara.lean` defines normal-ordered operators from a locally
truncated Heisenberg action. It states both the current commutator
`[L_n,J_m]=-mJ_{n+m}` and the full Virasoro commutator with central charge
one. These general statements do not themselves construct the concrete
polynomial Fock modes used in problem 2145.1.

The fixed revision uses Lean 4.34.0 and Mathlib revision
`5ed2965256430c3649e86755f9576b54eca72435`; this repository uses
Lean 4.33.0 and Mathlib revision
`db584cd6d46c92f209a44c0f1c829460d327499d`. The source is an
implementation reference, not a compiled dependency of this repository.

## Verified locator

- Commit `5ff4245383b2cdd4eea7a0524bc1274c32041eb4`,
  `VirasoroProject/Sugawara.lean`, opening documentation and named main
  statements; source and project pins checked on 29 September 2026:
  https://github.com/kkytola/VirasoroProject/blob/5ff4245383b2cdd4eea7a0524bc1274c32041eb4/VirasoroProject/Sugawara.lean
