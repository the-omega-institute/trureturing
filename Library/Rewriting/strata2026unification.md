---
bibkey: strata2026unification
authors: Strata Contributors
year: 2026
title: "Strata finite type substitution and unification"
doi: null
url: https://github.com/strata-org/Strata/tree/a74043b69b98d4197dfd7d59df1b4427dcfc3f37
claim: "The finite substitution algorithm, soundness, arbitrary-substitution MGU and normalized support invariants."
strata_touched:
  - D5/S0/Rewriting/NativeUnificationCore
  - D5/S0/Rewriting/NativeSubstitution
  - D5/S0/Rewriting/NativeTermUnification
  - D5/S0/Rewriting/UnificationCompleteness
license: Apache-2.0 OR MIT
triage: anchor
---

# Finite type unification

The pinned Strata source supplies `Constraint.unifyOne`,
`Constraints.unifyCore`, `Constraints.unify`, their soundness and
most-general-unifier proofs, and the well-formed substitution invariant.
The occurs-check and constructor-argument decomposition proofs apply to
arbitrary substitutions. The matching-completeness theorem has a separated
variable hypothesis and is not an unrestricted completeness theorem.

The local source retains the complete copyright notices, LICENSE-APACHE,
LICENSE-MIT and NOTICE inside the consumed `NativeUnificationCore.lean` source. Original
algorithms and proof telescopes are preserved. Import addresses and module
visibility follow the repository's Lean source format; local implicit-binder
options retain the upstream elaboration setting. Compatibility proof changes
handle Boolean reflection and the equation indexing a recursive match.

Retirement is local: replace the port by direct references when this
repository's pinned dependency contains equivalent usable declarations for
the consumed closure. Acceptance elsewhere is insufficient.

## Verified locator

https://github.com/strata-org/Strata/tree/a74043b69b98d4197dfd7d59df1b4427dcfc3f37

The immutable commit contains `leanprover/lean4:v4.31.0`; this repository uses
Lean 4.33.0. The adopted proof sources are the Lean files at this commit,
not external prose sketches or other unification implementations.
