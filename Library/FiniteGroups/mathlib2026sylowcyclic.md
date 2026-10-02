---
bibkey: mathlib2026sylowcyclic
authors: Mathlib contributors
year: 2026
title: Sylow theory and automorphisms of finite cyclic groups in Mathlib
doi: null
url: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/GroupTheory/Sylow.lean
claim: Sylow conjugacy, counting, and characteristic unique Sylow subgroups, together with the totient cardinality of the automorphism group of a finite cyclic group.
strata_touched:
  - D5/S3/FiniteGroups/CycleNineThreeObstruction
license: Apache-2.0
triage: anchor
---

# Sylow and cyclic-group inputs

`IsPGroup.toSylow` identifies a prime-power subgroup of index coprime to the prime as a Sylow subgroup. `Sylow.isPretransitive_of_finite` supplies conjugacy, while `Sylow.card_dvd_index` and `card_sylow_modEq_one` supply the divisibility and congruence of its count. `Sylow.characteristic_of_subsingleton` makes a unique Sylow subgroup characteristic. A characteristic subgroup of a normal subgroup is normal in the ambient group.

In `Mathlib/GroupTheory/SpecificGroups/Cyclic.lean`, `IsCyclic.card_mulAut` identifies the cardinality of the automorphism group of a finite cyclic group with the totient of its cardinality. For a cyclic group of order three, this cardinality is two. These statements are inputs to the obstruction; none states the complete orders-nine-three-two contradiction.

## Verified locator

- URL: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/GroupTheory/Sylow.lean
- Cyclic-group source: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/GroupTheory/SpecificGroups/Cyclic.lean
