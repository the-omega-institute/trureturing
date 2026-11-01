---
bibkey: cfsg-frattini-kernel
authors: Qiuzhen-CFSG contributors
year: 2026
title: CFSG Frattini automorphism kernel
url: https://github.com/Qiuzhen-CFSG/CFSG/blob/0c6635528a02dd46f2e93e2ade0c4ac647ad1eb7/Theory/GroupTheory/PGroup/FrattiniAutomorphismKernel.lean
claim: The kernel of the automorphism action on the Frattini quotient of any finite p-group is a p-group.
strata_touched:
  - D5/S3/FiniteGroups/FrattiniAutomorphismKernel
license: Apache-2.0, full text in docs/reports/licenses/cfsg-frattini-kernel-LICENSE.txt
triage: anchor
---

# Frattini automorphism kernel

The immutable Lean source proves `Subgroup.isPGroup_quotientAut_frattini_kernel`
for every finite group G and every natural p satisfying `IsPGroup p G`.
Its `quotientAut` construction is in
`Theory/GroupTheory/CentralCharacteristicAutomorphisms.lean` at the same revision.
The upstream pins Lean 4.33.0 and Mathlib
db584cd6d46c92f209a44c0f1c829460d327499d.

The proof acts on functions from G to its Frattini subgroup, interpreting a
function f as the tuple of lifts g f(g). The nongenerating property of the
Frattini subgroup makes the action free. Orbit decomposition then shows that
the kernel order divides the number of tuples, a power of the Frattini
subgroup order. This establishes the ordinary kernel theorem without needing
the commutator-and-powers characterization of the Frattini subgroup.

The repository port retains that proof and its characteristic quotient action,
with namespace, import, visibility and module syntax adaptations. The full
upstream Apache license is retained. The upstream root tree has no NOTICE file.
The port retires when this repository's pinned Mathlib supplies
`Subgroup.isPGroup_quotientAut_frattini_kernel` with the same statement.
This source is a formalization reference, not verification of any attribution
to an original printed group-theory text.
