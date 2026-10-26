/- GID: D5/S3/Combinatorics/SubsetSpectrum/TengokuSubsetSums
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SubsetSpectrum/TengokuSubsetSums
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Multiset.Powerset]
   utility: none
   digest: Attributed multiset subset-sum and powerset-map leaves. -/

import Mathlib.Data.Multiset.Powerset
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs

/-
Copyright (c) 2026 James Huang, Samuël Borza. All rights reserved.
Released under Apache 2.0 license; the complete LICENSE and NOTICE chain is in
 docs/reports/licenses/tengoku-subset-sums/.
Authors: James Huang, Samuël Borza

Adapted from competemath/tengoku at
 e784113248524aeef7681b0687c722b426c1b115:
 ComplexExponential.lean, subsetSums; SubsetSumPolynomial.lean, powerset_map_eq.
Adaptations: imports use pinned Mathlib; declarations have the enclosing namespace.
Retire each port when this repository's own pinned Mathlib has an equivalent
 declaration and replace its consumers by direct imports and applications.
-/

namespace D5.S3.Combinatorics.SubsetSpectrum

/-- The multiset of all subset sums, preserving subset occurrences. -/
def subsetSums {α : Type*} [AddCommMonoid α] (s : Multiset α) : Multiset α :=
  s.powerset.map Multiset.sum

/-- Taking powersets commutes with mapping a function over a multiset. -/
lemma powerset_map_eq {α β : Type*} (f : α → β) (s : Multiset α) :
    Multiset.map (Multiset.map f) s.powerset = (Multiset.map f s).powerset := by
  rw [← Multiset.bind_powerset_len s, Multiset.map_bind]
  simp_rw [← Multiset.powersetCard_map]
  rw [← Multiset.bind_powerset_len (Multiset.map f s), Multiset.card_map]

end D5.S3.Combinatorics.SubsetSpectrum
