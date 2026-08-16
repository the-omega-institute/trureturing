/- GID: D5/S1/FixedPoints/KleeneStageLimit
   generality: G
   mirror-B: D5/B/S1/FixedPoints/KleeneStageLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An omega-continuous operator's least fixed point is the supremum of its stages. -/

import Mathlib.Order.FixedPoints

/- Library-search audit trail (2026-08-16):
   * Local D5 searches for Scott continuity, iterates from bottom, and Kleene
     fixed points found no equivalent repository declaration.
   * The pinned-Mathlib search and `smart_search.sh` both found the exact
     theorem `fixedPoints.lfp_eq_sSup_iterate`, imported and applied below.
   * LeanSearch's `/api/search` endpoint returned HTTP 404. -/

namespace D5.S1.FixedPoints.KleeneStageLimit

open OmegaCompletePartialOrder

/-- The least fixed point of an omega-Scott-continuous order endomorphism is
the supremum of its finite stages starting from bottom. -/
theorem inductive_definition_is_supremum_of_stages
    {α : Type*} [CompleteLattice α] (f : α →o α)
    (hf : ωScottContinuous f) :
    f.lfp = ⨆ n, f^[n] ⊥ :=
  fixedPoints.lfp_eq_sSup_iterate f hf

#print axioms inductive_definition_is_supremum_of_stages

end D5.S1.FixedPoints.KleeneStageLimit
