/- GID: D5/S3/Quantum/PureState/UnitGramIndistinguishability
   generality: G
   mirror-B: D5/B/S3/Quantum/PureState/UnitGramIndistinguishability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Unit Gram overlap detects equality and defines an equivalence relation. -/

import Mathlib.Analysis.InnerProductSpace.Basic

/- Library-search audit trail (2026-08-17):
   * Repository search found Gram-overlap channel laws and normalized-record complementarity,
     but no theorem characterizing unit overlap as equality or packaging its equivalence relation.
   * Pinned Mathlib and Loogle exactly found `inner_eq_one_iff_of_norm_eq_one`; the proof below
     imports and applies it rather than reproving the equality case of Cauchy-Schwarz.
   * LeanSearch's `/api/search` endpoint returned HTTP 404. GitHub code search returned HTTP 401
     without authentication. Reservoir was reachable but supplied no declaration-level result. -/

open scoped InnerProductSpace

namespace D5.S3.Quantum.PureState.UnitGramIndistinguishability

/-- Unit Gram overlap is exactly equality, so record indistinguishability by unit overlap is an
equivalence relation. -/
theorem unit_gram_overlap_characterization
    {𝕜 Index E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (record : Index → E) (normalized : ∀ i, ‖record i‖ = 1) :
    (∀ i j, ⟪record i, record j⟫_𝕜 = 1 ↔ record i = record j) ∧
      Equivalence (fun i j => ⟪record i, record j⟫_𝕜 = 1) := by
  have overlap_eq_iff (i j : Index) :
      ⟪record i, record j⟫_𝕜 = 1 ↔ record i = record j :=
    inner_eq_one_iff_of_norm_eq_one (normalized i) (normalized j)
  refine ⟨overlap_eq_iff, ?_⟩
  constructor
  · intro i
    exact (overlap_eq_iff i i).2 rfl
  · intro i j hij
    exact (overlap_eq_iff j i).2 ((overlap_eq_iff i j).1 hij).symm
  · intro i j k hij hjk
    exact (overlap_eq_iff i k).2
      (((overlap_eq_iff i j).1 hij).trans ((overlap_eq_iff j k).1 hjk))

#print axioms unit_gram_overlap_characterization

end D5.S3.Quantum.PureState.UnitGramIndistinguishability
