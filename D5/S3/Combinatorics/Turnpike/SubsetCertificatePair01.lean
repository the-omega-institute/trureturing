/- GID: D5/S3/Combinatorics/Turnpike/SubsetCertificatePair01
   generality: G
   mirror-B: none(waiver:covered-by-pruned-subset-projection-obstruction-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Partial-flow coverage over every triangle -/

module
public import D5.S3.Combinatorics.Turnpike.SubsetPairs01.Check456
/-! Omega original.
# Partial-flow coverage over every triangle
-/
@[expose] public section
namespace Omega.Turnpike.SubsetCertificate
open Omega.Turnpike
open scoped BigOperators
theorem checks_01 (τ : Triangle 7) :
    ∀ U ∈ (positiveSupport (edge τ 0)).powerset,
    ∃ L, PartialFlowCheck (numericAtoms τ) (fun z => numerator (edge τ z))
      0 1 2 U L := by
  have h := triangleCovered τ
  simp only [triangleCover,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst τ; exact Flow012_01.covered
  · subst τ; exact Flow013_01.covered
  · subst τ; exact Flow014_01.covered
  · subst τ; exact Flow015_01.covered
  · subst τ; exact Flow016_01.covered
  · subst τ; exact Flow023_01.covered
  · subst τ; exact Flow024_01.covered
  · subst τ; exact Flow025_01.covered
  · subst τ; exact Flow026_01.covered
  · subst τ; exact Flow034_01.covered
  · subst τ; exact Flow035_01.covered
  · subst τ; exact Flow036_01.covered
  · subst τ; exact Flow045_01.covered
  · subst τ; exact Flow046_01.covered
  · subst τ; exact Flow056_01.covered
  · subst τ; exact Flow123_01.covered
  · subst τ; exact Flow124_01.covered
  · subst τ; exact Flow125_01.covered
  · subst τ; exact Flow126_01.covered
  · subst τ; exact Flow134_01.covered
  · subst τ; exact Flow135_01.covered
  · subst τ; exact Flow136_01.covered
  · subst τ; exact Flow145_01.covered
  · subst τ; exact Flow146_01.covered
  · subst τ; exact Flow156_01.covered
  · subst τ; exact Flow234_01.covered
  · subst τ; exact Flow235_01.covered
  · subst τ; exact Flow236_01.covered
  · subst τ; exact Flow245_01.covered
  · subst τ; exact Flow246_01.covered
  · subst τ; exact Flow256_01.covered
  · subst τ; exact Flow345_01.covered
  · subst τ; exact Flow346_01.covered
  · subst τ; exact Flow356_01.covered
  · subst τ; exact Flow456_01.covered
theorem numericAtoms_complete (τ : Triangle 7) :
    ∀ r : Fin 12 × Fin 12 × Fin 12,
    r ∈ numericAtoms τ ↔
      values r.1 + values r.2.1 = values r.2.2 ∧
      (r.1 ≠ r.2.1 ∨ 2 ≤ μ r.1) ∧ ProductAllowed μ τ r := by
  have h := triangleCovered τ
  simp only [triangleCover,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst τ; exact Numeric012.complete
  · subst τ; exact Numeric013.complete
  · subst τ; exact Numeric014.complete
  · subst τ; exact Numeric015.complete
  · subst τ; exact Numeric016.complete
  · subst τ; exact Numeric023.complete
  · subst τ; exact Numeric024.complete
  · subst τ; exact Numeric025.complete
  · subst τ; exact Numeric026.complete
  · subst τ; exact Numeric034.complete
  · subst τ; exact Numeric035.complete
  · subst τ; exact Numeric036.complete
  · subst τ; exact Numeric045.complete
  · subst τ; exact Numeric046.complete
  · subst τ; exact Numeric056.complete
  · subst τ; exact Numeric123.complete
  · subst τ; exact Numeric124.complete
  · subst τ; exact Numeric125.complete
  · subst τ; exact Numeric126.complete
  · subst τ; exact Numeric134.complete
  · subst τ; exact Numeric135.complete
  · subst τ; exact Numeric136.complete
  · subst τ; exact Numeric145.complete
  · subst τ; exact Numeric146.complete
  · subst τ; exact Numeric156.complete
  · subst τ; exact Numeric234.complete
  · subst τ; exact Numeric235.complete
  · subst τ; exact Numeric236.complete
  · subst τ; exact Numeric245.complete
  · subst τ; exact Numeric246.complete
  · subst τ; exact Numeric256.complete
  · subst τ; exact Numeric345.complete
  · subst τ; exact Numeric346.complete
  · subst τ; exact Numeric356.complete
  · subst τ; exact Numeric456.complete
end Omega.Turnpike.SubsetCertificate
