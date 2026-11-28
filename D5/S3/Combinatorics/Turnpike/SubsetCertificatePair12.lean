/- GID: D5/S3/Combinatorics/Turnpike/SubsetCertificatePair12
   generality: G
   mirror-B: none(waiver:covered-by-pruned-subset-projection-obstruction-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Partial-flow coverage over every triangle -/

module
public import D5.S3.Combinatorics.Turnpike.SubsetPairs12.Check456
public import D5.S3.Combinatorics.Turnpike.SubsetCertificatePair02
/-! Omega original.
# Partial-flow coverage over every triangle
-/
@[expose] public section
namespace Omega.Turnpike.SubsetCertificate
open Omega.Turnpike
open scoped BigOperators
theorem checks_12 (τ : Triangle 7) :
    ∀ U ∈ (positiveSupport (edge τ 1)).powerset,
    ∃ L, PartialFlowCheck (numericAtoms τ) (fun z => numerator (edge τ z))
      1 2 0 U L := by
  have h := triangleCovered τ
  simp only [triangleCover,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst τ; exact Flow012_12.covered
  · subst τ; exact Flow013_12.covered
  · subst τ; exact Flow014_12.covered
  · subst τ; exact Flow015_12.covered
  · subst τ; exact Flow016_12.covered
  · subst τ; exact Flow023_12.covered
  · subst τ; exact Flow024_12.covered
  · subst τ; exact Flow025_12.covered
  · subst τ; exact Flow026_12.covered
  · subst τ; exact Flow034_12.covered
  · subst τ; exact Flow035_12.covered
  · subst τ; exact Flow036_12.covered
  · subst τ; exact Flow045_12.covered
  · subst τ; exact Flow046_12.covered
  · subst τ; exact Flow056_12.covered
  · subst τ; exact Flow123_12.covered
  · subst τ; exact Flow124_12.covered
  · subst τ; exact Flow125_12.covered
  · subst τ; exact Flow126_12.covered
  · subst τ; exact Flow134_12.covered
  · subst τ; exact Flow135_12.covered
  · subst τ; exact Flow136_12.covered
  · subst τ; exact Flow145_12.covered
  · subst τ; exact Flow146_12.covered
  · subst τ; exact Flow156_12.covered
  · subst τ; exact Flow234_12.covered
  · subst τ; exact Flow235_12.covered
  · subst τ; exact Flow236_12.covered
  · subst τ; exact Flow245_12.covered
  · subst τ; exact Flow246_12.covered
  · subst τ; exact Flow256_12.covered
  · subst τ; exact Flow345_12.covered
  · subst τ; exact Flow346_12.covered
  · subst τ; exact Flow356_12.covered
  · subst τ; exact Flow456_12.covered
end Omega.Turnpike.SubsetCertificate
