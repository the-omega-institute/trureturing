/- GID: D5/S3/Combinatorics/Turnpike/SubsetCertificatePair02
   generality: G
   mirror-B: none(waiver:covered-by-pruned-subset-projection-obstruction-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Partial-flow coverage over every triangle -/

module
public import D5.S3.Combinatorics.Turnpike.SubsetPairs02.Check456
public import D5.S3.Combinatorics.Turnpike.SubsetCertificatePair01
/-! Omega original.
# Partial-flow coverage over every triangle
-/
@[expose] public section
namespace Omega.Turnpike.SubsetCertificate
open Omega.Turnpike
open scoped BigOperators
theorem checks_02 (τ : Triangle 7) :
    ∀ U ∈ (positiveSupport (edge τ 0)).powerset,
    ∃ L, PartialFlowCheck (numericAtoms τ) (fun z => numerator (edge τ z))
      0 2 1 U L := by
  have h := triangleCovered τ
  simp only [triangleCover,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst τ; exact Flow012_02.covered
  · subst τ; exact Flow013_02.covered
  · subst τ; exact Flow014_02.covered
  · subst τ; exact Flow015_02.covered
  · subst τ; exact Flow016_02.covered
  · subst τ; exact Flow023_02.covered
  · subst τ; exact Flow024_02.covered
  · subst τ; exact Flow025_02.covered
  · subst τ; exact Flow026_02.covered
  · subst τ; exact Flow034_02.covered
  · subst τ; exact Flow035_02.covered
  · subst τ; exact Flow036_02.covered
  · subst τ; exact Flow045_02.covered
  · subst τ; exact Flow046_02.covered
  · subst τ; exact Flow056_02.covered
  · subst τ; exact Flow123_02.covered
  · subst τ; exact Flow124_02.covered
  · subst τ; exact Flow125_02.covered
  · subst τ; exact Flow126_02.covered
  · subst τ; exact Flow134_02.covered
  · subst τ; exact Flow135_02.covered
  · subst τ; exact Flow136_02.covered
  · subst τ; exact Flow145_02.covered
  · subst τ; exact Flow146_02.covered
  · subst τ; exact Flow156_02.covered
  · subst τ; exact Flow234_02.covered
  · subst τ; exact Flow235_02.covered
  · subst τ; exact Flow236_02.covered
  · subst τ; exact Flow245_02.covered
  · subst τ; exact Flow246_02.covered
  · subst τ; exact Flow256_02.covered
  · subst τ; exact Flow345_02.covered
  · subst τ; exact Flow346_02.covered
  · subst τ; exact Flow356_02.covered
  · subst τ; exact Flow456_02.covered
end Omega.Turnpike.SubsetCertificate
