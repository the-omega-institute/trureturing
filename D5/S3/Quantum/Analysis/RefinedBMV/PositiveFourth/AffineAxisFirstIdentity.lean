/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/AffineAxisFirstIdentity
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bind the affine coefficient table to its exact sign polynomial. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineAxisFirstData
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineCheckedIdentity

/-! A single exact integer identity certifies this polynomial factorization. -/

open RefinedBMV.ThreeBlockGram.PositiveSpectrum
open RefinedBMV.ThreeBlockGram.PositiveSpectrum.AffineRadixIdentity
open RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks.AxisFirst

open RefinedBMV.DividedDifference.SparseExpansion
open private boundedTable identitySizes identityWidth tableMass from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineCheckedIdentity

private def tableDegree : Exponents := ⟨12, 12, 10, 16, 12⟩

private theorem checkedSizes :
    identitySizes .axisFirst tableDegree = ⟨13, 25, 37, 17, 17⟩ := by rfl

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- The kernel sums the grouped coefficient mass.
private theorem checkedWidth : identityWidth .axisFirst (tableMass certificate) = 90 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- The kernel checks the length and rate bounds of each group.
private theorem checkedBounds : boundedTable certificate 11 tableDegree = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The kernel compares the two packed integer evaluations.
private theorem checkedIdentity : checkIdentity .axisFirst certificate 11 tableDegree = true := by
  simp only [checkIdentity, checkedSizes, checkedWidth, checkedBounds, Bool.true_and]
  decide +kernel

#print axioms checkedIdentity
