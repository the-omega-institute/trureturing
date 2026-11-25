/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/AffineAxisMiddleIdentity
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bind the middle-axis coefficient table to its exact sign polynomial. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineAxisMiddleData
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineCheckedIdentity

/-! A single exact integer identity certifies this polynomial factorization. -/

open RefinedBMV.ThreeBlockGram.PositiveSpectrum
open RefinedBMV.ThreeBlockGram.PositiveSpectrum.AffineRadixIdentity
open RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks.AxisMiddle

open RefinedBMV.DividedDifference.SparseExpansion
open private boundedTable identitySizes identityWidth tableMass from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineCheckedIdentity

private def tableDegree : Exponents := ⟨12, 10, 10, 12, 12⟩

private theorem checkedSizes :
    identitySizes .axisMiddle tableDegree = ⟨13, 25, 37, 17, 17⟩ := by rfl

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checkedWidth : identityWidth .axisMiddle (tableMass certificate) = 90 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checkedBounds : boundedTable certificate 11 tableDegree = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checkedIdentity : checkIdentity .axisMiddle certificate 11 tableDegree = true := by
  simp only [checkIdentity, checkedSizes, checkedWidth, checkedBounds, Bool.true_and]
  decide +kernel

#print axioms checkedIdentity
