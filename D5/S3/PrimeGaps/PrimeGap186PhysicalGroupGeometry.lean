/- GID: D5/S3/PrimeGaps/PrimeGap186PhysicalGroupGeometry
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Port the exact six physical covering groups, assigned source rows, and component schedule from PrimeGaps186. -/

import D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGeometry

/-!
Exact port of the six covering-group definitions and finite schedule skeleton from
`openai/PrimeGaps186` commit `61340d0b74163003b32756bb16e91d9209a5e330`.
No physical integral inequality is assumed here.
-/

namespace D5.S3.PrimeGaps.PrimeGap186PhysicalGroupGeometry

open D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGeometry

/-- Exact rational geometry for one covering group. -/
structure PhysicalSourceGroupData where
  dimension : ℕ
  order : ℚ
  activation : ℚ
  threshold : ℚ
  lowerRadius : ℚ
  upperRadius : ℚ
  cap : ℚ
  split : ℚ

/-- The six covering groups in upstream order:
`outer_h2`, `outer_h25`, `old_inner_h2`, `old_inner_h25`, `new_inner_h2`, `new_inner_h25`. -/
def physicalSourceGroup (g : Fin 6) : PhysicalSourceGroupData :=
  let S := physicalSourceOuterRadius
  let T0 := physicalSourceInnerRadius 0
  let T1 := physicalSourceInnerRadius 1
  let e := physicalSourceAdvance
  ![{ dimension := 40, order := 2,
      activation := (physicalSourceRow 0 23).activation, threshold := S + e,
      lowerRadius := (physicalSourceRow 1 0).outerCore,
      upperRadius := (physicalSourceRow 1 24).outerCore,
      cap := 49152 * trialMesh, split := 24576 * trialMesh },
    { dimension := 40, order := 5 / 2,
      activation := (physicalSourceRow 1 38).activation, threshold := S + e / 2,
      lowerRadius := (physicalSourceRow 1 24).outerCore,
      upperRadius := 98303 * trialMesh,
      cap := 46580 * trialMesh, split := 19660 * trialMesh },
    { dimension := 39, order := 2,
      activation := (physicalSourceRow 0 23).activation, threshold := T0 + e,
      lowerRadius := (physicalSourceRow 0 12).innerCore,
      upperRadius := (physicalSourceRow 0 24).innerCore,
      cap := 44781 * trialMesh, split := 22390 * trialMesh },
    { dimension := 39, order := 5 / 2,
      activation := (physicalSourceRow 0 27).activation, threshold := T0 + e / 2,
      lowerRadius := (physicalSourceRow 0 24).innerCore,
      upperRadius := 89563 * trialMesh,
      cap := 35265 * trialMesh, split := 17912 * trialMesh },
    { dimension := 39, order := 2,
      activation := (physicalSourceRow 1 23).activation, threshold := T1 + e,
      lowerRadius := (physicalSourceRow 1 12).innerCore,
      upperRadius := (physicalSourceRow 1 24).innerCore,
      cap := 44976 * trialMesh, split := 22488 * trialMesh },
    { dimension := 39, order := 5 / 2,
      activation := (physicalSourceRow 1 38).activation, threshold := T1 + e / 2,
      lowerRadius := (physicalSourceRow 1 24).innerCore,
      upperRadius := 89953 * trialMesh,
      cap := 35419 * trialMesh, split := 17990 * trialMesh }] g

/-- Exact source-family/index pairs assigned to each covering group. -/
def physicalSourceRows (g : Fin 6) : Finset (Fin 2 × ℕ) :=
  ![(Finset.range 24).biUnion (fun t => {(0, t), (1, t)}),
    (Finset.Icc 24 27).image (fun t => (0, t)) ∪
      (Finset.Icc 24 38).image (fun t => (1, t)),
    (Finset.Icc 12 23).image (fun t => (0, t)),
    (Finset.Icc 24 27).image (fun t => (0, t)),
    (Finset.Icc 12 23).image (fun t => (1, t)),
    (Finset.Icc 24 38).image (fun t => (1, t))] g

/-- Exact rational boundaries of the low-fragment partition. -/
def physicalSourceLowBoundaries (g : Fin 6) : List ℚ :=
  let ξ := (physicalSourceGroup g).activation
  let p := (physicalSourceGroup g).split
  let a : ℕ → ℚ := fun j => (1 / 20) * (6 / 5) ^ j
  ![[ξ, (3 / 2) * ξ, a 0, a 4, a 5, a 6, a 7, a 8, (a 8 + a 9) / 2, a 9, p],
    [ξ, 2 * ξ, 4 * ξ, 8 * ξ, 16 * ξ, 32 * ξ, 64 * ξ, 128 * ξ,
      256 * ξ, 1 / 100, 3 / 200, 9 / 400, 27 / 800, a 0, a 1, a 2,
      a 3, a 4, a 5, a 6, a 7, (a 7 + p) / 2, p],
    [ξ, a 0, a 4, a 6, a 8, p],
    [ξ, 2 * ξ, 1 / 100, 27 / 800, a 3, a 5, a 6, p],
    [ξ, a 1, a 4, a 5, a 7, a 8, p],
    [ξ, 2 * ξ, 16 * ξ, 64 * ξ, 256 * ξ, 9 / 400,
      a 1, a 3, a 5, a 6, a 7, p]] g

/-- Exact rational subdivision fractions for the rank-two partition. -/
def physicalSourceRankFractions (g : Fin 6) : List ℚ :=
  ![[0, 1 / 6, 1 / 3, 1 / 2, 2 / 3, 5 / 6, 1],
    [0, 1 / 16, 1 / 8, 3 / 16, 1 / 4, 5 / 16, 3 / 8,
      7 / 16, 1 / 2, 5 / 8, 3 / 4, 7 / 8, 1],
    [0, 1],
    [0, 1 / 2, 1],
    [0, 1 / 6, 1 / 2, 2 / 3, 1],
    [0, 1 / 8, 3 / 8, 1 / 2, 3 / 4, 1]] g

/-- Number of low-fragment schedule components. -/
def physicalSourceLowCount (g : Fin 6) : ℕ :=
  (physicalSourceLowBoundaries g).length - 1

/-- Number of rank-two schedule components. -/
def physicalSourceRankCount (g : Fin 6) : ℕ :=
  (physicalSourceRankFractions g).length - 1

/-- Total schedule components: low + rank-two + one high/triple-count component. -/
def physicalSourceRowCount (g : Fin 6) : ℕ :=
  physicalSourceLowCount g + physicalSourceRankCount g + 1

/-- Exact component kind encoding used upstream: 0 = low, 1 = rank-two, 2 = high. -/
def physicalSourceComponentKind (g : Fin 6) (j : ℕ) : ℕ :=
  if j < physicalSourceLowCount g then 0
  else if j < physicalSourceLowCount g + physicalSourceRankCount g then 1 else 2

/-- Exact group dimensions are `[40,40,39,39,39,39]`. -/
theorem physicalSourceGroup_dimensions :
    (List.ofFn (fun g : Fin 6 => (physicalSourceGroup g).dimension)) = [40, 40, 39, 39, 39, 39] := by
  native_decide

/-- Exact effective group orders are `[2,5/2,2,5/2,2,5/2]`. -/
theorem physicalSourceGroup_orders :
    (List.ofFn (fun g : Fin 6 => (physicalSourceGroup g).order)) =
      [2, 5 / 2, 2, 5 / 2, 2, 5 / 2] := by
  native_decide

/-- The low-component counts generated by the exact boundary lists. -/
theorem physicalSourceLowCounts :
    List.ofFn physicalSourceLowCount = [10, 22, 5, 7, 6, 11] := by
  native_decide

/-- The rank-component counts generated by the exact fraction lists. -/
theorem physicalSourceRankCounts :
    List.ofFn physicalSourceRankCount = [6, 12, 1, 2, 4, 5] := by
  native_decide

/-- The six total row counts are exactly the six numerical table lengths. -/
theorem physicalSourceRowCounts :
    List.ofFn physicalSourceRowCount = [17, 35, 7, 10, 11, 17] := by
  native_decide

/-- There are 96 source components in total. -/
theorem total_physical_source_rows :
    ∑ g : Fin 6, physicalSourceRowCount g = 96 := by
  native_decide

/-- The two outer groups contribute 52 source components. -/
theorem total_outer_source_rows :
    physicalSourceRowCount 0 + physicalSourceRowCount 1 = 52 := by
  native_decide

/-- The four inner groups contribute 45 source components. -/
theorem total_inner_source_rows :
    physicalSourceRowCount 2 + physicalSourceRowCount 3 +
      physicalSourceRowCount 4 + physicalSourceRowCount 5 = 45 := by
  native_decide

/-- Therefore the 104 outer numerical inequalities are exactly two component bounds per one of
52 outer source components. -/
theorem outer_bound_count_from_source_rows :
    2 * (physicalSourceRowCount 0 + physicalSourceRowCount 1) = 104 := by
  native_decide

#print axioms PhysicalSourceGroupData
#print axioms physicalSourceGroup
#print axioms physicalSourceRows
#print axioms physicalSourceLowBoundaries
#print axioms physicalSourceRankFractions
#print axioms physicalSourceRowCount
#print axioms physicalSourceGroup_dimensions
#print axioms physicalSourceGroup_orders
#print axioms physicalSourceLowCounts
#print axioms physicalSourceRankCounts
#print axioms physicalSourceRowCounts
#print axioms total_physical_source_rows
#print axioms outer_bound_count_from_source_rows

end D5.S3.PrimeGaps.PrimeGap186PhysicalGroupGeometry
