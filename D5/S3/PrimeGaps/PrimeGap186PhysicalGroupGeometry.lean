/- GID: D5/S3/PrimeGaps/PrimeGap186PhysicalGroupGeometry
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact six physical covering groups, source-row assignment, and 97-component schedule. -/

import D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGeometry

/-!
Exact covering-group definitions and schedule from `openai/PrimeGaps186`, commit
`61340d0b74163003b32756bb16e91d9209a5e330`. The finite schedule has 52 outer and
45 inner components, hence 97 components and 152 analytic inequalities after
counting both outer terms and the three scalar bounds. No integral is assumed.
-/

namespace D5.S3.PrimeGaps.PrimeGap186PhysicalGroupGeometry

open D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGeometry
open scoped BigOperators

structure PhysicalSourceGroupData where
  dimension : ℕ
  order : ℚ
  activation : ℚ
  threshold : ℚ
  lowerRadius : ℚ
  upperRadius : ℚ
  cap : ℚ
  split : ℚ

/-- Exact upstream ordering: two outer, two base-inner, two enlarged-inner groups. -/
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

/-- Rational endpoints of the low-fragment partition. -/
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

/-- Exact subdivision fractions for the rank-two partition. -/
def physicalSourceRankFractions (g : Fin 6) : List ℚ :=
  ![[0, 1 / 6, 1 / 3, 1 / 2, 2 / 3, 5 / 6, 1],
    [0, 1 / 16, 1 / 8, 3 / 16, 1 / 4, 5 / 16, 3 / 8,
      7 / 16, 1 / 2, 5 / 8, 3 / 4, 7 / 8, 1],
    [0, 1], [0, 1 / 2, 1], [0, 1 / 6, 1 / 2, 2 / 3, 1],
    [0, 1 / 8, 3 / 8, 1 / 2, 3 / 4, 1]] g

def physicalSourceLowCount (g : Fin 6) : ℕ :=
  (physicalSourceLowBoundaries g).length - 1

def physicalSourceRankCount (g : Fin 6) : ℕ :=
  (physicalSourceRankFractions g).length - 1

/-- The final summand is the high/triple-count component. -/
def physicalSourceRowCount (g : Fin 6) : ℕ :=
  physicalSourceLowCount g + physicalSourceRankCount g + 1

def physicalSourceComponentKind (g : Fin 6) (j : ℕ) : ℕ :=
  if j < physicalSourceLowCount g then 0
  else if j < physicalSourceLowCount g + physicalSourceRankCount g then 1 else 2

theorem physicalSourceGroup_dimensions :
    List.ofFn (fun g : Fin 6 => (physicalSourceGroup g).dimension) =
      [40, 40, 39, 39, 39, 39] := by decide

theorem physicalSourceGroup_orders :
    List.ofFn (fun g : Fin 6 => (physicalSourceGroup g).order) =
      [2, 5 / 2, 2, 5 / 2, 2, 5 / 2] := by rfl

theorem physicalSourceLowCounts :
    List.ofFn physicalSourceLowCount = [10, 22, 5, 7, 6, 11] := by decide

theorem physicalSourceRankCounts :
    List.ofFn physicalSourceRankCount = [6, 12, 1, 2, 4, 5] := by decide

theorem physicalSourceRowCounts :
    List.ofFn physicalSourceRowCount = [17, 35, 7, 10, 11, 17] := by decide

/-- Corrected component total. The earlier draft's 96 is false. -/
theorem total_physical_source_rows :
    ∑ g : Fin 6, physicalSourceRowCount g = 97 := by decide

theorem total_outer_source_rows :
    physicalSourceRowCount 0 + physicalSourceRowCount 1 = 52 := by decide

theorem total_inner_source_rows :
    physicalSourceRowCount 2 + physicalSourceRowCount 3 +
      physicalSourceRowCount 4 + physicalSourceRowCount 5 = 45 := by decide

theorem outer_bound_count_from_source_rows :
    2 * (physicalSourceRowCount 0 + physicalSourceRowCount 1) = 104 := by decide

#print axioms physicalSourceGroup_dimensions
#print axioms physicalSourceGroup_orders
#print axioms physicalSourceLowCounts
#print axioms physicalSourceRankCounts
#print axioms physicalSourceRowCounts
#print axioms total_physical_source_rows
#print axioms total_outer_source_rows
#print axioms total_inner_source_rows
#print axioms outer_bound_count_from_source_rows

end D5.S3.PrimeGaps.PrimeGap186PhysicalGroupGeometry
