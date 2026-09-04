/- GID: D5/S3/PrimeGaps/PrimeGap186PhysicalSourceGroups
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact finite source-group ownership and schedule partition for the PrimeGaps186 physical certificate. -/

import D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGeometry

/-!
This module isolates the discrete combinatorial layer between the exact rational source ladders and
the later interval/integral certificate. The goal is to make every source component addressable by
a finite owner and schedule tag before any numerical analytic inequality is introduced.
-/

namespace D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups

open D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGeometry

/-- The six source groups used by the physical certificate. -/
inductive PhysicalSourceGroup
  | outerH2
  | outerH25
  | outerH3
  | innerH2
  | innerH25
  | innerH3
  deriving DecidableEq, Repr

instance : Fintype PhysicalSourceGroup where
  elems := { .outerH2, .outerH25, .outerH3, .innerH2, .innerH25, .innerH3 }
  complete := by intro g; cases g <;> simp

/-- Outer/inner orientation of a source group. -/
def PhysicalSourceGroup.isOuter : PhysicalSourceGroup → Bool
  | .outerH2 | .outerH25 | .outerH3 => true
  | .innerH2 | .innerH25 | .innerH3 => false

/-- Effective dense-divisibility order attached to each group. The `h25` families are encoded
exactly as rational order `5/2`; the remaining groups use integral orders two and three. -/
def PhysicalSourceGroup.effectiveOrder : PhysicalSourceGroup → ℚ
  | .outerH2 | .innerH2 => 2
  | .outerH25 | .innerH25 => 5 / 2
  | .outerH3 | .innerH3 => 3

/-- The two source ladders. `base` corresponds to `ν = 0`; `enlarged` corresponds to `ν = 1`. -/
inductive PhysicalSourceFamily
  | base
  | enlarged
  deriving DecidableEq, Repr

/-- Groups below the enlarged boundary use the base source family, while the final two groups use
the enlarged family. This is the finite family-selection rule used downstream by the certificate. -/
def PhysicalSourceGroup.family : PhysicalSourceGroup → PhysicalSourceFamily
  | .outerH2 | .outerH25 | .outerH3 | .innerH2 => .base
  | .innerH25 | .innerH3 => .enlarged

/-- Every physical source group belongs to exactly one of the outer and inner orientations. -/
theorem sourceGroup_outer_xor_inner (g : PhysicalSourceGroup) :
    g.isOuter = true ∨ g.isOuter = false := by
  cases g <;> simp [PhysicalSourceGroup.isOuter]

/-- Effective order is always strictly positive. -/
theorem sourceGroup_effectiveOrder_pos (g : PhysicalSourceGroup) :
    0 < g.effectiveOrder := by
  cases g <;> norm_num [PhysicalSourceGroup.effectiveOrder]

/-- Every effective order is one of the three values used by the upstream construction. -/
theorem sourceGroup_effectiveOrder_cases (g : PhysicalSourceGroup) :
    g.effectiveOrder = 2 ∨ g.effectiveOrder = 5 / 2 ∨ g.effectiveOrder = 3 := by
  cases g <;> simp [PhysicalSourceGroup.effectiveOrder]

/-- The finite schedule phase inside one source group. -/
inductive PhysicalSchedulePhase
  | low
  | rankTwo
  | high
  deriving DecidableEq, Repr

instance : Fintype PhysicalSchedulePhase where
  elems := { .low, .rankTwo, .high }
  complete := by intro p; cases p <;> simp

/-- A fully discrete address for one family of physical certificate components. The analytic
certificate will later refine each address by a finite local bin index. -/
structure PhysicalComponentAddress where
  group : PhysicalSourceGroup
  phase : PhysicalSchedulePhase
  deriving DecidableEq, Repr

instance : Fintype PhysicalComponentAddress := Fintype.ofFinite _

/-- There are exactly six groups times three schedule phases. -/
theorem card_physicalComponentAddress :
    Fintype.card PhysicalComponentAddress = 18 := by
  native_decide

/-- Outer groups occupy exactly nine of the eighteen coarse component addresses. -/
def outerComponentAddresses : Finset PhysicalComponentAddress :=
  Finset.univ.filter (fun a => a.group.isOuter)

/-- Inner groups occupy the complementary nine coarse addresses. -/
def innerComponentAddresses : Finset PhysicalComponentAddress :=
  Finset.univ.filter (fun a => !a.group.isOuter)

/-- The outer and inner coarse schedules are disjoint. -/
theorem outer_inner_addresses_disjoint :
    Disjoint outerComponentAddresses innerComponentAddresses := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro a haOuter haInner
  simp [outerComponentAddresses, innerComponentAddresses] at haOuter haInner

/-- Every coarse component address is classified as outer or inner. -/
theorem outer_union_inner_addresses :
    outerComponentAddresses ∪ innerComponentAddresses = Finset.univ := by
  classical
  ext a
  by_cases h : a.group.isOuter
  · simp [outerComponentAddresses, innerComponentAddresses, h]
  · have hf : a.group.isOuter = false := Bool.eq_false_iff.mpr h
    simp [outerComponentAddresses, innerComponentAddresses, hf]

/-- The six-group ownership layer is finite and contains no analytic assumptions. -/
theorem card_source_groups : Fintype.card PhysicalSourceGroup = 6 := by
  native_decide

#print axioms PhysicalSourceGroup
#print axioms PhysicalSourceGroup.effectiveOrder
#print axioms sourceGroup_effectiveOrder_pos
#print axioms PhysicalSchedulePhase
#print axioms PhysicalComponentAddress
#print axioms card_physicalComponentAddress
#print axioms outer_inner_addresses_disjoint
#print axioms outer_union_inner_addresses
#print axioms card_source_groups

end D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups
