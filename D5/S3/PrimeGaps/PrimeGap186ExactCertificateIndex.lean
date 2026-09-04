/- GID: D5/S3/PrimeGaps/PrimeGap186ExactCertificateIndex
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Replace the opaque 152-cell numerical input by exact typed row and component addresses. -/

import D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups

/-!
The upstream physical axiom consists of:

* 17 order-two outer rows;
* 35 order-5/2 outer rows;
* two component bounds (`root`, `face`) for each outer row, giving 104 inequalities;
* 7 old-inner order-two rows;
* 10 old-inner order-5/2 rows;
* 11 new-inner order-two rows;
* 17 new-inner order-5/2 rows, giving 45 inequalities;
* three scalar cap/trial inequalities.

This file records that exact combinatorial shape as types. No numerical inequality is assumed.
-/

namespace D5.S3.PrimeGaps.PrimeGap186ExactCertificateIndex

open D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups

/-- Which component of one outer table row is being bounded. -/
inductive OuterComponentKind
  | root
  | face
  deriving DecidableEq, Repr

instance : Fintype OuterComponentKind where
  elems := { .root, .face }
  complete := by intro k; cases k <;> simp

/-- Exact row addresses for the 52 outer rows. -/
inductive OuterRowAddress
  | orderTwo (index : Fin 17)
  | orderFiveHalves (index : Fin 35)
  deriving DecidableEq, Repr

instance : Fintype OuterRowAddress := Fintype.ofFinite _

/-- Exact row addresses for the 45 inner rows. -/
inductive InnerRowAddress
  | oldOrderTwo (index : Fin 7)
  | oldOrderFiveHalves (index : Fin 10)
  | newOrderTwo (index : Fin 11)
  | newOrderFiveHalves (index : Fin 17)
  deriving DecidableEq, Repr

instance : Fintype InnerRowAddress := Fintype.ofFinite _

/-- Every outer numerical inequality is a row plus one of its two components. -/
structure OuterBoundAddress where
  row : OuterRowAddress
  component : OuterComponentKind
  deriving DecidableEq, Repr

instance : Fintype OuterBoundAddress := Fintype.ofFinite _

/-- Three global scalar cap/trial obligations. -/
abbrev ScalarBoundAddress := Fin 3

/-- The complete exact finite address space for the upstream physical numerical input. -/
inductive PhysicalBoundAddress
  | outer (address : OuterBoundAddress)
  | inner (address : InnerRowAddress)
  | scalar (address : ScalarBoundAddress)
  deriving DecidableEq, Repr

instance : Fintype PhysicalBoundAddress := Fintype.ofFinite _

/-- The 52 outer rows split exactly as 17 + 35. -/
theorem card_outer_rows : Fintype.card OuterRowAddress = 52 := by
  native_decide

/-- Every outer row carries exactly two component inequalities, hence 104 outer bounds. -/
theorem card_outer_bounds : Fintype.card OuterBoundAddress = 104 := by
  native_decide

/-- The four inner tables contain exactly 45 rows. -/
theorem card_inner_rows : Fintype.card InnerRowAddress = 45 := by
  native_decide

/-- The complete physical numerical package contains exactly 152 obligations. -/
theorem card_all_physical_bounds : Fintype.card PhysicalBoundAddress = 152 := by
  native_decide

/-- Exact coarse source owner of an outer row. -/
def OuterRowAddress.sourceGroup : OuterRowAddress → PhysicalSourceGroup
  | .orderTwo _ => .outerH2
  | .orderFiveHalves _ => .outerH25

/-- Exact coarse source owner of an inner row. -/
def InnerRowAddress.sourceGroup : InnerRowAddress → PhysicalSourceGroup
  | .oldOrderTwo _ => .oldInnerH2
  | .oldOrderFiveHalves _ => .oldInnerH25
  | .newOrderTwo _ => .newInnerH2
  | .newOrderFiveHalves _ => .newInnerH25

/-- Outer table ownership always points to an outer source group. -/
theorem outerRow_sourceGroup_isOuter (r : OuterRowAddress) :
    r.sourceGroup.isOuter = true := by
  cases r <;> simp [OuterRowAddress.sourceGroup, PhysicalSourceGroup.isOuter]

/-- Inner table ownership always points to an inner source group. -/
theorem innerRow_sourceGroup_isInner (r : InnerRowAddress) :
    r.sourceGroup.isOuter = false := by
  cases r <;> simp [InnerRowAddress.sourceGroup, PhysicalSourceGroup.isOuter]

/-- The table row type records the same effective order as its source owner. -/
def OuterRowAddress.effectiveOrder : OuterRowAddress → ℚ
  | .orderTwo _ => 2
  | .orderFiveHalves _ => 5 / 2

/-- The inner row type records its exact effective order. -/
def InnerRowAddress.effectiveOrder : InnerRowAddress → ℚ
  | .oldOrderTwo _ | .newOrderTwo _ => 2
  | .oldOrderFiveHalves _ | .newOrderFiveHalves _ => 5 / 2

/-- Outer row order agrees definitionally with the owning source group. -/
theorem outerRow_order_agrees_with_owner (r : OuterRowAddress) :
    r.effectiveOrder = r.sourceGroup.effectiveOrder := by
  cases r <;> norm_num [OuterRowAddress.effectiveOrder, OuterRowAddress.sourceGroup,
    PhysicalSourceGroup.effectiveOrder]

/-- Inner row order agrees definitionally with the owning source group. -/
theorem innerRow_order_agrees_with_owner (r : InnerRowAddress) :
    r.effectiveOrder = r.sourceGroup.effectiveOrder := by
  cases r <;> norm_num [InnerRowAddress.effectiveOrder, InnerRowAddress.sourceGroup,
    PhysicalSourceGroup.effectiveOrder]

/-- Forgetting the component kind maps the 104 outer inequalities onto the 52 source rows. -/
def OuterBoundAddress.rowOwner (a : OuterBoundAddress) : PhysicalSourceGroup :=
  a.row.sourceGroup

/-- There are exactly twice as many outer inequalities as outer rows. -/
theorem outer_bounds_double_rows :
    Fintype.card OuterBoundAddress = 2 * Fintype.card OuterRowAddress := by
  native_decide

/-- The exact cardinality decomposition of the full numerical input. -/
theorem physical_bound_cardinality_decomposition :
    152 = 2 * (17 + 35) + (7 + 10 + 11 + 17) + 3 := by
  norm_num

#print axioms OuterComponentKind
#print axioms OuterRowAddress
#print axioms InnerRowAddress
#print axioms OuterBoundAddress
#print axioms PhysicalBoundAddress
#print axioms card_outer_rows
#print axioms card_outer_bounds
#print axioms card_inner_rows
#print axioms card_all_physical_bounds
#print axioms outerRow_sourceGroup_isOuter
#print axioms innerRow_sourceGroup_isInner
#print axioms outerRow_order_agrees_with_owner
#print axioms innerRow_order_agrees_with_owner
#print axioms physical_bound_cardinality_decomposition

end D5.S3.PrimeGaps.PrimeGap186ExactCertificateIndex
