/- GID: D5/S3/PrimeGaps/PrimeGap186ExactCertificateIndex
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact typed row, component, and scalar addresses with constructive finite enumeration. -/

import D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups

namespace D5.S3.PrimeGaps.PrimeGap186ExactCertificateIndex

open D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups

inductive OuterComponentKind
  | root
  | face
  deriving DecidableEq, Repr

instance : Fintype OuterComponentKind where
  elems := { .root, .face }
  complete := by intro k; cases k <;> simp

inductive OuterRowAddress
  | orderTwo (index : Fin 17)
  | orderFiveHalves (index : Fin 35)
  deriving DecidableEq, Repr

instance : Fintype OuterRowAddress where
  elems := (Finset.univ.image OuterRowAddress.orderTwo) ∪
    (Finset.univ.image OuterRowAddress.orderFiveHalves)
  complete := by intro r; cases r <;> simp

inductive InnerRowAddress
  | oldOrderTwo (index : Fin 7)
  | oldOrderFiveHalves (index : Fin 10)
  | newOrderTwo (index : Fin 11)
  | newOrderFiveHalves (index : Fin 17)
  deriving DecidableEq, Repr

instance : Fintype InnerRowAddress where
  elems := (Finset.univ.image InnerRowAddress.oldOrderTwo) ∪
    (Finset.univ.image InnerRowAddress.oldOrderFiveHalves) ∪
    (Finset.univ.image InnerRowAddress.newOrderTwo) ∪
    (Finset.univ.image InnerRowAddress.newOrderFiveHalves)
  complete := by intro r; cases r <;> simp

structure OuterBoundAddress where
  row : OuterRowAddress
  component : OuterComponentKind
  deriving DecidableEq, Repr

instance : Fintype OuterBoundAddress where
  elems := Finset.univ.biUnion (fun r : OuterRowAddress =>
    Finset.univ.image (fun c : OuterComponentKind => (⟨r, c⟩ : OuterBoundAddress)))
  complete := by
    rintro ⟨r, c⟩
    exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩⟩

/-- The three global cap/trial inequalities at the end of the upstream physical input. -/
inductive ScalarBoundAddress
  | trialIHLower
  | trialIHUpper
  | trialJLambdaHLower
  deriving DecidableEq, Repr

instance : Fintype ScalarBoundAddress where
  elems := { .trialIHLower, .trialIHUpper, .trialJLambdaHLower }
  complete := by intro s; cases s <;> simp

inductive PhysicalBoundAddress
  | outer (address : OuterBoundAddress)
  | inner (address : InnerRowAddress)
  | scalar (address : ScalarBoundAddress)
  deriving DecidableEq, Repr

instance : Fintype PhysicalBoundAddress where
  elems := (Finset.univ.image PhysicalBoundAddress.outer) ∪
    (Finset.univ.image PhysicalBoundAddress.inner) ∪
    (Finset.univ.image PhysicalBoundAddress.scalar)
  complete := by intro a; cases a <;> simp

-- These small exact enumerations are reduced by the kernel, without native_decide.
set_option maxRecDepth 4096 in
theorem card_outer_rows : Fintype.card OuterRowAddress = 52 := by decide
set_option maxRecDepth 4096 in
theorem card_outer_bounds : Fintype.card OuterBoundAddress = 104 := by decide
set_option maxRecDepth 4096 in
theorem card_inner_rows : Fintype.card InnerRowAddress = 45 := by decide
theorem card_scalar_bounds : Fintype.card ScalarBoundAddress = 3 := by decide
set_option maxRecDepth 4096 in
theorem card_all_physical_bounds : Fintype.card PhysicalBoundAddress = 152 := by decide

def OuterRowAddress.sourceGroup : OuterRowAddress → PhysicalSourceGroup
  | .orderTwo _ => .outerH2
  | .orderFiveHalves _ => .outerH25

def InnerRowAddress.sourceGroup : InnerRowAddress → PhysicalSourceGroup
  | .oldOrderTwo _ => .oldInnerH2
  | .oldOrderFiveHalves _ => .oldInnerH25
  | .newOrderTwo _ => .newInnerH2
  | .newOrderFiveHalves _ => .newInnerH25

theorem outerRow_sourceGroup_isOuter (r : OuterRowAddress) :
    r.sourceGroup.isOuter = true := by
  cases r <;> simp [OuterRowAddress.sourceGroup, PhysicalSourceGroup.isOuter]

theorem innerRow_sourceGroup_isInner (r : InnerRowAddress) :
    r.sourceGroup.isOuter = false := by
  cases r <;> simp [InnerRowAddress.sourceGroup, PhysicalSourceGroup.isOuter]

def OuterRowAddress.effectiveOrder : OuterRowAddress → ℚ
  | .orderTwo _ => 2
  | .orderFiveHalves _ => 5 / 2

def InnerRowAddress.effectiveOrder : InnerRowAddress → ℚ
  | .oldOrderTwo _ | .newOrderTwo _ => 2
  | .oldOrderFiveHalves _ | .newOrderFiveHalves _ => 5 / 2

theorem outerRow_order_agrees_with_owner (r : OuterRowAddress) :
    r.effectiveOrder = r.sourceGroup.effectiveOrder := by
  cases r <;> norm_num [OuterRowAddress.effectiveOrder, OuterRowAddress.sourceGroup,
    PhysicalSourceGroup.effectiveOrder]

theorem innerRow_order_agrees_with_owner (r : InnerRowAddress) :
    r.effectiveOrder = r.sourceGroup.effectiveOrder := by
  cases r <;> norm_num [InnerRowAddress.effectiveOrder, InnerRowAddress.sourceGroup,
    PhysicalSourceGroup.effectiveOrder]

def OuterBoundAddress.rowOwner (a : OuterBoundAddress) : PhysicalSourceGroup :=
  a.row.sourceGroup

theorem outer_bounds_double_rows :
    Fintype.card OuterBoundAddress = 2 * Fintype.card OuterRowAddress := by
  rw [card_outer_bounds, card_outer_rows]

theorem physical_bound_cardinality_decomposition :
    152 = 2 * (17 + 35) + (7 + 10 + 11 + 17) + 3 := by
  norm_num

#print axioms card_outer_rows
#print axioms card_outer_bounds
#print axioms card_inner_rows
#print axioms card_scalar_bounds
#print axioms card_all_physical_bounds
#print axioms outerRow_sourceGroup_isOuter
#print axioms innerRow_sourceGroup_isInner
#print axioms outerRow_order_agrees_with_owner
#print axioms innerRow_order_agrees_with_owner
#print axioms physical_bound_cardinality_decomposition

end D5.S3.PrimeGaps.PrimeGap186ExactCertificateIndex
