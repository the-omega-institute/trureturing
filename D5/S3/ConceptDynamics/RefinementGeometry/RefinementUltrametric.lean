/- GID: D5/S3/ConceptDynamics/DefinitionEscape/RefinementUltrametric
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite definition history induces a canonical ultrametric pseudodistance by common agreement depth. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Omega

/- Library-search audit trail (2026-08-23):
   * `FiniteDiscussionStability` bounds the length of effective strict-refinement
     chains but does not construct a geometry on the underlying states.
   * Repository searches for common refinement depth, prefix ultrametric, and
     definition-history distance found no matching declaration.
   * `Nat.findGreatest` is reused as the pinned finite maximum operator. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.RefinementUltrametric

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- Two states agree through a depth when every readout before that depth gives
the same coordinate. Heterogeneous coordinate types are allowed at each level. -/
def AgreesThrough
    {X : Type*}
    (Coordinate : Nat → Type*)
    (readout : (level : Nat) → Concept X (Coordinate level))
    (depth : Nat) (x y : X) : Prop :=
  ∀ level, level < depth → readout level x = readout level y

@[simp] theorem agreesThrough_zero
    {X : Type*}
    (Coordinate : Nat → Type*)
    (readout : (level : Nat) → Concept X (Coordinate level))
    (x y : X) :
    AgreesThrough Coordinate readout 0 x y := by
  intro level impossible
  omega

/-- Agreement at a deeper level restricts to every shallower level. -/
theorem agreesThrough_mono
    {X : Type*}
    (Coordinate : Nat → Type*)
    (readout : (level : Nat) → Concept X (Coordinate level))
    {smaller larger : Nat} (depthOrder : smaller ≤ larger)
    {x y : X}
    (agreement : AgreesThrough Coordinate readout larger x y) :
    AgreesThrough Coordinate readout smaller x y := by
  intro level levelSmall
  exact agreement level (levelSmall.trans_le depthOrder)

/-- Agreement depth is symmetric. -/
theorem agreesThrough_symm
    {X : Type*}
    (Coordinate : Nat → Type*)
    (readout : (level : Nat) → Concept X (Coordinate level))
    {depth : Nat} {x y : X}
    (agreement : AgreesThrough Coordinate readout depth x y) :
    AgreesThrough Coordinate readout depth y x := by
  intro level levelDepth
  exact (agreement level levelDepth).symm

/-- Agreement depth is transitive. -/
theorem agreesThrough_trans
    {X : Type*}
    (Coordinate : Nat → Type*)
    (readout : (level : Nat) → Concept X (Coordinate level))
    {depth : Nat} {x y z : X}
    (left : AgreesThrough Coordinate readout depth x y)
    (right : AgreesThrough Coordinate readout depth y z) :
    AgreesThrough Coordinate readout depth x z := by
  intro level levelDepth
  exact (left level levelDepth).trans (right level levelDepth)

/-- The common depth is the greatest prefix length, bounded by the chosen finite
horizon, on which the two states agree. -/
noncomputable def commonDepth
    {X : Type*}
    (Coordinate : Nat → Type*)
    (readout : (level : Nat) → Concept X (Coordinate level))
    (horizon : Nat) (x y : X) : Nat := by
  classical
  exact Nat.findGreatest
    (fun depth => AgreesThrough Coordinate readout depth x y) horizon

/-- Common depth never exceeds the selected horizon. -/
theorem commonDepth_le_horizon
    {X : Type*}
    (Coordinate : Nat → Type*)
    (readout : (level : Nat) → Concept X (Coordinate level))
    (horizon : Nat) (x y : X) :
    commonDepth Coordinate readout horizon x y ≤ horizon := by
  classical
  unfold commonDepth
  exact Nat.findGreatest_le horizon

/-- The greatest depth found by `commonDepth` really is an agreement depth. -/
theorem agreesThrough_commonDepth
    {X : Type*}
    (Coordinate : Nat → Type*)
    (readout : (level : Nat) → Concept X (Coordinate level))
    (horizon : Nat) (x y : X) :
    AgreesThrough Coordinate readout
      (commonDepth Coordinate readout horizon x y) x y := by
  classical
  unfold commonDepth
  exact Nat.findGreatest_spec (Nat.zero_le horizon)
    (agreesThrough_zero Coordinate readout x y)

/-- Common depth is symmetric. -/
theorem commonDepth_symm
    {X : Type*}
    (Coordinate : Nat → Type*)
    (readout : (level : Nat) → Concept X (Coordinate level))
    (horizon : Nat) (x y : X) :
    commonDepth Coordinate readout horizon x y =
      commonDepth Coordinate readout horizon y x := by
  classical
  apply le_antisymm
  · unfold commonDepth
    apply Nat.le_findGreatest
    · exact Nat.findGreatest_le horizon
    · exact agreesThrough_symm Coordinate readout
        (agreesThrough_commonDepth Coordinate readout horizon x y)
  · unfold commonDepth
    apply Nat.le_findGreatest
    · exact Nat.findGreatest_le horizon
    · exact agreesThrough_symm Coordinate readout
        (agreesThrough_commonDepth Coordinate readout horizon y x)

/-- The finite refinement distance is the horizon minus common agreement depth.
States that remain indistinguishable longer are closer. -/
noncomputable def refinementDistance
    {X : Type*}
    (Coordinate : Nat → Type*)
    (readout : (level : Nat) → Concept X (Coordinate level))
    (horizon : Nat) (x y : X) : Nat :=
  horizon - commonDepth Coordinate readout horizon x y

@[simp] theorem refinementDistance_self
    {X : Type*}
    (Coordinate : Nat → Type*)
    (readout : (level : Nat) → Concept X (Coordinate level))
    (horizon : Nat) (x : X) :
    refinementDistance Coordinate readout horizon x x = 0 := by
  classical
  have selfAgreement :
      AgreesThrough Coordinate readout horizon x x := by
    intro level _
    rfl
  have fullDepth : commonDepth Coordinate readout horizon x x = horizon := by
    unfold commonDepth
    exact Nat.findGreatest_eq selfAgreement
  simp [refinementDistance, fullDepth]

/-- Refinement distance is symmetric. -/
theorem refinementDistance_symm
    {X : Type*}
    (Coordinate : Nat → Type*)
    (readout : (level : Nat) → Concept X (Coordinate level))
    (horizon : Nat) (x y : X) :
    refinementDistance Coordinate readout horizon x y =
      refinementDistance Coordinate readout horizon y x := by
  simp only [refinementDistance, commonDepth_symm Coordinate readout horizon x y]

/-- Zero distance is exactly full-horizon agreement. -/
theorem refinementDistance_eq_zero_iff_agreesThrough
    {X : Type*}
    (Coordinate : Nat → Type*)
    (readout : (level : Nat) → Concept X (Coordinate level))
    (horizon : Nat) (x y : X) :
    refinementDistance Coordinate readout horizon x y = 0 ↔
      AgreesThrough Coordinate readout horizon x y := by
  classical
  constructor
  · intro zeroDistance
    have depthBound := commonDepth_le_horizon
      Coordinate readout horizon x y
    have fullDepth : commonDepth Coordinate readout horizon x y = horizon := by
      unfold refinementDistance at zeroDistance
      omega
    rw [← fullDepth]
    exact agreesThrough_commonDepth Coordinate readout horizon x y
  · intro fullAgreement
    have fullDepth : commonDepth Coordinate readout horizon x y = horizon := by
      unfold commonDepth
      exact Nat.findGreatest_eq fullAgreement
    simp [refinementDistance, fullDepth]

/-- The induced distance satisfies the strong triangle inequality. -/
theorem refinementDistance_ultrametric
    {X : Type*}
    (Coordinate : Nat → Type*)
    (readout : (level : Nat) → Concept X (Coordinate level))
    (horizon : Nat) (x y z : X) :
    refinementDistance Coordinate readout horizon x z ≤
      max (refinementDistance Coordinate readout horizon x y)
        (refinementDistance Coordinate readout horizon y z) := by
  classical
  let depthXY := commonDepth Coordinate readout horizon x y
  let depthYZ := commonDepth Coordinate readout horizon y z
  let sharedDepth := min depthXY depthYZ
  have sharedLeHorizon : sharedDepth ≤ horizon := by
    exact (min_le_left depthXY depthYZ).trans
      (commonDepth_le_horizon Coordinate readout horizon x y)
  have agreementXY : AgreesThrough Coordinate readout sharedDepth x y := by
    apply agreesThrough_mono Coordinate readout (min_le_left depthXY depthYZ)
    exact agreesThrough_commonDepth Coordinate readout horizon x y
  have agreementYZ : AgreesThrough Coordinate readout sharedDepth y z := by
    apply agreesThrough_mono Coordinate readout (min_le_right depthXY depthYZ)
    exact agreesThrough_commonDepth Coordinate readout horizon y z
  have agreementXZ : AgreesThrough Coordinate readout sharedDepth x z :=
    agreesThrough_trans Coordinate readout agreementXY agreementYZ
  have sharedLeXZ :
      sharedDepth ≤ commonDepth Coordinate readout horizon x z := by
    unfold commonDepth
    exact Nat.le_findGreatest sharedLeHorizon agreementXZ
  by_cases depthOrder : depthXY ≤ depthYZ
  · have depthXYLeXZ : depthXY ≤ commonDepth Coordinate readout horizon x z := by
      simpa [sharedDepth, min_eq_left depthOrder] using sharedLeXZ
    apply le_trans ?_ (le_max_left _ _)
    simp only [refinementDistance]
    omega
  · have depthYZLeXY : depthYZ ≤ depthXY := Nat.le_of_lt (lt_of_not_ge depthOrder)
    have depthYZLeXZ : depthYZ ≤ commonDepth Coordinate readout horizon x z := by
      simpa [sharedDepth, min_eq_right depthYZLeXY] using sharedLeXZ
    apply le_trans ?_ (le_max_right _ _)
    simp only [refinementDistance]
    omega

/-- A finite readout history separates states when full-horizon agreement forces
state equality. -/
def SeparatesByHorizon
    {X : Type*}
    (Coordinate : Nat → Type*)
    (readout : (level : Nat) → Concept X (Coordinate level))
    (horizon : Nat) : Prop :=
  ∀ ⦃x y : X⦄, AgreesThrough Coordinate readout horizon x y → x = y

/-- Under separation, the pseudodistance has the ordinary identity-of-indiscernibles
property and is therefore a finite ultrametric. -/
theorem refinementDistance_eq_zero_iff_eq
    {X : Type*}
    (Coordinate : Nat → Type*)
    (readout : (level : Nat) → Concept X (Coordinate level))
    (horizon : Nat)
    (separates : SeparatesByHorizon Coordinate readout horizon)
    (x y : X) :
    refinementDistance Coordinate readout horizon x y = 0 ↔ x = y := by
  constructor
  · intro zeroDistance
    exact separates
      ((refinementDistance_eq_zero_iff_agreesThrough
        Coordinate readout horizon x y).1 zeroDistance)
  · rintro rfl
    exact refinementDistance_self Coordinate readout horizon x

private def bitCoordinate : Nat → Type
  | 0 => Bool
  | _ => Unit

private def bitReadout : (level : Nat) → Concept Bool (bitCoordinate level)
  | 0 => id
  | _ => fun _ => ()

private theorem bitReadout_separates :
    SeparatesByHorizon bitCoordinate bitReadout 1 := by
  intro left right agreement
  exact agreement 0 (by omega)

example :
    refinementDistance bitCoordinate bitReadout 1 false true ≠ 0 := by
  intro zeroDistance
  have statesEqual :=
    (refinementDistance_eq_zero_iff_eq bitCoordinate bitReadout 1
      bitReadout_separates false true).1 zeroDistance
  exact Bool.false_ne_true statesEqual

#print axioms refinementDistance_eq_zero_iff_agreesThrough
#print axioms refinementDistance_ultrametric
#print axioms refinementDistance_eq_zero_iff_eq

end D5.S3.ConceptDynamics.DefinitionEscape.RefinementUltrametric
