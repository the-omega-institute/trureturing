/- GID: D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Preemption is coded by endpoint and cause CUTs, ADMITS, and trace anchors. -/

import D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi

/- Library-search audit trail (2026-09-04): exact repository hits `PreemptionTrace`,
   `endState`, `activeCause`, `IsOrderedPreemption`, both named traces, and the frozen
   theorem are imported and reused. Mathlib supplies finite `Pi` instances. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause

open D5.S3.ConceptDynamics.CIRPT
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause

/-- Exhaustive finite coding of the two source mechanisms. -/
def mechanismEquiv : Mechanism ≃ Bool where
  toFun
    | .shooterA => false
    | .shooterB => true
  invFun
    | false => .shooterA
    | true => .shooterB
  left_inv := by intro mechanism; cases mechanism <;> rfl
  right_inv := by intro bit; cases bit <;> rfl

instance : Fintype Mechanism := Fintype.ofEquiv Bool mechanismEquiv.symm

instance (trace : PreemptionTrace) (first delayed : Mechanism) :
    Decidable (IsOrderedPreemption trace first delayed) := by
  unfold IsOrderedPreemption
  infer_instance

/-- The two CUT and two ADMIT roles in the preemption statement. -/
inductive PreemptionReadout
  | cutEnd
  | cutCause
  | admitAThenB
  | admitBThenA
  deriving DecidableEq

instance : Fintype PreemptionReadout where
  elems := {.cutEnd, .cutCause, .admitAThenB, .admitBThenA}
  complete := by intro i; cases i <;> simp

/-- The two named trace witnesses used as point anchors. -/
inductive PreemptionAnchor
  | aThenB
  | bThenA
  deriving DecidableEq

instance : Fintype PreemptionAnchor where
  elems := {.aThenB, .bThenA}
  complete := by intro i; cases i <;> simp

/-- Typed CUT/CUT/ADMIT/ADMIT signature with both source witnesses anchored. -/
abbrev preemptionSignature : PrimitiveSignature PreemptionTrace where
  Index := PreemptionReadout
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output
    | .cutEnd => Bool
    | .cutCause => Option Mechanism
    | .admitAThenB => Bool
    | .admitBThenA => Bool
  outputDecidableEq
    | .cutEnd => inferInstance
    | .cutCause => inferInstance
    | .admitAThenB => inferInstance
    | .admitBThenA => inferInstance
  axis
    | .cutEnd => .cut
    | .cutCause => .cut
    | .admitAThenB => .admit
    | .admitBThenA => .admit
  readoutAxisNotAnchor := by intro i; cases i <;> simp
  AnchorIndex := PreemptionAnchor
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

/-- The exact proposition proved by the frozen preemption theorem. -/
def EndStateOmitsPreemptingCauseStatement : Prop :=
  IsOrderedPreemption aThenB .shooterA .shooterB /\
    IsOrderedPreemption bThenA .shooterB .shooterA /\
    endState aThenB = endState bThenA /\
    activeCause aThenB ≠ activeCause bThenA /\
    ¬ ∃ recover : Bool -> Option Mechanism,
      activeCause = recover ∘ endState

/-- The five source clauses stated through realization readouts and anchors. -/
def endStateOmitsPreemptingCauseArena : PrimitiveLawArena where
  toArena := Arena.ofFintype PreemptionTrace
  signature := preemptionSignature
  Law := fun r =>
    r.readout .admitAThenB (r.anchor .aThenB) = true /\
      r.readout .admitBThenA (r.anchor .bThenA) = true /\
      r.readout .cutEnd (r.anchor .aThenB) =
        r.readout .cutEnd (r.anchor .bThenA) /\
      r.readout .cutCause (r.anchor .aThenB) ≠
        r.readout .cutCause (r.anchor .bThenA) /\
      ¬ ∃ recover : Bool -> Option Mechanism,
        r.readout .cutCause = recover ∘ r.readout .cutEnd

end D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause
