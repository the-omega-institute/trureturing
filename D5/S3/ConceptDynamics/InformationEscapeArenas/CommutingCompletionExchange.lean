/- GID: D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The completion countermodel is a law of two FLOW readouts and one Boolean CUT. -/

import D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import Mathlib.Tactic

/- Library-search audit trail (2026-09-04): exact repository hits
   `KernelEquivalent`, `predictiveProjection`, and the frozen countermodel theorem are
   imported and reused. Mathlib supplies `Fin 4` enumeration and finite transport. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange

open D5.S3.ConceptDynamics.CIRPT
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange
open D5.S3.ConceptDynamics.Sufficiency.MinimalPredictiveCompletionQuotient

/-- Constructor code for exhaustive FourState computation. -/
def fourStateCode : FourState -> Fin 4
  | .a => 0
  | .b => 1
  | .c => 2
  | .d => 3

/-- Inverse of the exhaustive FourState code. -/
def fourStateOfCode : Fin 4 -> FourState
  | 0 => .a
  | 1 => .b
  | 2 => .c
  | _ => .d

/-- Transparent equivalence used to enumerate the source carrier. -/
def fourStateEquiv : FourState ≃ Fin 4 where
  toFun := fourStateCode
  invFun := fourStateOfCode
  left_inv := by intro x; cases x <;> rfl
  right_inv := by intro x; fin_cases x <;> rfl

instance : Fintype FourState := Fintype.ofEquiv (Fin 4) fourStateEquiv.symm
instance : DecidableEq FourState := fourStateEquiv.decidableEq

/-- The two FLOW roles and one CUT role of the countermodel. -/
inductive CompletionReadout
  | flowF
  | flowG
  | cut
  deriving DecidableEq

instance : Fintype CompletionReadout where
  elems := {.flowF, .flowG, .cut}
  complete := by intro i; cases i <;> simp

/-- Typed FLOW/FLOW/CUT signature of the countermodel. -/
abbrev completionSignature : PrimitiveSignature FourState where
  Index := CompletionReadout
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output
    | .flowF => FourState
    | .flowG => FourState
    | .cut => Bool
  outputDecidableEq
    | .flowF => inferInstance
    | .flowG => inferInstance
    | .cut => inferInstance
  axis
    | .flowF => .flow
    | .flowG => .flow
    | .cut => .cut
  readoutAxisNotAnchor := by intro i; cases i <;> simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

/-- The exact proposition proved by the frozen completion countermodel theorem. -/
def CommutativityNecessaryStatement : Prop :=
  ¬ Function.Commute counterexampleF counterexampleG /\
    ¬ KernelEquivalent
      (predictiveProjection counterexampleF
        (predictiveProjection counterexampleG counterexampleReadout))
      (predictiveProjection counterexampleG
        (predictiveProjection counterexampleF counterexampleReadout))

/-- The frozen statement rewritten through the two FLOW slots and CUT slot. -/
def commutingCompletionArena : PrimitiveLawArena where
  toArena := Arena.ofFintype FourState
  signature := completionSignature
  Law := fun r =>
    ¬ Function.Commute (r.readout .flowF) (r.readout .flowG) /\
      ¬ KernelEquivalent
        (predictiveProjection (r.readout .flowF)
          (predictiveProjection (r.readout .flowG) (r.readout .cut)))
        (predictiveProjection (r.readout .flowG)
          (predictiveProjection (r.readout .flowF) (r.readout .cut)))

end D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange
