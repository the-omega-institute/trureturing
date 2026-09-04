/- GID: D5/S3/ConceptDynamics/InformationEscapeArenas/LocalLawGluingObstruction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscapeArenas/LocalLawGluingObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The three-cycle gluing obstruction is expressed through three coded ADMIT readouts. -/

import D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit

/- Library-search audit trail (2026-09-04): exact repository hits for the frozen
   gluing theorem and `admit_readout_eq_true_iff` are imported and reused. Searches
   for a pre-existing typed gluing realization or fiber law found no further hit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscapeArenas.LocalLawGluingObstruction

open D5.S3.ConceptDynamics.CIRPT
open D5.S3.ConceptDynamics.InformationEscape

/-- The equality relation used by the two adjacent local laws. -/
def sameLaw : Set (Bool × Bool) := {pair | pair.1 = pair.2}

/-- The inequality relation used by the outer local law. -/
def differentLaw : Set (Bool × Bool) := {pair | pair.1 ≠ pair.2}

/-- The three ADMIT roles obtained by pulling the local laws back to triples. -/
inductive GluingReadout
  | admit01
  | admit12
  | admit02
  deriving DecidableEq

instance : Fintype GluingReadout where
  elems := {.admit01, .admit12, .admit02}
  complete := by intro i; cases i <;> simp

/-- Typed three-ADMIT signature on attempted global states. -/
abbrev localLawGluingSignature : PrimitiveSignature (Bool × Bool × Bool) where
  Index := GluingReadout
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Bool
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .admit
  readoutAxisNotAnchor := by intro i; cases i <;> simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

/-- The exact proposition proved by the frozen local-law gluing theorem. -/
def LocalLawGluingStatement : Prop :=
  (Prod.snd '' sameLaw = Prod.fst '' sameLaw /\
    Prod.fst '' sameLaw = Prod.fst '' differentLaw /\
    Prod.snd '' sameLaw = Prod.snd '' differentLaw) /\
  ¬ ∃ state : Bool × Bool × Bool,
    (state.1, state.2.1) ∈ sameLaw /\
    (state.2.1, state.2.2) ∈ sameLaw /\
    (state.1, state.2.2) ∈ differentLaw

/-- Marginal compatibility and global inconsistency through realization ADMIT slots. -/
def localLawGluingArena : PrimitiveLawArena where
  toArena := Arena.ofFintype (Bool × Bool × Bool)
  signature := localLawGluingSignature
  Law := fun r =>
    (forall b : Bool,
      (∃ state, r.readout .admit01 state = true /\ state.2.1 = b) <->
        (∃ state, r.readout .admit12 state = true /\ state.2.1 = b)) /\
    (forall b : Bool,
      (∃ state, r.readout .admit01 state = true /\ state.1 = b) <->
        (∃ state, r.readout .admit02 state = true /\ state.1 = b)) /\
    (forall b : Bool,
      (∃ state, r.readout .admit12 state = true /\ state.2.2 = b) <->
        (∃ state, r.readout .admit02 state = true /\ state.2.2 = b)) /\
    ¬ ∃ state,
      r.readout .admit01 state = true /\
      r.readout .admit12 state = true /\
      r.readout .admit02 state = true

/-- The finite gluing arena contains at least two distinct attempted global states. -/
theorem localLawGluingArena_nondegenerate : localLawGluingArena.toArena.Nondegenerate := by
  decide

end D5.S3.ConceptDynamics.InformationEscapeArenas.LocalLawGluingObstruction
