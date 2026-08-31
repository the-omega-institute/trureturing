/- GID: D5/S3/ConceptDynamics/OperationalTuition/InstitutionalMappingAndCaptureFiltration
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/OperationalTuition/InstitutionalMappingAndCaptureFiltration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Append-only institutions yield decidable monotone capture filtrations. -/

import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Tactic.DeriveFintype

/- Library-search audit trail (2026-08-30):
   * Exact searches for `institution_domain_monotone_and_defect_decidable` and
     `capture_ladder_filtration_and_t1_nondecreasing` found no declaration in D5
     or pinned Mathlib.
   * Shape searches for domain monotonicity, decidable violations, prefix
     inclusion, and defect exceptions found only unrelated partial-map domains
     and general filtrations.
   * `DagSemantics/BirthStageFiltration.AppendOnly` is a nearby abstract monotone
     set family, but has no finite operational events, institution map, or defect
     locator.  The List prefix and finite rank-order primitives are reused below.

   Clause echo:
   * T-A: every institution registered in a trajectory prefix remains in the
     domain of every extension; established same-class recurrence has a Boolean
     decision procedure whose true result is equivalent to the violation Prop.
   * T-B: the wall/gate/author threshold sets form a filtration; for an already
     institutionalized class, capture is nondecreasing or the later event is the
     sole permitted alternative, a T1-flagged institutional defect located by an
     explicit prefix/suffix decomposition. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.OperationalTuition.InstitutionalMappingAndCaptureFiltration

-- Lean 4.33's stricter type check breaks mathlib's `Fintype` deriving handler.
set_option backward.isDefEq.respectTransparency.types false in
/-- The three capture levels. -/
inductive CaptureLevel where
  | wall
  | gate
  | author
deriving DecidableEq, Fintype, Repr

/-- Numeric rank inducing the operational order `wall < gate < author`. -/
def captureRank : CaptureLevel -> Nat
  | .wall => 0
  | .gate => 1
  | .author => 2

instance : LE CaptureLevel where
  le lower upper := captureRank lower ≤ captureRank upper

instance : LT CaptureLevel where
  lt lower upper := captureRank lower < captureRank upper

instance : Preorder CaptureLevel where
  le_refl level := Nat.le_refl (captureRank level)
  le_trans _ _ _ lowerMiddle middleUpper :=
    Nat.le_trans lowerMiddle middleUpper
  lt_iff_le_not_ge lower upper := by
    change captureRank lower < captureRank upper ↔
      captureRank lower ≤ captureRank upper ∧ ¬captureRank upper ≤ captureRank lower
    exact Nat.lt_iff_le_and_not_ge

def wall : CaptureLevel := .wall

def gate : CaptureLevel := .gate

def author : CaptureLevel := .author

/-- Error classes are quotients by equality of repair profiles: two raw events
belong to one class exactly when every institution prevents both or neither. -/
abbrev RepairClass (RawEvent Institution : Type*)
    (prevents : Institution -> RawEvent -> Prop) :=
  Quotient (Setoid.ker (fun event => fun institution => prevents institution event))

/-- The canonical classification map into the same-repair quotient. -/
def classifyByRepair {RawEvent Institution : Type*}
    (prevents : Institution -> RawEvent -> Prop) (event : RawEvent) :
    RepairClass RawEvent Institution prevents :=
  Quotient.mk _ event

/-- A finite-trace event records its error class, capture level, institution
registration action, and whether operations flagged it as an institutional defect. -/
structure Event (ErrorClass : Type*) where
  errorClass : ErrorClass
  capture : CaptureLevel
  registersInstitution : Bool
  institutionalDefect : Bool
deriving DecidableEq, Repr

/-- A finite operational trajectory.  `institution` names the policy assigned to
each class; its partial registration map is derived from the append-only event log. -/
structure OperationalTrajectory (ErrorClass Institution : Type*) where
  events : List (Event ErrorClass)
  institution : ErrorClass -> Institution

/-- Definition 3.1's maturity carrier: the chronological capture history internal
to one error class, distinct from the trajectory's overall error rate. -/
def classMaturity {ErrorClass Institution : Type*} [DecidableEq ErrorClass]
    (trajectory : OperationalTrajectory ErrorClass Institution)
    (errorClass : ErrorClass) : List CaptureLevel :=
  trajectory.events.filterMap fun event =>
    if event.errorClass = errorClass then some event.capture else none

/-- Whether a class has already occurred in a finite event prefix. -/
def classOccurred {ErrorClass : Type*} [DecidableEq ErrorClass]
    (history : List (Event ErrorClass)) (errorClass : ErrorClass) : Bool :=
  history.any fun event => decide (event.errorClass = errorClass)

/-- Whether an event prefix has registered an institution for a class. -/
def institutionEstablished {ErrorClass : Type*} [DecidableEq ErrorClass]
    (history : List (Event ErrorClass)) (errorClass : ErrorClass) : Bool :=
  history.any fun event =>
    decide (event.errorClass = errorClass) && event.registersInstitution

/-- The partial institution map after a prefix.  Its defined domain can only grow
because registration evidence is retained by List extension. -/
def institutionAt {ErrorClass Institution : Type*} [DecidableEq ErrorClass]
    (trajectory : OperationalTrajectory ErrorClass Institution)
    (history : List (Event ErrorClass)) (errorClass : ErrorClass) : Option Institution :=
  if institutionEstablished history errorClass then
    some (trajectory.institution errorClass)
  else
    none

/-- The defined domain of the institution map at the end of a trajectory. -/
def institutionDomain {ErrorClass Institution : Type*} [DecidableEq ErrorClass]
    (trajectory : OperationalTrajectory ErrorClass Institution) : Set ErrorClass :=
  {errorClass | institutionEstablished trajectory.events errorClass = true}

/-- Prefix order for trajectories with the same class-to-institution assignment. -/
def IsTrajectoryPrefix {ErrorClass Institution : Type*}
    (earlier later : OperationalTrajectory ErrorClass Institution) : Prop :=
  earlier.institution = later.institution ∧ earlier.events <+: later.events

/-- An established class has recurred: this is the finite, decidable T1 violation
state called an institutional-defect event in the source theory. -/
def InstitutionalDefect {ErrorClass : Type*} [DecidableEq ErrorClass]
    (history : List (Event ErrorClass)) (current : Event ErrorClass) : Prop :=
  classOccurred history current.errorClass = true ∧
    institutionEstablished history current.errorClass = true

/-- Executable classifier for the institutional-defect state. -/
def defectDecision {ErrorClass : Type*} [DecidableEq ErrorClass]
    (history : List (Event ErrorClass)) (current : Event ErrorClass) : Bool :=
  classOccurred history current.errorClass &&
    institutionEstablished history current.errorClass

/-- T1 compliance is a trace predicate, not a Lean axiom.  Append-only
registration is enforced by `institutionAt`; this clause requires every actual
established-class recurrence to carry the institutional-defect flag. -/
def T1Compliant {ErrorClass Institution : Type*} [DecidableEq ErrorClass]
    (trajectory : OperationalTrajectory ErrorClass Institution) : Prop :=
  ∀ history current suffix,
    trajectory.events = history ++ current :: suffix ->
    InstitutionalDefect history current ->
    current.institutionalDefect = true

/-- A trajectory packages the defining T1 operational law as evidence. -/
structure T1CompliantTrajectory (ErrorClass Institution : Type*)
    [DecidableEq ErrorClass]
    extends OperationalTrajectory ErrorClass Institution where
  t1Compliant : T1Compliant toOperationalTrajectory

/-- Events captured no later than a threshold; the thresholds form the capture
filtration from wall through gate to author. -/
def captureFiltration {ErrorClass Institution : Type*}
    (trajectory : OperationalTrajectory ErrorClass Institution)
    (level : CaptureLevel) : Set (Event ErrorClass) :=
  {event | event ∈ trajectory.events ∧ event.capture ≤ level}

/-- A defect is located by the exact prefix ending immediately before it and the
suffix beginning immediately after it. -/
def LocatedInstitutionalDefect {ErrorClass Institution : Type*}
    [DecidableEq ErrorClass]
    (trajectory : OperationalTrajectory ErrorClass Institution)
    (current : Event ErrorClass) : Prop :=
  ∃ history suffix,
    trajectory.events = history ++ current :: suffix ∧
      InstitutionalDefect history current ∧
      current.institutionalDefect = true

private theorem institutionEstablished_mono_of_prefix
    {ErrorClass : Type*} [DecidableEq ErrorClass]
    {earlier later : List (Event ErrorClass)} {errorClass : ErrorClass}
    (isPrefix : earlier <+: later)
    (established : institutionEstablished earlier errorClass = true) :
    institutionEstablished later errorClass = true := by
  rcases isPrefix with ⟨tail, rfl⟩
  unfold institutionEstablished at established ⊢
  simp only [List.any_append, Bool.or_eq_true]
  exact Or.inl established

private theorem institution_domain_mono_of_prefix
    {ErrorClass Institution : Type*} [DecidableEq ErrorClass]
    {earlier later : OperationalTrajectory ErrorClass Institution}
    (isPrefix : IsTrajectoryPrefix earlier later) :
    institutionDomain earlier ⊆ institutionDomain later := by
  intro errorClass established
  rcases isPrefix with ⟨_, eventsPrefix⟩
  change institutionEstablished earlier.events errorClass = true at established
  change institutionEstablished later.events errorClass = true
  exact institutionEstablished_mono_of_prefix eventsPrefix established

/-- T-A: institution domains grow along trajectory prefixes, and the same-class
recurrence violation has an executable Boolean decision procedure. -/
theorem institution_domain_monotone_and_defect_decidable
    {ErrorClass Institution : Type*} [DecidableEq ErrorClass] :
    (∀ {earlier later : OperationalTrajectory ErrorClass Institution},
        IsTrajectoryPrefix earlier later ->
          institutionDomain earlier ⊆ institutionDomain later) ∧
      (∀ (history : List (Event ErrorClass)) (current : Event ErrorClass),
        defectDecision history current = true ↔
          InstitutionalDefect history current) := by
  constructor
  · intro earlier later isPrefix
    exact institution_domain_mono_of_prefix isPrefix
  · intro history current
    simp [defectDecision, InstitutionalDefect]

/-- T-B: capture thresholds form a filtration.  Between two events of an already
institutionalized class, either capture does not fall or the later event is the
T1-flagged institutional defect, with its precise trace location exhibited. -/
theorem capture_ladder_filtration_and_t1_nondecreasing
    {ErrorClass Institution : Type*} [DecidableEq ErrorClass]
    (trajectory : T1CompliantTrajectory ErrorClass Institution) :
    Monotone (captureFiltration trajectory.toOperationalTrajectory) ∧
      ∀ history earlier middle later suffix,
        trajectory.events =
            history ++ earlier :: middle ++ later :: suffix ->
        institutionEstablished history earlier.errorClass = true ->
        earlier.errorClass = later.errorClass ->
        earlier.capture ≤ later.capture ∨
          LocatedInstitutionalDefect trajectory.toOperationalTrajectory later := by
  constructor
  · intro lower upper levelsIncrease event captured
    exact ⟨captured.1, captured.2.trans levelsIncrease⟩
  · intro history earlier middle later suffix traceShape established sameClass
    right
    let defectPrefix := history ++ earlier :: middle
    have occurred : classOccurred defectPrefix later.errorClass = true := by
      simp [defectPrefix, classOccurred, sameClass]
    have institutionPersists :
        institutionEstablished defectPrefix later.errorClass = true := by
      apply institutionEstablished_mono_of_prefix
        (earlier := history) (later := defectPrefix)
      · exact ⟨earlier :: middle, rfl⟩
      · simpa [sameClass] using established
    have isDefect : InstitutionalDefect defectPrefix later :=
      ⟨occurred, institutionPersists⟩
    have locatedShape :
        trajectory.events = defectPrefix ++ later :: suffix := by
      simpa [defectPrefix, List.append_assoc] using traceShape
    have flagged : later.institutionalDefect = true :=
      trajectory.t1Compliant defectPrefix later suffix locatedShape isDefect
    exact ⟨defectPrefix, suffix, locatedShape, isDefect, flagged⟩

#print axioms institution_domain_monotone_and_defect_decidable
#print axioms capture_ladder_filtration_and_t1_nondecreasing

-- The finite capture carrier and its strict ladder are inhabited computationally.
example : CaptureLevel := author

example : wall < gate ∧ gate < author := by
  change (0 : Nat) < 1 ∧ (1 : Nat) < 2
  decide

private def sampleFirst : Event Bool where
  errorClass := false
  capture := wall
  registersInstitution := true
  institutionalDefect := true

private def sampleGate : Event Bool where
  errorClass := false
  capture := gate
  registersInstitution := false
  institutionalDefect := true

private def sampleDefect : Event Bool where
  errorClass := false
  capture := wall
  registersInstitution := false
  institutionalDefect := true

private def sampleTrajectory : OperationalTrajectory Bool Unit where
  events := [sampleFirst, sampleGate, sampleDefect]
  institution := fun _ => ()

-- T1 compliance has a concrete finite inhabitant with an established recurrence.
private def sampleCompliant : T1CompliantTrajectory Bool Unit where
  toOperationalTrajectory := sampleTrajectory
  t1Compliant := by
    intro history current suffix traceShape _
    have currentMem : current ∈ sampleTrajectory.events := by
      rw [traceShape]
      simp
    simp only [sampleTrajectory, List.mem_cons, List.not_mem_nil, or_false] at currentMem
    rcases currentMem with rfl | rfl | rfl
    all_goals rfl

-- The T-B premises are jointly satisfiable even when capture falls gate-to-wall:
-- the theorem locates the permitted institutional-defect branch.
example :
    sampleGate.capture ≤ sampleDefect.capture ∨
      LocatedInstitutionalDefect sampleTrajectory sampleDefect := by
  exact (capture_ladder_filtration_and_t1_nondecreasing sampleCompliant).2
    [sampleFirst] sampleGate [] sampleDefect [] rfl rfl rfl

-- The derived institution domain is nonempty on the concrete trace.
example : false ∈ institutionDomain sampleTrajectory := by
  change institutionEstablished sampleTrajectory.events false = true
  decide

example : classMaturity sampleTrajectory false = [wall, gate, wall] := by
  rfl

end D5.S3.ConceptDynamics.OperationalTuition.InstitutionalMappingAndCaptureFiltration
