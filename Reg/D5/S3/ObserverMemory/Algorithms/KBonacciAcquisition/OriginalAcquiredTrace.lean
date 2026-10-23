import Reg.Support.KBonacciAcquisition.ExecutionSource
import Reg.Support.KBonacciAcquisition.ActualPositiveCoordinates
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells OriginalNarrowCost OriginalExecutionBridge OriginalAcquiredTrace
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe z

@[reducible] def traceSignature : Signature where
  Params := Σ k : {k : ℕ // 2 ≤ k}, Σ m : ℕ, Type z
  State p := List Bool × NarrowWindowCost.Selector p.2.1 p.2.2 × ℕ ×
    Option (ZMod 2) × NarrowWindowCost.Archive p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Option (p.2.2 × ℕ)
  Anchor := Empty
  finiteAnchor := inferInstance

def traceActual : Realization traceSignature.{z} := realize traceSignature
  (fun _ p state => NarrowWindowCost.execute p.1.val (by have := p.1.property; omega)
    state.2.1 state.2.2.1 state.1 state.2.2.2.1 state.2.2.2.2)
  (fun e => nomatch e)

def traceRejected : Realization traceSignature.{z} :=
  realize traceSignature (fun _ _ _ => none) (fun e => nomatch e)

@[reducible] def traceArena : Arena where
  signature := traceSignature.{z}
  Law R := ∀ {Y : Type z} (k m : ℕ) (hk : 2 ≤ k)
    (localAlphabet : Bool) (f : Option (LiveRecord k) → Y)
    (history : List (AllowedBlock k m localAlphabet))
    (y₀ : Option (ZMod 2)) (archive : NarrowWindowCost.Archive m)
    (free : NarrowWindowCost.output k (by omega)
      (history.flatMap (fun action => List.ofFn action.val)) = y₀)
    (matched : ActualArchive k (by omega)
      (history.flatMap (fun action => List.ofFn action.val)) archive)
    (π : NarrowWindowCost.Selector m Y) (d c : ℕ),
    let w := history.flatMap (fun action => List.ofFn action.val)
    let initial := OriginalRecord k (by omega) w
    let current := OriginalRecord k (by omega) (w ++ archiveWords archive)
    R.readout () ⟨⟨k, hk⟩, m, Y⟩ (w ++ archiveWords archive, π, d, y₀, archive) =
        some (f initial, c) ↔
      ∃ issued, PaidTrace π y₀ current archive issued (f initial) ∧
        issued.length = c ∧ c ≤ d ∧ ActualArchive k (by omega) w (archive ++ issued) ∧
        (initial, OriginalRecord k (by omega) (w ++ archiveWords (archive ++ issued))) ∈
          AcquiredPairs k m (by omega) localAlphabet y₀ (archive ++ issued)

private theorem traceActualPositive : traceArena.{z}.Law traceActual := by
  intro Y k m hk localAlphabet f history y₀ archive free matched π d c
  exact acquired_execution_trace k m hk localAlphabet f history y₀ archive free matched π d c

private theorem traceRejectedNegative : ¬ traceArena.{z}.Law traceRejected := by
  intro h
  let label : ULift.{z} Unit := ⟨()⟩
  have rejected := h 3 1 (by decide) false (fun _ => label) [] (some 0) []
    (by rfl) trivial (fun _ _ => .inl label) 0 0
  have rhs : ∃ issued, PaidTrace (fun _ _ => .inl label) (some 0)
      (OriginalRecord 3 (by decide) ([] ++ archiveWords ([] : NarrowWindowCost.Archive 1)))
      [] issued (label) ∧ issued.length = 0 ∧ 0 ≤ 0 ∧
      ActualArchive 3 (by decide) [] ([] ++ issued) ∧
      (OriginalRecord 3 (by decide) [],
        OriginalRecord 3 (by decide) ([] ++ archiveWords ([] ++ issued))) ∈
        AcquiredPairs 3 1 (by decide) false (some 0) ([] ++ issued) := by
    refine ⟨[], rfl, rfl, le_rfl, trivial, ?_⟩
    exact ⟨[], rfl, trivial, rfl, rfl⟩
  have impossible := rejected.mpr rhs
  cases impossible

def traceEvidence : Registration traceArena.{z}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.acquired_execution_trace.{z})) where
  actual := traceActual
  bridge := Iff.rfl
  variation := ⟨traceActualPositive, traceRejected, traceRejectedNegative⟩
  sensitivity := ⟨fun i => ⟨traceRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, traceRejectedNegative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    let Y := ULift.{z} Bool
    let π : NarrowWindowCost.Selector 1 Y := fun y₀ _ => .inl ⟨decide (y₀ = some 0)⟩
    refine ⟨⟨⟨3, by decide⟩, 1, Y⟩,
      ([], π, 0, some 0, []), ([true], π, 0, some 1, []), ?_⟩
    simp [traceActual, realize, NarrowWindowCost.execute, π]
    intro h
    cases congrArg ULift.down h


end



namespace ArchiveLengthAudit
@[reducible] def signature : Signature where
  Params := ℕ
  State m := NarrowWindowCost.Archive m
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ ar => (archiveWords ar).length) (fun e => nomatch e)
def oracle : Realization signature := realize signature
  (fun _ _ ar => (archiveWords ar).length + 1) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (archive : NarrowWindowCost.Archive m),
    R.readout () m archive = archive.length * m
private theorem positive : arena.Law actual := archive_length
private theorem negative : ¬ arena.Law oracle := by
  intro law
  have bad := law ([] : NarrowWindowCost.Archive 1)
  norm_num [oracle, realize, archiveWords] at bad
def evidence : Registration arena (type_of% (@archive_length)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, oracle, negative⟩
  sensitivity := ⟨fun i => ⟨oracle, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, negative⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨1, [], [(fun _ => false, none)], ?_⟩
    cases i
    decide

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.archive_length)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.archive_length
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.ArchiveLengthAudit/Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.ArchiveLengthAudit.arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.ArchiveLengthAudit.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "fn", "arg"],
      stateBinder := 1,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms evidence
#print axioms registration
end ArchiveLengthAudit
#print axioms _root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.archive_length

end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.ActualArchiveReplyAudit

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells OriginalNarrowCost OriginalAcquiredTrace
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature where
  Params := ℕ
  State k := Set (Option (LiveRecord k) × Option (LiveRecord k))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ k := Set (Option (LiveRecord k) × Option (LiveRecord k)) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ A B => A = B) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k m : ℕ) (hk : 2 ≤ k) (localAlphabet : Bool)
    (sourceHistory : List (AllowedBlock k m localAlphabet))
    (archive : NarrowWindowCost.Archive m)
    (sourceArchive : ActualArchive k (by omega)
      (sourceHistory.flatMap (fun action => List.ofFn action.val)) archive)
    (B : Fin m → Bool) (reply : Option (ZMod 2)),
    let w := sourceHistory.flatMap (fun action => List.ofFn action.val)
    let y₀ := NarrowWindowCost.output k (by omega) w
    let cell : CandidateState k (Option (LiveRecord k)) :=
      ⟨AcquiredPairs k m (by omega) localAlphabet y₀ archive,
        ⟨(OriginalRecord k (by omega) w,
          OriginalRecord k (by omega) (w ++ archiveWords archive)),
          sourceHistory, rfl, sourceArchive, rfl, rfl⟩⟩
    R.readout () k (replyFiber k m cell B reply)
      (AcquiredPairs k m (by omega) localAlphabet y₀ (archive ++ [(B, reply)]))

private theorem actual_positive : arena.Law actual := by
  intro k m hk localAlphabet sourceHistory archive sourceArchive B reply
  exact actual_archive_reply k m hk localAlphabet sourceHistory archive sourceArchive B reply

private theorem rejected_negative : ¬ arena.Law rejected := by
  intro law
  have impossible := law 2 1 (by decide) false
    ([] : List (AllowedBlock 2 1 false))
    ([] : NarrowWindowCost.Archive 1)
    (by trivial)
    (fun _ : Fin 1 => false) none
  cases impossible

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let A0 : signature.State 2 := ∅
  let p : Option (LiveRecord 2) × Option (LiveRecord 2) := (none, none)
  let A1 : signature.State 2 := {p}
  refine ⟨2, A0, A1, ?_⟩
  intro h
  have h0 : (A0 = A0) = (A1 = A0) := by
    simpa [actual, realize] using congrFun h A0
  have hEq : A1 = A0 := Eq.mp h0 rfl
  have hp : p ∈ A1 := by simp [A1]
  rw [hEq] at hp
  simpa [A0] using hp

def evidence : Registration arena (type_of%
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.actual_archive_reply)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_positive, rejected, rejected_negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_negative
  dependence := dependence

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.actual_archive_reply)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str
      (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ObserverMemory") "Algorithms")
      "KBonacciAcquisition") "OriginalAcquiredTrace") "actual_archive_reply")
      "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.ActualArchiveReplyAudit/Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.ActualArchiveReplyAudit.arena/[anonymous]")
      "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.ActualArchiveReplyAudit.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms evidence
#print axioms registration

end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.ActualArchiveReplyAudit

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.ActualPositiveCoordinatesAudit
open Reg.Support.KBonacciAcquisition.ActualPositiveCoordinates
abbrev signature : Signature where
  Params := ℕ
  State k := Set (ZMod (k + 1))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ k := Set (ZMod (k + 1)) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ A B => A ⊆ B) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ A _ => A ⊆ ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k m : ℕ) (hk : 3 ≤ k) (short : m < k)
    (localAlphabet : Bool) (v previous : ZMod 2) (archive : NarrowWindowCost.Archive m)
    (parent : Fin m → Bool)
    (prior : archiveEndpoint (some v) archive = some previous),
    let acquired := archive ++ [(parent, some (previous + 1))]
    let A := initialSupport k m (by omega) localAlphabet v acquired
    R.readout () k A (physicalWindow k m archive.length) ∧
    (∀ j ∈ A, wordIncrement k (-j + ((archive.length * m : ℕ) : ZMod (k + 1))) parent = 1) ∧
    ∀ pair ∈ AcquiredPairs k m (by omega) localAlphabet (some v) acquired,
      ∃ initial current : LiveRecord k,
        pair.1 = some initial ∧ pair.2 = some current ∧
        current.value = previous + 1 ∧ current.tail < k ∧
        current.phase = initial.phase + (((archive.length + 1) * m : ℕ) : ZMod (k + 1))

private theorem positive : arena.Law actual := by
  intro k m hk short localAlphabet v previous archive parent prior
  exact actual_positive_coordinates k m hk short localAlphabet v previous archive parent prior

private theorem negative : ¬ arena.Law rejected := by
  intro law
  have h := law 3 1 (by decide) (by decide) true 0 0
    ([] : NarrowWindowCost.Archive 1) parent (by rfl)
  have impossible : initialSupport 3 1 (by decide) true 0 acquired ⊆
      (∅ : Set (ZMod 4)) := h.1
  exact impossible (support_member true)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let A0 : signature.State 3 := ∅
  let A1 : signature.State 3 := {0}
  refine ⟨3, A0, A1, ?_⟩
  intro same
  have eqProp : (A0 ⊆ A0) = (A1 ⊆ A0) := by
    simpa [actual, realize] using congrFun same A0
  have subset : A1 ⊆ A0 := Eq.mp eqProp (fun _ h => h)
  have member : (0 : ZMod 4) ∈ A1 := by simp [A1]
  exact subset member

def evidence : Registration arena (type_of%
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.actual_positive_coordinates)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected negative
  dependence := dependence

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.actual_positive_coordinates)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str
      (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ObserverMemory") "Algorithms")
      "KBonacciAcquisition") "OriginalAcquiredTrace") "actual_positive_coordinates")
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.ActualPositiveCoordinatesAudit/Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.ActualPositiveCoordinatesAudit.arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.ActualPositiveCoordinatesAudit.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace,
    definition := none, coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
#print axioms evidence
#print axioms registration
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.ActualPositiveCoordinatesAudit

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.ActualArchiveAppendAudit
open Reg.Support.KBonacciAcquisition.ActualPositiveCoordinates

abbrev signature : Signature where
  Params := Σ m : ℕ, NarrowWindowCost.Archive m
  State p := NarrowWindowCost.Archive p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := NarrowWindowCost.Archive p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p rest => p.2 ++ rest) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ p _ => [(fun _ : Fin p.1 => true, (none : Option (ZMod 2)))])
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (k : ℕ) (hk : 0 < k)
    (w : List Bool) (first rest : NarrowWindowCost.Archive m),
    ActualArchive k hk w (R.readout () ⟨m, first⟩ rest) ↔
      ActualArchive k hk w first ∧
        ActualArchive k hk (w ++ archiveWords first) rest

private theorem positive : arena.Law actual := @actual_archive_append

private theorem negative : ¬ arena.Law rejected := by
  intro law
  obtain ⟨initial, current, member, _⟩ := support_member true
  obtain ⟨history, _, matched, _, _⟩ := member
  let w := history.flatMap (fun action => List.ofFn action.val)
  have bad : ActualArchive 3 (by decide) w [(parent, none)] :=
    (law 3 (by decide) w acquired []).mpr ⟨matched, trivial⟩
  change NarrowWindowCost.output 3 (by decide) (w ++ List.ofFn parent) = none ∧ True at bad
  change NarrowWindowCost.output 3 (by decide) (w ++ List.ofFn parent) =
    some ((0 : ZMod 2) + 1) ∧ True at matched
  have impossible := matched.1.symm.trans bad.1
  cases impossible

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, []⟩, [], acquired, ?_⟩
  simp [actual, realize, acquired]

def evidence : Registration arena (type_of%
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.actual_archive_append)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected negative
  dependence := dependence

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.actual_archive_append)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str
      (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ObserverMemory") "Algorithms")
      "KBonacciAcquisition") "OriginalAcquiredTrace") "actual_archive_append")
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.ActualArchiveAppendAudit/Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.ActualArchiveAppendAudit.arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.ActualArchiveAppendAudit.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace,
    definition := none, coordinates := #[0, 4],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg"],
      stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms evidence
#print axioms registration
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.ActualArchiveAppendAudit

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.AcquiredExecutionTraceAudit
universe z
open Reg.Support.KBonacciAcquisition.ExecutionSource.AcquiredExecutionTrace Reg.Support.KBonacciAcquisition.ExecutionSource.SelectorObservation
noncomputable def registration : LeanInformationAudit.Contract.Registration.{z+1,0,1,0,0,0,z+1,z,0,z,0,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.acquired_execution_trace.{z})
    (type_of% (realize signature.{z} actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.acquired_execution_trace
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.AcquiredExecutionTraceAudit/Reg.Support.KBonacciAcquisition.ExecutionSource.AcquiredExecutionTrace.arena/[anonymous]") "__information_unit",
  realizationName := `Reg.Support.KBonacciAcquisition.ExecutionSource.AcquiredExecutionTrace.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{z}⟩, objectArena := .source ⟨arena.{z}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{z} ⟨evidence.{z}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{z} actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace,
    definition := none, coordinates := #[0, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "fn", "fn", "fn", "arg"],
      stateBinder := 11, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
#print axioms registration
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.AcquiredExecutionTraceAudit

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.ExecutePaidTraceAudit
universe z
open Reg.Support.KBonacciAcquisition.ExecutionSource.ExecutePaidTrace Reg.Support.KBonacciAcquisition.ExecutionSource.SelectorObservation
noncomputable def registration : LeanInformationAudit.Contract.Registration.{z+1,0,1,0,0,0,z+1,z,0,z,0,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.execute_paid_trace.{z})
    (type_of% (realize signature.{z} actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.execute_paid_trace
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.ExecutePaidTraceAudit/Reg.Support.KBonacciAcquisition.ExecutionSource.ExecutePaidTrace.arena/[anonymous]") "__information_unit",
  realizationName := `Reg.Support.KBonacciAcquisition.ExecutionSource.ExecutePaidTrace.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{z}⟩, objectArena := .source ⟨arena.{z}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{z} ⟨evidence.{z}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{z} actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace,
    definition := none, coordinates := #[0, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "fn", "fn", "fn", "arg"],
      stateBinder := 4, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
#print axioms registration
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.ExecutePaidTraceAudit

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.FullPositiveParentAudit
open Reg.Support.KBonacciAcquisition.ExecutionSource.FullPositiveParent Reg.Support.KBonacciAcquisition.ExecutionSource.WindowObservation
noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.full_positive_parent)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.full_positive_parent
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.FullPositiveParentAudit/Reg.Support.KBonacciAcquisition.ExecutionSource.FullPositiveParent.arena/[anonymous]") "__information_unit",
  realizationName := `Reg.Support.KBonacciAcquisition.ExecutionSource.FullPositiveParent.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace,
    definition := none, coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "domain", "arg"],
      stateBinder := 8, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
#print axioms registration
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.FullPositiveParentAudit

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.FullPositiveHistoryTraceAudit
universe z
open Reg.Support.KBonacciAcquisition.ExecutionSource.FullPositiveHistoryTrace Reg.Support.KBonacciAcquisition.ExecutionSource.WindowObservation
noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.full_positive_history_trace.{z})
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.full_positive_history_trace
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.FullPositiveHistoryTraceAudit/Reg.Support.KBonacciAcquisition.ExecutionSource.FullPositiveHistoryTrace.arena/[anonymous]") "__information_unit",
  realizationName := `Reg.Support.KBonacciAcquisition.ExecutionSource.FullPositiveHistoryTrace.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{z}⟩, objectArena := .source ⟨arena.{z}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{z} ⟨evidence.{z}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace,
    definition := none, coordinates := #[1, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "domain", "arg"],
      stateBinder := 9, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
#print axioms registration
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.FullPositiveHistoryTraceAudit

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.NativeExecutePaidTraceAudit
universe z
open Reg.Support.KBonacciAcquisition.ExecutionSource.NativeExecutePaidTrace Reg.Support.KBonacciAcquisition.ExecutionSource.SelectorObservation
noncomputable def registration : LeanInformationAudit.Contract.Registration.{z+1,0,1,0,0,0,z+1,z,0,z,0,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.native_execute_paid_trace.{z})
    (type_of% (realize signature.{z} actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.native_execute_paid_trace
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.NativeExecutePaidTraceAudit/Reg.Support.KBonacciAcquisition.ExecutionSource.NativeExecutePaidTrace.arena/[anonymous]") "__information_unit",
  realizationName := `Reg.Support.KBonacciAcquisition.ExecutionSource.NativeExecutePaidTrace.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{z}⟩, objectArena := .source ⟨arena.{z}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{z} ⟨evidence.{z}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{z} actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace,
    definition := none, coordinates := #[0, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "fn", "fn", "fn", "arg"],
      stateBinder := 3, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
#print axioms registration
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.NativeExecutePaidTraceAudit
