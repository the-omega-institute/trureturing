import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound
import Reg.Support.DependentFamily

namespace Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound

open _root_.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound
open _root_.D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

universe u v

def signature : Signature where
  Params := Σ Q : Type u, Σ F : Type v, Σ _ : F → Q → Q, Q → F → ℕ
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := List p.2.1 → ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u, v} :=
  realize signature.{u, v}
    (fun _ p initial ↦ Comm p.2.2.1 p.2.2.2 initial)
    (fun e ↦ nomatch e)

def rejected : Realization signature.{u, v} :=
  realize signature.{u, v} (fun _ _ _ _ ↦ 1) (fun e ↦ nomatch e)

def arena : Arena where
  signature := signature.{u, v}
  Law R := ∀ {Q : Type u} {F : Type v} [Fintype Q] [Nonempty Q] [Fintype F] [Nonempty F]
    (I : Set Q) (T : F → Q → Q) (w : Q → F → ℕ)
    (_hReach : ∀ state : Q, ∃ initial ∈ I, ∃ path : List F,
      runWord T path initial = state),
    let finiteInfinite := ∀ initial ∈ I, ∀ word : ℕ → F,
      InfiniteComm T w initial word ≠ ⊤
    let uniformlyBounded := ∃ bound : ℕ, ∀ initial ∈ I, ∀ word : List F,
      Comm T w initial word ≤ bound
    let zeroCycles := ∀ state : Q, ∀ cycle : List F, cycle ≠ [] →
      runWord T cycle state = state → Comm T w state cycle = 0
    List.TFAE [finiteInfinite, uniformlyBounded, zeroCycles] ∧
      (zeroCycles → ∀ initial ∈ I, ∀ word : List F,
        R.readout () ⟨Q, F, T, w⟩ initial word ≤
          (Fintype.card Q - 1) * maxEdgeCost w)

theorem rejected_law : ¬ arena.{u, v}.Law rejected.{u, v} := by
  intro law
  have specialized := law (Q := ULift.{u} Unit) (F := ULift.{v} Unit)
    Set.univ (fun _ state ↦ state) (fun _ _ ↦ 0)
    (fun state ↦ ⟨state, Set.mem_univ state, [], rfl⟩)
  have zeroCycles :
      ∀ state : ULift.{u} Unit, ∀ cycle : List (ULift.{v} Unit), cycle ≠ [] →
        runWord (fun _ state ↦ state) cycle state = state →
          Comm (fun _ state ↦ state) (fun _ _ ↦ 0) state cycle = 0 := by
    intro state cycle hNonempty hClosed
    clear hNonempty hClosed
    induction cycle generalizing state with
    | nil => rfl
    | cons action cycle ih =>
        simp only [Comm, zero_add]
        exact ih state
  have impossible := specialized.2 zeroCycles ⟨()⟩ (Set.mem_univ _) [⟨()⟩]
  norm_num [rejected, realize, signature, maxEdgeCost] at impossible

def registration : Registration arena.{u, v} (arena.{u, v}.Law actual.{u, v}) where
  actual := actual.{u, v}
  bridge := Iff.rfl
  variation := ⟨by
    intro Q F _ _ _ _ I T w hReach
    exact cumulative_communication_criterion I T w hReach
  , rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    let p : signature.{u, v}.Params := ⟨ULift.{u} Bool, ULift.{v} Unit,
      (fun _ state ↦ state), (fun state _ ↦ if state.down then 1 else 0)⟩
    refine ⟨p, ⟨false⟩, ⟨true⟩, ?_⟩
    intro readingsEqual
    have atOne := congrFun readingsEqual [⟨()⟩]
    norm_num [actual, realize, signature, p, Comm] at atOne

noncomputable def registration_1.{u_1, u_2} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.cumulative_communication_criterion.{u_1, u_2}) (type_of% (realize.{max (u_1 + 1) (u_2 + 1), u_1, 0, u_2, 0} signature.{u_1, u_2}
    (fun _ p initial ↦ Comm.{u_1, u_2} p.2.2.1 p.2.2.2 initial)
    (fun e ↦ nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ObserverMemory") "Prediction") "ActionGraphCommunicationBound") "cumulative_communication_criterion") "Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound/Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2}) ⟨(registration.{u_1, u_2})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{max (u_1 + 1) (u_2 + 1), u_1, 0, u_2, 0} signature.{u_1, u_2}
    (fun _ p initial ↦ Comm.{u_1, u_2} p.2.2.1 p.2.2.2 initial)
    (fun e ↦ nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound, definition := none, coordinates := #[0, 1, 7, 8], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "body", "body", "fn", "arg", "fn"], stateBinder := 14, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound, declaration := `D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.cumulative_communication_criterion, part := .type, path := [], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound, declaration := `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound, declaration := `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound, declaration := `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound, declaration := `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2] }], facts := [`Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1.canonicalArenaFact, `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1.sourceBridgeFact, `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1.observationFact0, `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1.anchorEnumeration }


#print axioms registration

end

end Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound


noncomputable def Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1.canonicalArenaOperand.{u_1, u_2} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (u_1 + 1) (u_2 + 1), u_1, 0, u_2, 0} :=
  Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.arena.{u_1, u_2}
noncomputable def Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1.canonicalArenaFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Prediction\",\"ActionGraphCommunicationBound\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Prediction\",\"ActionGraphCommunicationBound\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound, declaration := `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound, declaration := `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  .evidence
noncomputable def Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1.canonicalObjectArenaOperand.{u_1, u_2} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (u_1 + 1) (u_2 + 1), u_1, 0, u_2, 0} :=
  Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.arena.{u_1, u_2}
noncomputable def Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1.canonicalObjectArenaFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Prediction\",\"ActionGraphCommunicationBound\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Prediction\",\"ActionGraphCommunicationBound\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound, declaration := `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound, declaration := `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  .evidence


noncomputable def Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1.sourceLaw.{u_1, u_2} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{max (u_1 + 1) (u_2 + 1), u_1, 0, u_2, 0}
  Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.arena.{u_1, u_2}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{max (u_1 + 1) (u_2 + 1), u_1, 0, u_2,
        0}
    Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.arena.{u_1, u_2}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{max (u_1 + 1) (u_2 + 1), u_1, 0, u_2, 0}
      Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.arena.{u_1, u_2}
      Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.actual.{u_1, u_2})
    Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration.{u_1, u_2})

noncomputable def Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1.sourceBridgeFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ObserverMemory\",\"Prediction\",\"ActionGraphCommunicationBound\",\"cumulative_communication_criterion\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Prediction\",\"ActionGraphCommunicationBound\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound, declaration := `D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.cumulative_communication_criterion, part := .type, path := [], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound, declaration := `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{max (u_1 + 1) (u_2 + 1), u_1, 0, u_2, 0}
  Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.arena.{u_1, u_2}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{max (u_1 + 1) (u_2 + 1), u_1, 0, u_2, 0}
    Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.arena.{u_1, u_2}
    Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.actual.{u_1, u_2})
  Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration.{u_1, u_2})

noncomputable def Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1.observation0.{u_1, u_2} : {Q : Type u_1} →
  {F : Type u_2} →
    [Fintype.{u_1} Q] →
      [Nonempty.{u_1 + 1} Q] →
        [Fintype.{u_2} F] →
          [Nonempty.{u_2 + 1} F] →
            (I : Set.{u_1} Q) →
              (T : F → Q → Q) →
                (w : Q → F → Nat) →
                  (hReach :
                      ∀ (state : Q),
                        @Exists.{u_1 + 1} Q fun (initial : Q) =>
                          And (@Membership.mem.{u_1, u_1} Q (Set.{u_1} Q) (@Set.instMembership.{u_1} Q) I initial)
                            (@Exists.{u_2 + 1} (List.{u_2} F) fun (path : List.{u_2} F) =>
                              @Eq.{u_1 + 1} Q
                                (@D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality.runWord.{u_2, u_1} F Q
                                  T path initial)
                                state)) →
                    have zeroCycles : Prop :=
                      ∀ (state : Q) (cycle : List.{u_2} F),
                        @Ne.{u_2 + 1} (List.{u_2} F) cycle (@List.nil.{u_2} F) →
                          @Eq.{u_1 + 1} Q
                              (@D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality.runWord.{u_2, u_1} F Q T
                                cycle state)
                              state →
                            @Eq.{1} Nat
                              (@D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.Comm.{u_1, u_2} Q F T w
                                state cycle)
                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)));
                    zeroCycles →
                      (initial : Q) →
                        @Membership.mem.{u_1, u_1} Q (Set.{u_1} Q) (@Set.instMembership.{u_1} Q) I initial →
                          (word : List.{u_2} F) →
                            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{max (u_1 + 1)
                                  (u_2 + 1),
                                u_1, 0, u_2, 0}
                              Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.signature.{u_1, u_2}
                              PUnit.unit.{1}
                              (@Sigma.mk.{u_1 + 1, max (max u_1 u_2) (u_2 + 1)} (Type u_1)
                                (fun (Q : Type u_1) =>
                                  @Sigma.{u_2 + 1, max u_1 u_2} (Type u_2) fun (F : Type u_2) =>
                                    @Sigma.{max u_1 u_2, max u_1 u_2} (F → Q → Q) fun (x : F → Q → Q) => Q → F → Nat)
                                Q
                                (@Sigma.mk.{u_2 + 1, max u_1 u_2} (Type u_2)
                                  (fun (F : Type u_2) =>
                                    @Sigma.{max u_1 u_2, max u_1 u_2} (F → Q → Q) fun (x : F → Q → Q) => Q → F → Nat)
                                  F
                                  (@Sigma.mk.{max u_1 u_2, max u_1 u_2} (F → Q → Q) (fun (x : F → Q → Q) => Q → F → Nat)
                                    T w))) :=
  fun {Q : Type u_1} {F : Type u_2} [Fintype.{u_1} Q] [Nonempty.{u_1 + 1} Q] [Fintype.{u_2} F] [Nonempty.{u_2 + 1} F]
    (I : Set.{u_1} Q) (T : F → Q → Q) (w : Q → F → Nat)
    (hReach :
      ∀ (state : Q),
        @Exists.{u_1 + 1} Q fun (initial : Q) =>
          And (@Membership.mem.{u_1, u_1} Q (Set.{u_1} Q) (@Set.instMembership.{u_1} Q) I initial)
            (@Exists.{u_2 + 1} (List.{u_2} F) fun (path : List.{u_2} F) =>
              @Eq.{u_1 + 1} Q
                (@D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality.runWord.{u_2, u_1} F Q T path initial)
                state)) =>
  have finiteInfinite : Prop :=
    ∀ (initial : Q),
      @Membership.mem.{u_1, u_1} Q (Set.{u_1} Q) (@Set.instMembership.{u_1} Q) I initial →
        ∀ (word : Nat → F),
          @Ne.{1} ENat
            (@D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.InfiniteComm.{u_1, u_2} Q F T w initial
              word)
            (@Top.top.{0} ENat instTopENat);
  have uniformlyBounded : Prop :=
    @Exists.{1} Nat fun (bound : Nat) =>
      ∀ (initial : Q),
        @Membership.mem.{u_1, u_1} Q (Set.{u_1} Q) (@Set.instMembership.{u_1} Q) I initial →
          ∀ (word : List.{u_2} F),
            @LE.le.{0} Nat instLENat
              (@D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.Comm.{u_1, u_2} Q F T w initial word)
              bound;
  have zeroCycles : Prop :=
    ∀ (state : Q) (cycle : List.{u_2} F),
      @Ne.{u_2 + 1} (List.{u_2} F) cycle (@List.nil.{u_2} F) →
        @Eq.{u_1 + 1} Q
            (@D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality.runWord.{u_2, u_1} F Q T cycle state)
            state →
          @Eq.{1} Nat
            (@D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.Comm.{u_1, u_2} Q F T w state cycle)
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)));
  fun (a : zeroCycles) (initial : Q)
    (a_1 : @Membership.mem.{u_1, u_1} Q (Set.{u_1} Q) (@Set.instMembership.{u_1} Q) I initial) (word : List.{u_2} F) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{max (u_1 + 1) (u_2 + 1), u_1, 0, u_2, 0}
    Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.signature.{u_1, u_2}
    Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.actual.{u_1, u_2} PUnit.unit.{1}
    (@Sigma.mk.{u_1 + 1, max (max u_1 u_2) (u_2 + 1)} (Type u_1)
      (fun (Q : Type u_1) =>
        @Sigma.{u_2 + 1, max u_1 u_2} (Type u_2) fun (F : Type u_2) =>
          @Sigma.{max u_1 u_2, max u_1 u_2} (F → Q → Q) fun (x : F → Q → Q) => Q → F → Nat)
      Q
      (@Sigma.mk.{u_2 + 1, max u_1 u_2} (Type u_2)
        (fun (F : Type u_2) => @Sigma.{max u_1 u_2, max u_1 u_2} (F → Q → Q) fun (x : F → Q → Q) => Q → F → Nat) F
        (@Sigma.mk.{max u_1 u_2, max u_1 u_2} (F → Q → Q) (fun (x : F → Q → Q) => Q → F → Nat) T w)))
    initial

noncomputable def Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1.observationFact0.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ObserverMemory\",\"Prediction\",\"ActionGraphCommunicationBound\",\"cumulative_communication_criterion\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"letBody\",\"letBody\",\"letBody\",\"argument\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"function\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Prediction\",\"ActionGraphCommunicationBound\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound, declaration := `D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.cumulative_communication_criterion, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .letBody, .letBody, .letBody, .argument, .body, .body, .body, .body, .function, .argument, .function], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound, declaration := `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1.varyingLawInput.{u_1, u_2} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1.canonicalArenaOperand.{u_1, u_2})
noncomputable def Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1.varyingLaw.{u_1, u_2}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Prediction\",\"ActionGraphCommunicationBound\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"

noncomputable def Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1.statementExclusion.{u_1, u_2} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Prediction\",\"ActionGraphCommunicationBound\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ObserverMemory\",\"Prediction\",\"ActionGraphCommunicationBound\",\"cumulative_communication_criterion\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound, declaration := `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  statementLocation := { owner := `D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound, declaration := `D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.cumulative_communication_criterion, part := .type, path := [], levels := [(.param `u_1), (.param `u_2)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration.{u_1, u_2}).actual (Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration.{u_1, u_2}).variation.2.choose (Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration.{u_1, u_2}).variation.1 (Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration.{u_1, u_2}).variation.2.choose_spec

noncomputable def Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1.descriptorFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Prediction\",\"ActionGraphCommunicationBound\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Prediction\",\"ActionGraphCommunicationBound\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound, declaration := `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound, declaration := `Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2)] }
  (by first | rfl | (ext <;> rfl))
