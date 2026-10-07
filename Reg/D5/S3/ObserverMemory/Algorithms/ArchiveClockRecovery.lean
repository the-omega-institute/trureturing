import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery
import Reg.Support.DependentFamily

open Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery

open _root_.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery

noncomputable section

universe uX uA uY

def signature : Signature where
  Params := Unit
  State := fun _ => Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ (n : Nat) => n ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ (_ : Nat) => (0 : Nat)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := forall {X : Type uX} {A : Type uA} {Y : Type uY},
    [Fintype X] -> [Fintype A] -> [Fintype Y] ->
    forall (n : Nat) (_hcard : Fintype.card X = n)
      (X0 : Set X) (_hX0 : X0.Nonempty) (S : System X A Y),
      List.TFAE [
        ArchiveRecoverable S X0,
        forall x, x ∈ X0 -> forall x', x' ∈ X0 -> forall word,
          SynchronizedPath S x x' word -> deltaSum S x x' word = 0,
        forall pair, SynchronouslyReachable S X0 pair -> forall a,
          SynchronizedEdge S pair a -> S.cost a pair.1 - S.cost a pair.2 = 0] ∧
      (Not (ArchiveRecoverable S X0) ->
        exists x, x ∈ X0 ∧ exists x', x' ∈ X0 ∧ exists word,
          Legal S x word ∧ Legal S x' word ∧
            visibleArchive S x word = visibleArchive S x' word ∧
            clock S x word ≠ clock S x' word ∧
            word.length <= R.readout () () n)

def ambiguitySystem :
    System (ULift.{uX} Bool) (ULift.{uA} Unit) (ULift.{uY} Unit) where
  domain := fun _ _ => True
  domainDecidable := fun _ _ => inferInstance
  successor := fun _ state => state
  reading := fun _ _ _ => ULift.up ()
  cost := fun _ state => if state.down then 1 else 0

theorem ambiguity_not_recoverable :
    ¬ ArchiveRecoverable ambiguitySystem Set.univ := by
  intro hrecoverable
  rcases hrecoverable with ⟨recover, hrecover⟩
  have hfalse := hrecover (ULift.up false) (Set.mem_univ _) [ULift.up ()] (by
    simp [Legal, ambiguitySystem])
  have htrue := hrecover (ULift.up true) (Set.mem_univ _) [ULift.up ()] (by
    simp [Legal, ambiguitySystem])
  simp [visibleArchive, clock, ambiguitySystem] at hfalse htrue
  omega

theorem rejected_law : ¬ arena.{uX, uA, uY}.Law rejected := by
  intro h
  have hspecial := h
    (X := ULift.{uX} Bool) (A := ULift.{uA} Unit) (Y := ULift.{uY} Unit)
    2 (by simp) Set.univ ⟨ULift.up false, Set.mem_univ _⟩ ambiguitySystem
  rcases hspecial.2 ambiguity_not_recoverable with
    ⟨x, _, x', _, word, _, _, _, hclock, hlength⟩
  have hzero : word.length = 0 := Nat.eq_zero_of_le_zero (by
    simpa [rejected, realize] using hlength)
  have hempty : word = [] := List.eq_nil_of_length_eq_zero hzero
  subst word
  simp [clock] at hclock

def registration : Registration arena.{uX, uA, uY}
    (arena.{uX, uA, uY}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨?_, rejected, rejected_law⟩
    intro X A Y instX instA instY n hcard X0 hX0 S
    simpa only [actual, realize, signature] using
      (@archive_clock_recovery_and_finite_ambiguity
        X A Y instX instA instY n hcard X0 hX0 S)
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hji
        exact False.elim (hji (show j = i from @Subsingleton.elim Unit _ j i))
      · funext e
        exact nomatch e
    · intro i
      exact nomatch i
  dependence := by
    intro i
    change Unit at i
    rcases i with ⟨⟩
    refine ⟨(), (0 : Nat), (1 : Nat), ?_⟩
    change (0 : Nat) ^ 2 ≠ (1 : Nat) ^ 2
    exact Nat.zero_ne_one

noncomputable def registration_1.{u_1, u_2, u_3} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.archive_clock_recovery_and_finite_ambiguity.{u_1, u_2, u_3}) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ (n : Nat) => n ^ 2) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ObserverMemory") "Algorithms") "ArchiveClockRecovery") "archive_clock_recovery_and_finite_ambiguity") "Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery/Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2, u_3}) ⟨(registration.{u_1, u_2, u_3})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ (n : Nat) => n ^ 2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "body", "arg", "arg", "body", "arg", "arg", "arg", "arg", "arg"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery, declaration := `D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.archive_clock_recovery_and_finite_ambiguity, part := .type, path := [], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery, declaration := `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery, declaration := `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery, declaration := `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery, declaration := `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] }], facts := [`Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1.canonicalArenaFact, `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1.sourceBridgeFact, `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1.observationFact0, `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1.anchorEnumeration }


#print axioms ambiguity_not_recoverable
#print axioms rejected_law
#print axioms registration

end

end Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery


noncomputable def Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1.canonicalArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1.canonicalArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Algorithms\",\"ArchiveClockRecovery\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Algorithms\",\"ArchiveClockRecovery\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery, declaration := `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery, declaration := `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence
noncomputable def Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1.canonicalObjectArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1.canonicalObjectArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Algorithms\",\"ArchiveClockRecovery\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Algorithms\",\"ArchiveClockRecovery\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery, declaration := `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery, declaration := `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence


noncomputable def Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1.sourceLaw.{u_1, u_2, u_3} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.arena.{u_1, u_2, u_3}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.arena.{u_1, u_2, u_3}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.arena.{u_1, u_2, u_3}
      Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.actual)
    Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration.{u_1, u_2, u_3})

noncomputable def Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1.sourceBridgeFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ObserverMemory\",\"Algorithms\",\"ArchiveClockRecovery\",\"archive_clock_recovery_and_finite_ambiguity\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Algorithms\",\"ArchiveClockRecovery\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery, declaration := `D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.archive_clock_recovery_and_finite_ambiguity, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery, declaration := `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.arena.{u_1, u_2, u_3}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.arena.{u_1, u_2, u_3}
    Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.actual)
  Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration.{u_1, u_2, u_3})

noncomputable def Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1.observation0.{u_1, u_2, u_3} : {X : Type u_1} →
  {A : Type u_2} →
    {Y : Type u_3} →
      [inst : Fintype.{u_1} X] →
        [Fintype.{u_2} A] →
          [Fintype.{u_3} Y] →
            (n : Nat) →
              (hcard : @Eq.{1} Nat (@Fintype.card.{u_1} X inst) n) →
                (X0 : Set.{u_1} X) →
                  (_hX0 : @Set.Nonempty.{u_1} X X0) →
                    (S : D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.System.{u_1, u_2, u_3} X A Y) →
                      Not
                          (@D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.ArchiveRecoverable.{u_1, u_2, u_3} X A
                            Y S X0) →
                        (x x' : X) →
                          (word : List.{u_2} A) →
                            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                              Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.signature PUnit.unit.{1}
                              PUnit.unit.{1} :=
  fun {X : Type u_1} {A : Type u_2} {Y : Type u_3} [Fintype.{u_1} X] [Fintype.{u_2} A] [Fintype.{u_3} Y] (n : Nat)
    (hcard : @Eq.{1} Nat (@Fintype.card.{u_1} X inst) n) (X0 : Set.{u_1} X) (_hX0 : @Set.Nonempty.{u_1} X X0)
    (S : D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.System.{u_1, u_2, u_3} X A Y)
    (a : Not (@D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.ArchiveRecoverable.{u_1, u_2, u_3} X A Y S X0))
    (x x' : X) (word : List.{u_2} A) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.signature
    Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.actual PUnit.unit.{1} PUnit.unit.{1} n

noncomputable def Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1.observationFact0.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ObserverMemory\",\"Algorithms\",\"ArchiveClockRecovery\",\"archive_clock_recovery_and_finite_ambiguity\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"argument\",\"body\",\"argument\",\"argument\",\"body\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Algorithms\",\"ArchiveClockRecovery\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery, declaration := `D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.archive_clock_recovery_and_finite_ambiguity, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .body, .argument, .body, .argument, .argument, .body, .argument, .argument, .body, .argument, .argument, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery, declaration := `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1.varyingLawInput.{u_1, u_2, u_3} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1.canonicalArenaOperand.{u_1, u_2, u_3})
noncomputable def Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1.varyingLaw.{u_1, u_2, u_3}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Algorithms\",\"ArchiveClockRecovery\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"

noncomputable def Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1.statementExclusion.{u_1, u_2, u_3} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Algorithms\",\"ArchiveClockRecovery\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ObserverMemory\",\"Algorithms\",\"ArchiveClockRecovery\",\"archive_clock_recovery_and_finite_ambiguity\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery, declaration := `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  statementLocation := { owner := `D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery, declaration := `D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.archive_clock_recovery_and_finite_ambiguity, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration.{u_1, u_2, u_3}).actual (Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration.{u_1, u_2, u_3}).variation.2.choose (Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration.{u_1, u_2, u_3}).variation.1 (Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration.{u_1, u_2, u_3}).variation.2.choose_spec

noncomputable def Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Algorithms\",\"ArchiveClockRecovery\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Algorithms\",\"ArchiveClockRecovery\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery, declaration := `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery, declaration := `Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))
