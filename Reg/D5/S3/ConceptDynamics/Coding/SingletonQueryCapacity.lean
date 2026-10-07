import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.FiberBinaryIdentification
open _root_.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity

universe u

abbrev signature : Signature where
  Params := Unit
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ d => d + 1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

open Classical in
def arena : Arena where
  signature := signature
  Law r := ∀ {X : Type u} [Fintype X] {depth : Nat}
    (protocol : BinaryProtocol X depth)
    (identifies : Function.Injective protocol.transcript)
    (questions : ∀ (round : Fin depth) (history : Fin round.val → Bool),
      (∃ answer : Bool, ∀ x, protocol.question round history x = answer) ∨
      (Finset.univ.filter fun x : X => protocol.question round history x = true).card ≤ 1),
    Fintype.card X ≤ r.readout () () depth

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let protocol : BinaryProtocol PUnit.{u+1} 0 := {
    transcript := fun _ => 0
    question := fun round => Fin.elim0 round
    transcript_consistent := by intro x round; exact Fin.elim0 round }
  have bad := h protocol (fun x y _ => Subsingleton.elim x y)
    (by intro round; exact Fin.elim0 round)
  change Fintype.card PUnit ≤ 0 at bad
  simpa using bad

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    intro X inst depth protocol identifies questions
    exact singleton_or_constant_query_capacity protocol identifies questions,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(), (0 : Nat), (1 : Nat), ?_⟩
    change (1 : Nat) ≠ 2
    decide

noncomputable def registration_1.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.singleton_or_constant_query_capacity.{u_1}) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ d => d + 1) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "SingletonQueryCapacity") "singleton_or_constant_query_capacity") "Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity/Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1})⟩,
  objectArena := .source ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ d => d + 1) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity, declaration := `D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.singleton_or_constant_query_capacity, part := .type, path := [], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity, declaration := `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity, declaration := `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity, declaration := `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity, declaration := `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1] }], facts := [`Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1.observationFact0, `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity


noncomputable def Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1.canonicalArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.arena.{u_1}
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1.canonicalArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"SingletonQueryCapacity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"SingletonQueryCapacity\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity, declaration := `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity, declaration := `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1.canonicalObjectArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.arena.{u_1}
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1.canonicalObjectArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"SingletonQueryCapacity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"SingletonQueryCapacity\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity, declaration := `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity, declaration := `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence


noncomputable def Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1.sourceLaw.{u_1} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.arena.{u_1}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.arena.{u_1}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.arena.{u_1}
      Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.actual)
    Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration.{u_1})

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1.sourceBridgeFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"SingletonQueryCapacity\",\"singleton_or_constant_query_capacity\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"SingletonQueryCapacity\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity, declaration := `D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.singleton_or_constant_query_capacity, part := .type, path := [], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity, declaration := `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.arena.{u_1}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.arena.{u_1}
    Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.actual)
  Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration.{u_1})

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1.observation0.{u_1} : {X : Type u_1} →
  [inst : Fintype.{u_1} X] →
    {depth : Nat} →
      (protocol : D5.S3.ConceptDynamics.Coding.FiberBinaryIdentification.BinaryProtocol.{u_1} X depth) →
        (identifies :
            @Function.Injective.{u_1 + 1, 1} X (BitVec depth)
              (@D5.S3.ConceptDynamics.Coding.FiberBinaryIdentification.BinaryProtocol.transcript.{u_1} X depth
                protocol)) →
          (questions :
              ∀ (round : Fin depth) (history : Fin (@Fin.val depth round) → Bool),
                Or
                  (@Exists.{1} Bool fun (answer : Bool) =>
                    ∀ (x : X),
                      @Eq.{1} Bool
                        (@D5.S3.ConceptDynamics.Coding.FiberBinaryIdentification.BinaryProtocol.question.{u_1} X depth
                          protocol round history x)
                        answer)
                  (@LE.le.{0} Nat instLENat
                    (@Finset.card.{u_1} X
                      (@Finset.filter.{u_1} X
                        (fun (x : X) =>
                          @Eq.{1} Bool
                            (@D5.S3.ConceptDynamics.Coding.FiberBinaryIdentification.BinaryProtocol.question.{u_1} X
                              depth protocol round history x)
                            Bool.true)
                        (fun (a : X) =>
                          Classical.propDecidable
                            (@Eq.{1} Bool
                              (@D5.S3.ConceptDynamics.Coding.FiberBinaryIdentification.BinaryProtocol.question.{u_1} X
                                depth protocol round history a)
                              Bool.true))
                        (@Finset.univ.{u_1} X inst)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun {X : Type u_1} [Fintype.{u_1} X] {depth : Nat}
    (protocol : D5.S3.ConceptDynamics.Coding.FiberBinaryIdentification.BinaryProtocol.{u_1} X depth)
    (identifies :
      @Function.Injective.{u_1 + 1, 1} X (BitVec depth)
        (@D5.S3.ConceptDynamics.Coding.FiberBinaryIdentification.BinaryProtocol.transcript.{u_1} X depth protocol))
    (questions :
      ∀ (round : Fin depth) (history : Fin (@Fin.val depth round) → Bool),
        Or
          (@Exists.{1} Bool fun (answer : Bool) =>
            ∀ (x : X),
              @Eq.{1} Bool
                (@D5.S3.ConceptDynamics.Coding.FiberBinaryIdentification.BinaryProtocol.question.{u_1} X depth protocol
                  round history x)
                answer)
          (@LE.le.{0} Nat instLENat
            (@Finset.card.{u_1} X
              (@Finset.filter.{u_1} X
                (fun (x : X) =>
                  @Eq.{1} Bool
                    (@D5.S3.ConceptDynamics.Coding.FiberBinaryIdentification.BinaryProtocol.question.{u_1} X depth
                      protocol round history x)
                    Bool.true)
                (fun (a : X) =>
                  Classical.propDecidable
                    (@Eq.{1} Bool
                      (@D5.S3.ConceptDynamics.Coding.FiberBinaryIdentification.BinaryProtocol.question.{u_1} X depth
                        protocol round history a)
                      Bool.true))
                (@Finset.univ.{u_1} X inst)))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.signature
    Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.actual PUnit.unit.{1} PUnit.unit.{1} depth

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1.observationFact0.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"SingletonQueryCapacity\",\"singleton_or_constant_query_capacity\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"SingletonQueryCapacity\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity, declaration := `D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.singleton_or_constant_query_capacity, part := .type, path := [.body, .body, .body, .body, .body, .body, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity, declaration := `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1.varyingLawInput.{u_1} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1.canonicalArenaOperand.{u_1})
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1.varyingLaw.{u_1}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"SingletonQueryCapacity\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1.statementExclusion.{u_1} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"SingletonQueryCapacity\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"SingletonQueryCapacity\",\"singleton_or_constant_query_capacity\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity, declaration := `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1)] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity, declaration := `D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.singleton_or_constant_query_capacity, part := .type, path := [], levels := [(.param `u_1)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration.{u_1}).actual (Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration.{u_1}).variation.2.choose (Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration.{u_1}).variation.1 (Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration.{u_1}).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"SingletonQueryCapacity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"SingletonQueryCapacity\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity, declaration := `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity, declaration := `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))
