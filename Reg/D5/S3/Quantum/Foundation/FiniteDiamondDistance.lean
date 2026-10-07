import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Foundation.FiniteDiamondDistance
import Reg.Support.DependentFamily

open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance
open _root_.D5.S3.Quantum.Foundation.FiniteDiamondDistance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped CStarAlgebra ComplexOrder MatrixOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance
universe u v

abbrev signature : Signature where
  Params := Unit
  State := fun _ => Set ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ states => sSup states) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law observation := ∀ {a b : Type u}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (first second : QuantumChannel a b),
    (∀ {R : Type v} [Fintype R] [DecidableEq R] (rho : DensityState (R × a)),
      ∃ tau : DensityState (R × a),
        IsPure tau ∧ referenceError first second rho ≤ referenceError first second tau) ∧
    (∀ {R : Type v} [Fintype R] [DecidableEq R] (rho : DensityState (R × a)),
      ∃ tau : DensityState (Fin (Fintype.card a) × a),
        IsPure tau ∧ referenceError first second rho ≤ referenceError first second tau) ∧
    diamondDistance first second =
      observation.readout () ()
        ({0} ∪ {x : ℝ | ∃ tau : DensityState (Fin (Fintype.card a) × a),
          IsPure tau ∧ x = referenceError first second tau})

theorem actual_law : arena.{u, v}.Law actual := by
  intro a b _ _ _ _ first second
  exact _root_.D5.S3.Quantum.Foundation.FiniteDiamondDistance.result first second

theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  let q := ULift.{u} Unit
  let channel : QuantumChannel q q := {
    toCompletelyPositiveMap := {
      toLinearMap := LinearMap.id
      map_cstarMatrix_nonneg' := by
        intro k X hX
        change 0 ≤ X.map id
        simpa only [CStarMatrix.map_id] using hX }
    trace_preserving := by intro X; rfl }
  have hd : 0 ≤ diamondDistance channel channel := by
    apply Real.sSup_nonneg'
    exact ⟨0, Or.inl (Set.mem_singleton 0), le_rfl⟩
  have hbad := (h channel channel).2.2
  change diamondDistance channel channel = (-1 : ℝ) at hbad
  rw [hbad] at hd
  norm_num at hd

theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), {0}, {1}, ?_⟩
  change sSup ({0} : Set ℝ) ≠ sSup ({1} : Set ℝ)
  rw [csSup_singleton, csSup_singleton]
  norm_num

def registration : Registration arena.{u, v} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Foundation.FiniteDiamondDistance.result.{u, v}) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ states => sSup.{0} states) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Foundation") "FiniteDiamondDistance") "result") "Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance/Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u, v})⟩,
  objectArena := .source ⟨(arena.{u, v})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u, v}) ⟨(registration.{u, v})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ states => sSup.{0} states) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Foundation.FiniteDiamondDistance, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Foundation.FiniteDiamondDistance, declaration := `D5.S3.Quantum.Foundation.FiniteDiamondDistance.result, part := .type, path := [], levels := [.param `u, .param `v] },
    { owner := `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance, declaration := `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u, .param `v] },
    { owner := `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance, declaration := `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u, .param `v] },
    { owner := `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance, declaration := `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u, .param `v] },
    { owner := `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance, declaration := `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u, .param `v] }], facts := [`Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1.observationFact0, `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1.anchorEnumeration }


#print axioms registration
end Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance


noncomputable def Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1.canonicalArenaOperand.{u, v} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.arena.{u, v}
noncomputable def Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1.canonicalArenaFact.{u, v} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Foundation\",\"FiniteDiamondDistance\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Foundation\",\"FiniteDiamondDistance\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance, declaration := `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance, declaration := `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1.canonicalObjectArenaOperand.{u, v} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.arena.{u, v}
noncomputable def Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1.canonicalObjectArenaFact.{u, v} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Foundation\",\"FiniteDiamondDistance\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Foundation\",\"FiniteDiamondDistance\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance, declaration := `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance, declaration := `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1.sourceLaw.{u, v} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.arena.) (Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration.{u, v}).actual

noncomputable def Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1.sourceBridgeFact.{u, v} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Foundation\",\"FiniteDiamondDistance\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Foundation\",\"FiniteDiamondDistance\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `D5.S3.Quantum.Foundation.FiniteDiamondDistance, declaration := `D5.S3.Quantum.Foundation.FiniteDiamondDistance.result, part := .type, path := [], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance, declaration := `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  (Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration.{u, v}).bridge

noncomputable def Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1.observation0.{u} : {a b : Type u} →
  [inst : Fintype.{u} a] →
    [inst_1 : DecidableEq.{u + 1} a] →
      [inst_2 : Fintype.{u} b] →
        [inst_3 : DecidableEq.{u + 1} b] →
          (first second :
              @D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.{u, u} a b inst inst_1 inst_2 inst_3) →
            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun {a b : Type u} [inst : Fintype.{u} a] [inst_1 : DecidableEq.{u + 1} a] [inst_2 : Fintype.{u} b]
    [inst_3 : DecidableEq.{u + 1} b]
    (first second : @D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.{u, u} a b inst inst_1 inst_2 inst_3) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.signature
    Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.actual PUnit.unit.{1} PUnit.unit.{1}
    (@Union.union.{0} (Set.{0} Real) (@Set.instUnion.{0} Real)
      (@Singleton.singleton.{0, 0} Real (Set.{0} Real) (@Set.instSingletonSet.{0} Real)
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
      (@Set.ofPred.{0} Real fun (x : Real) =>
        @Exists.{u + 1}
          (@D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState.{u}
            (Prod.{0, u} (Fin (@Fintype.card.{u} a inst)) a)
            (@instFintypeProd.{0, u} (Fin (@Fintype.card.{u} a inst)) a (Fin.fintype (@Fintype.card.{u} a inst)) inst)
            fun (a_1 b : Prod.{0, u} (Fin (@Fintype.card.{u} a inst)) a) =>
            @instDecidableEqProd.{0, u} (Fin (@Fintype.card.{u} a inst)) a
              (instDecidableEqFin (@Fintype.card.{u} a inst)) inst_1 a_1 b)
          fun
            (tau :
              @D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState.{u}
                (Prod.{0, u} (Fin (@Fintype.card.{u} a inst)) a)
                (@instFintypeProd.{0, u} (Fin (@Fintype.card.{u} a inst)) a (Fin.fintype (@Fintype.card.{u} a inst))
                  inst)
                fun (a_1 b : Prod.{0, u} (Fin (@Fintype.card.{u} a inst)) a) =>
                @instDecidableEqProd.{0, u} (Fin (@Fintype.card.{u} a inst)) a
                  (instDecidableEqFin (@Fintype.card.{u} a inst)) inst_1 a_1 b) =>
          And
            (@D5.S3.Quantum.Foundation.FiniteDiamondDistance.IsPure.{u} (Prod.{0, u} (Fin (@Fintype.card.{u} a inst)) a)
              (@instFintypeProd.{0, u} (Fin (@Fintype.card.{u} a inst)) a (Fin.fintype (@Fintype.card.{u} a inst)) inst)
              (fun (a_1 b : Prod.{0, u} (Fin (@Fintype.card.{u} a inst)) a) =>
                @instDecidableEqProd.{0, u} (Fin (@Fintype.card.{u} a inst)) a
                  (instDecidableEqFin (@Fintype.card.{u} a inst)) inst_1 a_1 b)
              tau)
            (@Eq.{1} Real x
              (@D5.S3.Quantum.Foundation.FiniteDiamondDistance.referenceError.{0, u, u} (Fin (@Fintype.card.{u} a inst))
                a b (Fin.fintype (@Fintype.card.{u} a inst)) (instDecidableEqFin (@Fintype.card.{u} a inst)) inst inst_1
                inst_2 inst_3 first second tau))))

noncomputable def Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1.observationFact0.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Foundation\",\"FiniteDiamondDistance\",\"result\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Foundation\",\"FiniteDiamondDistance\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.Quantum.Foundation.FiniteDiamondDistance, declaration := `D5.S3.Quantum.Foundation.FiniteDiamondDistance.result, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .argument, .argument, .argument], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance, declaration := `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1.observation0, part := .value, path := [], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1.varyingLawInput.{u, v} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1.canonicalArenaOperand.{u, v})
noncomputable def Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1.varyingLaw.{u, v}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Foundation\",\"FiniteDiamondDistance\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1.statementExclusion.{u, v} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Foundation\",\"FiniteDiamondDistance\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Foundation\",\"FiniteDiamondDistance\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance, declaration := `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  statementLocation := { owner := `D5.S3.Quantum.Foundation.FiniteDiamondDistance, declaration := `D5.S3.Quantum.Foundation.FiniteDiamondDistance.result, part := .type, path := [], levels := [(.param `u), (.param `v)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration.{u, v}).actual (Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration.{u, v}).variation.2.choose (Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration.{u, v}).variation.1 (Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration.{u, v}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Foundation\",\"FiniteDiamondDistance\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Foundation\",\"FiniteDiamondDistance\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance, declaration := `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance, declaration := `Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u), (.param `v)] }
  (by first | rfl | (ext <;> rfl))
