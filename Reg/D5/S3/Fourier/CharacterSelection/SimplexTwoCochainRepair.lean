import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair
import Reg.Support.DependentFamily
import Mathlib.Data.ZMod.Basic

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair

universe u v

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => 4 * n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {V : Type u} {A : Type v} [Fintype V] [Nonempty V] [AddCommGroup A]
    (F : V → V → V → A),
    (∑ r : V, faceErrors F r) = tetraDefects F ∧
      (∃ r : V, Fintype.card V * faceErrors F r ≤ tetraDefects F) ∧
      (∀ edge : V → V → A,
        tetraDefects F ≤
          R.readout () () (Fintype.card V) * edgeErrors F edge) ∧
      ((∀ r i j k, F i j k - F r j k + F r i k - F r i j = 0) ↔
        ∃ edge : V → V → A, ∀ i j k,
          F i j k = edge j k - edge i k + edge i j)

theorem actual_law : arena.{u, v}.Law actual := by
  intro V A _ _ _ F
  simpa [actual, realize, signature] using
    (_root_.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.tetra_defects_incidence_repair_and_exactness
      F)

theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  let V := ULift.{u} Bool
  let A := ULift.{v} (ZMod 2)
  let F : V → V → V → A := fun i _ _ =>
    if i.down then ULift.up (1 : ZMod 2) else ULift.up (0 : ZMod 2)
  have hbad := (h (V := V) (A := A) F).2.2.1 (fun _ _ => 0)
  norm_num [rejected, realize, signature, tetraDefects, F, edgeErrors] at hbad
  have hterm := hbad (⟨true⟩ : V) (⟨false⟩ : V)
  have hdown := congrArg ULift.down hterm
  change (0 : ZMod 2) - 1 = 0 at hdown
  exact (by decide : (0 : ZMod 2) - 1 ≠ 0) hdown

theorem sensitivity_proof : Sensitivity arena.{u, v} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize, signature]

def registration : Registration arena.{u, v} (arena.{u, v}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨
    _root_.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.tetra_defects_incidence_repair_and_exactness,
    rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.tetra_defects_incidence_repair_and_exactness.{u, v}) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => 4 * n) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Fourier") "CharacterSelection") "SimplexTwoCochainRepair") "tetra_defects_incidence_repair_and_exactness") "Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair/Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u, v})⟩,
  objectArena := .source ⟨(arena.{u, v})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u, v}) ⟨(registration.{u, v})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => 4 * n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "body", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair, declaration := `D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.tetra_defects_incidence_repair_and_exactness, part := .type, path := [], levels := [.param `u, .param `v] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair, declaration := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u, .param `v] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair, declaration := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u, .param `v] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair, declaration := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u, .param `v] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair, declaration := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u, .param `v] }], facts := [`Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1.canonicalArenaFact, `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1.sourceBridgeFact, `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1.observationFact0, `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1.anchorEnumeration }


#print axioms rejected_law
#print axioms actual_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair


noncomputable def Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1.canonicalArenaOperand.{u, v} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.arena.{u, v}
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1.canonicalArenaFact.{u, v} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"SimplexTwoCochainRepair\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"SimplexTwoCochainRepair\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair, declaration := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair, declaration := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  .evidence
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1.canonicalObjectArenaOperand.{u, v} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.arena.{u, v}
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1.canonicalObjectArenaFact.{u, v} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"SimplexTwoCochainRepair\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"SimplexTwoCochainRepair\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair, declaration := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair, declaration := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  .evidence


noncomputable def Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1.sourceLaw.{u, v} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.arena.{u, v}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.arena.{u, v}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.arena.{u, v}
      Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.actual)
    Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration.{u, v})

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1.sourceBridgeFact.{u, v} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"SimplexTwoCochainRepair\",\"tetra_defects_incidence_repair_and_exactness\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"SimplexTwoCochainRepair\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair, declaration := `D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.tetra_defects_incidence_repair_and_exactness, part := .type, path := [], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair, declaration := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.arena.{u, v}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.arena.{u, v}
    Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.actual)
  Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration.{u, v})

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1.observation0.{u, v} : {V : Type u} →
  {A : Type v} →
    [Fintype.{u} V] →
      [Nonempty.{u + 1} V] →
        [AddCommGroup.{v} A] →
          (F : V → V → V → A) →
            (edge : V → V → A) →
              D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun {V : Type u} {A : Type v} [inst : Fintype.{u} V] [Nonempty.{u + 1} V] [AddCommGroup.{v} A] (F : V → V → V → A)
    (edge : V → V → A) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.signature
    Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.actual PUnit.unit.{1} PUnit.unit.{1}
    (@Fintype.card.{u} V inst)

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1.observationFact0.{u, v} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"SimplexTwoCochainRepair\",\"tetra_defects_incidence_repair_and_exactness\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"function\",\"argument\",\"body\",\"argument\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"SimplexTwoCochainRepair\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair, declaration := `D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.tetra_defects_incidence_repair_and_exactness, part := .type, path := [.body, .body, .body, .body, .body, .body, .argument, .argument, .function, .argument, .body, .argument, .function, .argument], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair, declaration := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1.observation0, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1.varyingLawInput.{u, v} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1.canonicalArenaOperand.{u, v})
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1.varyingLaw.{u, v}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"SimplexTwoCochainRepair\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1.statementExclusion.{u, v} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"SimplexTwoCochainRepair\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"SimplexTwoCochainRepair\",\"tetra_defects_incidence_repair_and_exactness\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair, declaration := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  statementLocation := { owner := `D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair, declaration := `D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.tetra_defects_incidence_repair_and_exactness, part := .type, path := [], levels := [(.param `u), (.param `v)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration.{u, v}).actual (Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration.{u, v}).variation.2.choose (Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration.{u, v}).variation.1 (Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration.{u, v}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"SimplexTwoCochainRepair\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"SimplexTwoCochainRepair\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair, declaration := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair, declaration := `Reg.D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u), (.param `v)] }
  (by first | rfl | (ext <;> rfl))
