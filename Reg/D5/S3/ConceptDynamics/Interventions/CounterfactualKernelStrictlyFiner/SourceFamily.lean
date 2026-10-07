import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.CausalSourceFamily

namespace Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner
open Reg.Support.CausalSourceFamily
open LeanInformationAudit

/-- An additional source-family occurrence preserves the complete original statement. -/
noncomputable def registration : Registration strictnessArena (Strictness actual) where
  actual := actual
  bridge := Iff.rfl
  variation := strictness_variation
  sensitivity := strictness_sensitivity
  dependence := dependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.counterfactual_kernel_strictly_finer) (type_of% (realize.{0, 0, 0, 0, 0} signature actual.readout actual.anchor)) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Interventions") "CounterfactualKernelStrictlyFiner") "counterfactual_kernel_strictly_finer") "Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily/Reg.Support.CausalSourceFamily.strictnessArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(strictnessArena)⟩,
  objectArena := .source ⟨(strictnessArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (strictnessArena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature actual.readout actual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner, definition := none, coordinates := #[], readouts := #[{ path := #["fn", "arg", "body", "body", "domain", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }, { path := #["fn", "arg", "body", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner, declaration := `D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.counterfactual_kernel_strictly_finer, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily, declaration := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily, declaration := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily, declaration := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily, declaration := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1.observationFact0, `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1.observationFact1, `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1.anchorEnumeration }


#print axioms registration
end Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily


noncomputable def Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.Support.CausalSourceFamily.strictnessArena
noncomputable def Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Interventions\",\"CounterfactualKernelStrictlyFiner\",\"SourceFamily\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Interventions\",\"CounterfactualKernelStrictlyFiner\",\"SourceFamily\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily, declaration := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily, declaration := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.Support.CausalSourceFamily.strictnessArena
noncomputable def Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Interventions\",\"CounterfactualKernelStrictlyFiner\",\"SourceFamily\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Interventions\",\"CounterfactualKernelStrictlyFiner\",\"SourceFamily\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily, declaration := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily, declaration := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.Support.CausalSourceFamily.strictnessArena) (Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration).actual

noncomputable def Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Interventions\",\"CounterfactualKernelStrictlyFiner\",\"counterfactual_kernel_strictly_finer\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Interventions\",\"CounterfactualKernelStrictlyFiner\",\"SourceFamily\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner, declaration := `D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.counterfactual_kernel_strictly_finer, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily, declaration := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration).bridge

noncomputable def Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Bool) where
  values := [Bool.true, Bool.false]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1.observation0 : (M N : D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
    Reg.Support.CausalSourceFamily.signature Bool.true PUnit.unit.{1} :=
  fun (M N : D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.Support.CausalSourceFamily.signature Reg.Support.CausalSourceFamily.actual Bool.true PUnit.unit.{1} M

noncomputable def Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Interventions\",\"CounterfactualKernelStrictlyFiner\",\"counterfactual_kernel_strictly_finer\"],\"part\":\"type\",\"path\":[\"function\",\"argument\",\"body\",\"body\",\"domain\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Interventions\",\"CounterfactualKernelStrictlyFiner\",\"SourceFamily\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner, declaration := `D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.counterfactual_kernel_strictly_finer, part := .type, path := [.function, .argument, .body, .body, .domain, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily, declaration := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1.observation1 : (M N : D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) →
  @Eq.{1} (Bool → Bool → Bool → Bool) (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.CF M)
      (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.CF N) →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      Reg.Support.CausalSourceFamily.signature Bool.false PUnit.unit.{1} :=
  fun (M N : D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM)
    (a :
      @Eq.{1} (Bool → Bool → Bool → Bool)
        (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.CF M)
        (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.CF N)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.Support.CausalSourceFamily.signature Reg.Support.CausalSourceFamily.actual Bool.false PUnit.unit.{1} M

noncomputable def Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1.observationFact1 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Interventions\",\"CounterfactualKernelStrictlyFiner\",\"counterfactual_kernel_strictly_finer\"],\"part\":\"type\",\"path\":[\"function\",\"argument\",\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Interventions\",\"CounterfactualKernelStrictlyFiner\",\"SourceFamily\",\"registration_1\",\"observation1\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner, declaration := `D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.counterfactual_kernel_strictly_finer, part := .type, path := [.function, .argument, .body, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily, declaration := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1.observation1, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Interventions\",\"CounterfactualKernelStrictlyFiner\",\"SourceFamily\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Interventions\",\"CounterfactualKernelStrictlyFiner\",\"SourceFamily\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Interventions\",\"CounterfactualKernelStrictlyFiner\",\"counterfactual_kernel_strictly_finer\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily, declaration := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner, declaration := `D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.counterfactual_kernel_strictly_finer, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration).actual (Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration).variation.2.choose (Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration).variation.1 (Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Interventions\",\"CounterfactualKernelStrictlyFiner\",\"SourceFamily\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Interventions\",\"CounterfactualKernelStrictlyFiner\",\"SourceFamily\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily, declaration := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily, declaration := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
