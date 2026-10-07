import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError
import Reg.Support.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError

open _root_.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory
open scoped Interval NNReal

noncomputable section

local instance : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩

def signature : Signature where
  Params := ℝ≥0
  State _ := AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun (_ : Unit) (_ : ℝ≥0)
      (s : AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi)) =>
      (∫ x : AddCircle (2 * Real.pi), circle_error s x ∂AddCircle.haarAddCircle : ℝ))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

def lowerArena : Arena where
  signature := signature
  Law R := ∀ (L : ℝ≥0)
    (s : AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi)),
    LipschitzWith L s → 2 / (2 * (L : ℝ) + 1) ≤ R.readout () L s

def sharpArena : Arena where
  signature := signature
  Law R := ∀ (L : ℝ≥0), (1 / 2 : ℝ) ≤ (L : ℝ) →
    ∃ s : AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi),
      LipschitzWith L s ∧ R.readout () L s = 2 / (2 * (L : ℝ) + 1)

theorem lower_rejected : ¬ lowerArena.Law rejected := by
  intro h
  let witness := sharpness (1 : ℝ≥0) (by norm_num)
  let s := Classical.choose witness
  have hs := (Classical.choose_spec witness).1
  have hc := h (1 : ℝ≥0) s hs
  change (2 : ℝ) / (2 * (1 : ℝ) + 1) ≤ 0 at hc
  norm_num at hc

theorem sharp_rejected : ¬ sharpArena.Law rejected := by
  intro h
  obtain ⟨s, _, hs⟩ := h (1 : ℝ≥0) (by norm_num)
  change (0 : ℝ) = 2 / (2 * (1 : ℝ) + 1) at hs
  norm_num at hs

theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  let w₁ := sharpness (1 : ℝ≥0) (by norm_num)
  let w₂ := sharpness (2 : ℝ≥0) (by norm_num)
  let s₁ := Classical.choose w₁
  let s₂ := Classical.choose w₂
  have h₁ := (Classical.choose_spec w₁).2
  have h₂ := (Classical.choose_spec w₂).2
  refine ⟨(0 : ℝ≥0), s₁, s₂, ?_⟩
  change (∫ x : AddCircle (2 * Real.pi), circle_error s₁ x ∂AddCircle.haarAddCircle) ≠
    (∫ x : AddCircle (2 * Real.pi), circle_error s₂ x ∂AddCircle.haarAddCircle)
  rw [h₁, h₂]
  norm_num

def lowerRegistration : Registration lowerArena
    (∀ (L : ℝ≥0) (s : AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi)),
      LipschitzWith L s →
        2 / (2 * (L : ℝ) + 1) ≤
          ∫ x : AddCircle (2 * Real.pi), circle_error s x ∂AddCircle.haarAddCircle) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by intro L s hs; exact lower_bound L s hs, rejected, lower_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, lower_rejected⟩
      intro j hj
      have hji : j = i := by cases j; cases i; rfl
      exact False.elim (hj hji)
    · intro i
      exact nomatch i
  dependence := actual_dependence

def sharpRegistration : Registration sharpArena
    (∀ (L : ℝ≥0), (1 / 2 : ℝ) ≤ (L : ℝ) →
      ∃ s : AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi),
        LipschitzWith L s ∧
        (∫ x : AddCircle (2 * Real.pi), circle_error s x ∂AddCircle.haarAddCircle) =
          2 / (2 * (L : ℝ) + 1)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by intro L hL; exact sharpness L hL, rejected, sharp_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, sharp_rejected⟩
      intro j hj
      have hji : j = i := by cases j; cases i; rfl
      exact False.elim (hj hji)
    · intro i
      exact nomatch i
  dependence := actual_dependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.lower_bound) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun (_ : Unit) (_ : ℝ≥0)
      (s : AddCircle.{0} (2 * Real.pi) → AddCircle.{0} (2 * Real.pi)) =>
      (∫ x : AddCircle.{0} (2 * Real.pi), circle_error s x ∂AddCircle.haarAddCircle : ℝ))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Topology") "CircleDoubleCoverLipschitzError") "lower_bound") "Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError/Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.lowerArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.lowerRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(lowerArena)⟩,
  objectArena := .source ⟨(lowerArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (lowerArena) ⟨(lowerRegistration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun (_ : Unit) (_ : ℝ≥0)
      (s : AddCircle.{0} (2 * Real.pi) → AddCircle.{0} (2 * Real.pi)) =>
      (∫ x : AddCircle.{0} (2 * Real.pi), circle_error s x ∂AddCircle.haarAddCircle : ℝ))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.lower_bound, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1.observationFact0, `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1.anchorEnumeration }


noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.sharpness) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun (_ : Unit) (_ : ℝ≥0)
      (s : AddCircle.{0} (2 * Real.pi) → AddCircle.{0} (2 * Real.pi)) =>
      (∫ x : AddCircle.{0} (2 * Real.pi), circle_error s x ∂AddCircle.haarAddCircle : ℝ))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Topology") "CircleDoubleCoverLipschitzError") "sharpness") "Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError/Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.sharpArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.sharpRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(sharpArena)⟩,
  objectArena := .source ⟨(sharpArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (sharpArena) ⟨(sharpRegistration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun (_ : Unit) (_ : ℝ≥0)
      (s : AddCircle.{0} (2 * Real.pi) → AddCircle.{0} (2 * Real.pi)) =>
      (∫ x : AddCircle.{0} (2 * Real.pi), circle_error s x ∂AddCircle.haarAddCircle : ℝ))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "arg", "body", "arg", "fn", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.sharpness, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2.observationFact0, `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2.anchorEnumeration }


#print axioms lowerRegistration
#print axioms sharpRegistration

end

end Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError


noncomputable def Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.sharpArena
noncomputable def Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Topology\",\"CircleDoubleCoverLipschitzError\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Topology\",\"CircleDoubleCoverLipschitzError\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.sharpArena
noncomputable def Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Topology\",\"CircleDoubleCoverLipschitzError\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Topology\",\"CircleDoubleCoverLipschitzError\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.lowerArena
noncomputable def Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Topology\",\"CircleDoubleCoverLipschitzError\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Topology\",\"CircleDoubleCoverLipschitzError\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.lowerArena
noncomputable def Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Topology\",\"CircleDoubleCoverLipschitzError\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Topology\",\"CircleDoubleCoverLipschitzError\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.sharpArena) (Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.sharpRegistration).actual

noncomputable def Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Topology\",\"CircleDoubleCoverLipschitzError\",\"sharpness\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Topology\",\"CircleDoubleCoverLipschitzError\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.sharpness, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.sharpRegistration).bridge

noncomputable def Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2.observation0 : (L : NNReal) →
  (hL :
      @LE.le.{0} Real Real.instLE
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
        (NNReal.toReal L)) →
    (s :
        @AddCircle.{0} Real Real.instAddCommGroup
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              Real.pi) →
          @AddCircle.{0} Real Real.instAddCommGroup
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              Real.pi)) →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.signature PUnit.unit.{1} L :=
  fun (L : NNReal)
    (hL :
      @LE.le.{0} Real Real.instLE
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
        (NNReal.toReal L))
    (s :
      @AddCircle.{0} Real Real.instAddCommGroup
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            Real.pi) →
        @AddCircle.{0} Real Real.instAddCommGroup
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            Real.pi)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.signature
    Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.actual PUnit.unit.{1} L s

noncomputable def Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Topology\",\"CircleDoubleCoverLipschitzError\",\"sharpness\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"argument\",\"body\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Topology\",\"CircleDoubleCoverLipschitzError\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.sharpness, part := .type, path := [.body, .body, .argument, .body, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2.canonicalArenaOperand)
noncomputable def Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Topology\",\"CircleDoubleCoverLipschitzError\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Topology\",\"CircleDoubleCoverLipschitzError\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Topology\",\"CircleDoubleCoverLipschitzError\",\"sharpness\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.sharpness, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.sharpRegistration).actual (Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.sharpRegistration).variation.2.choose (Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.sharpRegistration).variation.1 (Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.sharpRegistration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Topology\",\"CircleDoubleCoverLipschitzError\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Topology\",\"CircleDoubleCoverLipschitzError\",\"sharpRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.sharpRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.lowerArena) (Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.lowerRegistration).actual

noncomputable def Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Topology\",\"CircleDoubleCoverLipschitzError\",\"lower_bound\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Topology\",\"CircleDoubleCoverLipschitzError\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.lower_bound, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.lowerRegistration).bridge

noncomputable def Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1.observation0 : (L : NNReal) →
  (s :
      @AddCircle.{0} Real Real.instAddCommGroup
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            Real.pi) →
        @AddCircle.{0} Real Real.instAddCommGroup
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            Real.pi)) →
    (hs :
        @LipschitzWith.{0, 0}
          (@AddCircle.{0} Real Real.instAddCommGroup
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              Real.pi))
          (@AddCircle.{0} Real Real.instAddCommGroup
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              Real.pi))
          (@EMetricSpace.toPseudoEMetricSpace.{0}
            (@AddCircle.{0} Real Real.instAddCommGroup
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                Real.pi))
            (@MetricSpace.toEMetricSpace.{0}
              (@AddCircle.{0} Real Real.instAddCommGroup
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  Real.pi))
              (@NormedAddCommGroup.toMetricSpace.{0}
                (@AddCircle.{0} Real Real.instAddCommGroup
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    Real.pi))
                (AddCircle.instNormedAddCommGroupReal
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    Real.pi)))))
          (@EMetricSpace.toPseudoEMetricSpace.{0}
            (@AddCircle.{0} Real Real.instAddCommGroup
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                Real.pi))
            (@MetricSpace.toEMetricSpace.{0}
              (@AddCircle.{0} Real Real.instAddCommGroup
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  Real.pi))
              (@NormedAddCommGroup.toMetricSpace.{0}
                (@AddCircle.{0} Real Real.instAddCommGroup
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    Real.pi))
                (AddCircle.instNormedAddCommGroupReal
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    Real.pi)))))
          L s) →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.signature PUnit.unit.{1} L :=
  fun (L : NNReal)
    (s :
      @AddCircle.{0} Real Real.instAddCommGroup
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            Real.pi) →
        @AddCircle.{0} Real Real.instAddCommGroup
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            Real.pi))
    (hs :
      @LipschitzWith.{0, 0}
        (@AddCircle.{0} Real Real.instAddCommGroup
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            Real.pi))
        (@AddCircle.{0} Real Real.instAddCommGroup
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            Real.pi))
        (@EMetricSpace.toPseudoEMetricSpace.{0}
          (@AddCircle.{0} Real Real.instAddCommGroup
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              Real.pi))
          (@MetricSpace.toEMetricSpace.{0}
            (@AddCircle.{0} Real Real.instAddCommGroup
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                Real.pi))
            (@NormedAddCommGroup.toMetricSpace.{0}
              (@AddCircle.{0} Real Real.instAddCommGroup
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  Real.pi))
              (AddCircle.instNormedAddCommGroupReal
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  Real.pi)))))
        (@EMetricSpace.toPseudoEMetricSpace.{0}
          (@AddCircle.{0} Real Real.instAddCommGroup
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              Real.pi))
          (@MetricSpace.toEMetricSpace.{0}
            (@AddCircle.{0} Real Real.instAddCommGroup
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                Real.pi))
            (@NormedAddCommGroup.toMetricSpace.{0}
              (@AddCircle.{0} Real Real.instAddCommGroup
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  Real.pi))
              (AddCircle.instNormedAddCommGroupReal
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  Real.pi)))))
        L s) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.signature
    Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.actual PUnit.unit.{1} L s

noncomputable def Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Topology\",\"CircleDoubleCoverLipschitzError\",\"lower_bound\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Topology\",\"CircleDoubleCoverLipschitzError\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.lower_bound, part := .type, path := [.body, .body, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Topology\",\"CircleDoubleCoverLipschitzError\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Topology\",\"CircleDoubleCoverLipschitzError\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Topology\",\"CircleDoubleCoverLipschitzError\",\"lower_bound\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.lower_bound, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.lowerRegistration).actual (Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.lowerRegistration).variation.2.choose (Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.lowerRegistration).variation.1 (Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.lowerRegistration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Topology\",\"CircleDoubleCoverLipschitzError\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Topology\",\"CircleDoubleCoverLipschitzError\",\"lowerRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError, declaration := `Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError.lowerRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
