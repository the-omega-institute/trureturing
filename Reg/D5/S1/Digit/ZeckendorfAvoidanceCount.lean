import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import Reg.Support.SourceSelection
import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Digit.ZeckendorfAvoidanceCount
import Reg.Support.DependentFamily

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S1.Digit.ZeckendorfAvoidanceCount
open D5.S1.Digit.ZeckendorfContextualReplacement

namespace Reg.D5.S1.Digit.ZeckendorfAvoidanceCount
noncomputable section
open Classical

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ H => ((legalWords H 0).filter (fun w => decide (¬ B1 <:+: w))).length)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ H : ℕ, (R.readout () () H : ℝ) ≤
    Real.goldenRatio ^ (H + 1) *
      (1 - (Real.goldenRatio ^ (14 : ℕ))⁻¹) ^ (H / 14)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 2) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0
  have hphi : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  simp [rejected,realize] at hh
  linarith

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨uniform_avoidance_count,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(),0,1,?_⟩
    have avoid (w : List (Fin 2)) (hl : w.length ≤ 1) : ¬ B1 <:+: w := by
      intro h
      have hh := h.length_le
      norm_num [B1] at hh
      omega
    norm_num [actual,realize,legalWords,avoid [] (by simp),
      avoid [0] (by simp),avoid [1] (by simp)]

def selection : _root_.Reg.Support.SourceSelection := {
  owner := `D5.S1.Digit.ZeckendorfAvoidanceCount
  coordinates := #[]
  readouts := #[{path := #["body","fn","arg","arg"], stateOperand := some #["arg","arg","fn","arg"]}] }

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Digit.ZeckendorfAvoidanceCount.uniform_avoidance_count) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ _ H => ((legalWords H 0).filter (fun w => decide (¬ B1 <:+: w))).length)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Digit") "ZeckendorfAvoidanceCount") "uniform_avoidance_count") "Reg.D5.S1.Digit.ZeckendorfAvoidanceCount/Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ _ H => ((legalWords H 0).filter (fun w => decide (¬ B1 <:+: w))).length)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Digit.ZeckendorfAvoidanceCount, definition := none, coordinates := #[], readouts := #[{ path := #["body", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg", "arg", "fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Digit.ZeckendorfAvoidanceCount, declaration := `D5.S1.Digit.ZeckendorfAvoidanceCount.uniform_avoidance_count, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount, declaration := `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount, declaration := `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount, declaration := `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount, declaration := `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1.canonicalArenaFact, `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1.canonicalObjectArenaFact, `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1.sourceBridgeFact, `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1.observationFact0, `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1.anchorEnumeration }


#print axioms registration
end
end Reg.D5.S1.Digit.ZeckendorfAvoidanceCount


noncomputable def Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.arena
noncomputable def Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfAvoidanceCount\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfAvoidanceCount\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount, declaration := `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount, declaration := `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.arena
noncomputable def Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfAvoidanceCount\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfAvoidanceCount\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount, declaration := `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount, declaration := `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.arena) (Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration).actual

noncomputable def Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Digit\",\"ZeckendorfAvoidanceCount\",\"uniform_avoidance_count\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfAvoidanceCount\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Digit.ZeckendorfAvoidanceCount, declaration := `D5.S1.Digit.ZeckendorfAvoidanceCount.uniform_avoidance_count, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount, declaration := `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration).bridge

noncomputable def Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1.observation0 : (H : Nat) →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
    Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (H : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.signature Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.actual PUnit.unit.{1}
    PUnit.unit.{1} H

noncomputable def Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Digit\",\"ZeckendorfAvoidanceCount\",\"uniform_avoidance_count\"],\"part\":\"type\",\"path\":[\"body\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfAvoidanceCount\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Digit.ZeckendorfAvoidanceCount, declaration := `D5.S1.Digit.ZeckendorfAvoidanceCount.uniform_avoidance_count, part := .type, path := [.body, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount, declaration := `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfAvoidanceCount\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfAvoidanceCount\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Digit\",\"ZeckendorfAvoidanceCount\",\"uniform_avoidance_count\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount, declaration := `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Digit.ZeckendorfAvoidanceCount, declaration := `D5.S1.Digit.ZeckendorfAvoidanceCount.uniform_avoidance_count, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration).actual (Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration).variation.2.choose (Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration).variation.1 (Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfAvoidanceCount\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfAvoidanceCount\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount, declaration := `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount, declaration := `Reg.D5.S1.Digit.ZeckendorfAvoidanceCount.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
