import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation
import Reg.Support.DependentFamily

namespace Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation
open _root_.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State L := ZMod L → Fin 3
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ L := ZMod L → Fin 3
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => 1) (fun e => nomatch e)

/-- The complete negated claim; only the configuration in the hypothesis `∃ i, x i = 0` is
replaced. -/
abbrev arena : Arena where
  signature := signature
  Law O := ¬ ∀ (L : ℕ) [NeZero L] (x : ZMod L → Fin 3), (∃ i, O.readout () L x i = 0) →
    (rho x ∈ Set.Ico (0 : ℚ) (2 / 3) → (step ruleG)^[L] ((step ruleF)^[L] x) = fun _ => 0) ∧
    (rho x ∈ Set.Ioo (2 / 3 : ℚ) (3 / 4) → (step ruleG)^[L] ((step ruleF)^[L] x) = fun _ => 1) ∧
    (rho x ∈ Set.Ioo (3 / 4 : ℚ) 1 → (step ruleG)^[L] ((step ruleF)^[L] x) = fun _ => 2)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h
  intro L _ x hx
  obtain ⟨i, hi⟩ := hx
  change (1 : Fin 3) = 0 at hi
  exact absurd hi (by decide)

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, fun _ => 0, fun _ => 1, fun h => ?_⟩
  have := congrFun h 0
  change (0 : Fin 3) = 1 at this
  exact absurd this (by decide)

def registration : Registration arena (¬ claim) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "StatisticalMechanics") "CellularAutomata") "TernaryDensityClassificationRefutation") "result") "Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation/Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation, definition := some { owner := `D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation, name := `D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.claim, path := #["arg"] }, coordinates := #[0], readouts := #[{ path := #["arg", "body", "body", "body", "domain", "arg", "body", "fn", "arg", "fn"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation, declaration := `D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation, declaration := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation, declaration := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation, declaration := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation, declaration := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] },
    { owner := `D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation, declaration := `D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.claim, part := .value, path := [], levels := [] }], facts := [`Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1.canonicalArenaFact, `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1.sourceBridgeFact, `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1.observationFact0, `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1.anchorEnumeration }


#print axioms registration

end
end Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation


noncomputable def Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.arena
noncomputable def Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"CellularAutomata\",\"TernaryDensityClassificationRefutation\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"CellularAutomata\",\"TernaryDensityClassificationRefutation\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation, declaration := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation, declaration := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.arena
noncomputable def Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"CellularAutomata\",\"TernaryDensityClassificationRefutation\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"CellularAutomata\",\"TernaryDensityClassificationRefutation\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation, declaration := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation, declaration := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.arena) (Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration).actual

noncomputable def Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"StatisticalMechanics\",\"CellularAutomata\",\"TernaryDensityClassificationRefutation\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"CellularAutomata\",\"TernaryDensityClassificationRefutation\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation, declaration := `D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation, declaration := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration).bridge

noncomputable def Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1.observation0 : (L : Nat) →
  [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) L] →
    (x : ZMod L → Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) →
      (i : ZMod L) →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.signature
          PUnit.unit.{1} L :=
  fun (L : Nat) [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) L]
    (x : ZMod L → Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (i : ZMod L) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.signature
    Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.actual PUnit.unit.{1} L x

noncomputable def Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"StatisticalMechanics\",\"CellularAutomata\",\"TernaryDensityClassificationRefutation\",\"claim\"],\"part\":\"value\",\"path\":[\"body\",\"body\",\"body\",\"domain\",\"argument\",\"body\",\"function\",\"argument\",\"function\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"CellularAutomata\",\"TernaryDensityClassificationRefutation\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation, declaration := `D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.claim, part := .value, path := [.body, .body, .body, .domain, .argument, .body, .function, .argument, .function], levels := [] }
  { owner := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation, declaration := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"CellularAutomata\",\"TernaryDensityClassificationRefutation\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"CellularAutomata\",\"TernaryDensityClassificationRefutation\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"StatisticalMechanics\",\"CellularAutomata\",\"TernaryDensityClassificationRefutation\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation, declaration := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation, declaration := `D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration).actual (Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration).variation.2.choose (Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration).variation.1 (Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"CellularAutomata\",\"TernaryDensityClassificationRefutation\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"CellularAutomata\",\"TernaryDensityClassificationRefutation\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation, declaration := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation, declaration := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
