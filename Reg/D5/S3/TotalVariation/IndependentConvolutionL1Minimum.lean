import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.TotalVariation.IndependentConvolutionL1Minimum
import Reg.Support.DependentFamily

open _root_.D5.S3.TotalVariation.IndependentConvolutionL1Minimum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable
namespace Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum

abbrev signature : Signature where
  Params := ℕ
  State n := Fin n → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Fin n → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => 0) (fun e => nomatch e)

/-- Preserve every source hypothesis and vary the first factor only at the objective readout. -/
def arena : Arena where
  signature := signature
  Law r := ∀ (n : ℕ) (_hn : 3 ≤ n),
    IsLeast {v : ℝ | ∃ p q : Fin n → ℝ,
      p ∈ stdSimplex ℝ (Fin n) ∧ q ∈ stdSimplex ℝ (Fin n) ∧
      fullL1 n (r.readout () n p) q = v} (1 / (2 * n - 1 : ℕ))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨p, q, hp, hq, hv⟩ := (h 3 (by norm_num)).1
  norm_num [rejected, realize, fullL1, ordinaryConvolution,
    Finset.sum_range_succ] at hv

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨3, (Pi.single (0 : Fin 3) 1 : Fin 3 → ℝ),
    (Pi.single (1 : Fin 3) 1 : Fin 3 → ℝ), ?_⟩
  intro h
  have he := congrFun h (0 : Fin 3)
  norm_num [actual, realize, Pi.single_apply] at he

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ p => p) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "TotalVariation") "IndependentConvolutionL1Minimum") "result") "Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum/Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ p => p) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.TotalVariation.IndependentConvolutionL1Minimum, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "fn", "arg", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "fn", "arg", "fn", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.TotalVariation.IndependentConvolutionL1Minimum, declaration := `D5.S3.TotalVariation.IndependentConvolutionL1Minimum.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum, declaration := `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum, declaration := `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum, declaration := `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum, declaration := `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1.canonicalArenaFact, `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1.sourceBridgeFact, `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1.observationFact0, `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1.anchorEnumeration }


#print axioms registration
end Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum


noncomputable def Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.arena
noncomputable def Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"TotalVariation\",\"IndependentConvolutionL1Minimum\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"TotalVariation\",\"IndependentConvolutionL1Minimum\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum, declaration := `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum, declaration := `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.arena
noncomputable def Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"TotalVariation\",\"IndependentConvolutionL1Minimum\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"TotalVariation\",\"IndependentConvolutionL1Minimum\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum, declaration := `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum, declaration := `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.arena
      Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.actual)
    Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration)

noncomputable def Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"TotalVariation\",\"IndependentConvolutionL1Minimum\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"TotalVariation\",\"IndependentConvolutionL1Minimum\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.TotalVariation.IndependentConvolutionL1Minimum, declaration := `D5.S3.TotalVariation.IndependentConvolutionL1Minimum.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum, declaration := `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.arena
    Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.actual)
  Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration)

noncomputable def Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1.observation0 : (n : Nat) →
  (hn : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) n) →
    (v : Real) →
      (p q : Fin n → Real) →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.signature PUnit.unit.{1} n :=
  fun (n : Nat) (hn : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) n) (v : Real)
    (p q : Fin n → Real) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.signature
    Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.actual PUnit.unit.{1} n p

noncomputable def Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"TotalVariation\",\"IndependentConvolutionL1Minimum\",\"result\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"function\",\"argument\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"argument\",\"function\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"TotalVariation\",\"IndependentConvolutionL1Minimum\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.TotalVariation.IndependentConvolutionL1Minimum, declaration := `D5.S3.TotalVariation.IndependentConvolutionL1Minimum.result, part := .type, path := [.body, .body, .function, .argument, .argument, .body, .argument, .body, .argument, .body, .argument, .argument, .function, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum, declaration := `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"TotalVariation\",\"IndependentConvolutionL1Minimum\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"TotalVariation\",\"IndependentConvolutionL1Minimum\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"TotalVariation\",\"IndependentConvolutionL1Minimum\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum, declaration := `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.TotalVariation.IndependentConvolutionL1Minimum, declaration := `D5.S3.TotalVariation.IndependentConvolutionL1Minimum.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration).actual (Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration).variation.2.choose (Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration).variation.1 (Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"TotalVariation\",\"IndependentConvolutionL1Minimum\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"TotalVariation\",\"IndependentConvolutionL1Minimum\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum, declaration := `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum, declaration := `Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
