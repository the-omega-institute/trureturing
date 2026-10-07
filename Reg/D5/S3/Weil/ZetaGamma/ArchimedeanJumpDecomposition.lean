import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
open MeasureTheory Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

-- Source coordinates c and t retain their order; x is the lambda-bound state.
abbrev signature : Signature where
  Params := (_ : ℝ) × ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature
  Law R := ∀ {c t : ℝ}, 0 < c →
    (∫ x in Ioi (0 : ℝ), (R.readout () ⟨c, t⟩ x : ℝ)) = c / (c ^ 2 + t ^ 2)

def actual : Realization signature :=
  realize signature
    (fun (_ : Unit) (p : (_ : ℝ) × ℝ) (x : ℝ) =>
      Real.exp (-p.1 * x) * Real.cos (p.2 * x))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun (_ : Unit) (_ : (_ : ℝ) × ℝ) (_ : ℝ) => (0 : ℝ)) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := h (c := 1) (t := 0) (by norm_num)
  norm_num [rejected, realize] at hzero

def registration : Registration arena (∀ {c t : ℝ}, 0 < c →
    (∫ x in Ioi (0 : ℝ), Real.exp (-c * x) * Real.cos (t * x)) =
      c / (c ^ 2 + t ^ 2)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.integral_exp_neg_mul_cos,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨(1 : ℝ), (0 : ℝ)⟩, (1 : ℝ), (2 : ℝ), ?_⟩
    change Real.exp (-1 * 1) * Real.cos (0 * 1) ≠
      Real.exp (-1 * 2) * Real.cos (0 * 2)
    simp only [zero_mul, mul_one, Real.cos_zero]
    intro h
    have harg := Real.exp_injective h
    norm_num at harg

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.integral_exp_neg_mul_cos) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun (_ : Unit) (p : (_ : ℝ) × ℝ) (x : ℝ) =>
      Real.exp (-p.1 * x) * Real.cos (p.2 * x))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Weil") "ZetaGamma") "ArchimedeanJumpDecomposition") "integral_exp_neg_mul_cos") "Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition/Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration,
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
    (fun (_ : Unit) (p : (_ : ℝ) × ℝ) (x : ℝ) =>
      Real.exp (-p.1 * x) * Real.cos (p.2 * x))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition, definition := none, coordinates := #[0, 1], readouts := #[{ path := #["body", "body", "body", "fn", "arg", "arg", "body"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition, declaration := `D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.integral_exp_neg_mul_cos, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition, declaration := `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition, declaration := `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition, declaration := `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition, declaration := `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1.canonicalArenaFact, `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1.sourceBridgeFact, `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1.observationFact0, `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1.anchorEnumeration }


#print axioms registration
end
end Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition


noncomputable def Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.arena
noncomputable def Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"ZetaGamma\",\"ArchimedeanJumpDecomposition\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"ZetaGamma\",\"ArchimedeanJumpDecomposition\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition, declaration := `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition, declaration := `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.arena
noncomputable def Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"ZetaGamma\",\"ArchimedeanJumpDecomposition\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"ZetaGamma\",\"ArchimedeanJumpDecomposition\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition, declaration := `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition, declaration := `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.arena) (Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration).actual

noncomputable def Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Weil\",\"ZetaGamma\",\"ArchimedeanJumpDecomposition\",\"integral_exp_neg_mul_cos\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"ZetaGamma\",\"ArchimedeanJumpDecomposition\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition, declaration := `D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.integral_exp_neg_mul_cos, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition, declaration := `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration).bridge

noncomputable def Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1.observation0 : {c t : Real} →
  (hc : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c) →
    (x : Real) →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.signature PUnit.unit.{1}
        (@Sigma.mk.{0, 0} Real (fun (x : Real) => Real) c t) :=
  fun {c t : Real}
    (hc : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c)
    (x : Real) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.signature
    Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Real (fun (x : Real) => Real) c t) x

noncomputable def Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Weil\",\"ZetaGamma\",\"ArchimedeanJumpDecomposition\",\"integral_exp_neg_mul_cos\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"function\",\"argument\",\"argument\",\"body\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"ZetaGamma\",\"ArchimedeanJumpDecomposition\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition, declaration := `D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.integral_exp_neg_mul_cos, part := .type, path := [.body, .body, .body, .function, .argument, .argument, .body], levels := [] }
  { owner := `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition, declaration := `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"ZetaGamma\",\"ArchimedeanJumpDecomposition\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"ZetaGamma\",\"ArchimedeanJumpDecomposition\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Weil\",\"ZetaGamma\",\"ArchimedeanJumpDecomposition\",\"integral_exp_neg_mul_cos\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition, declaration := `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition, declaration := `D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.integral_exp_neg_mul_cos, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration).actual (Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration).variation.2.choose (Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration).variation.1 (Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"ZetaGamma\",\"ArchimedeanJumpDecomposition\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"ZetaGamma\",\"ArchimedeanJumpDecomposition\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition, declaration := `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition, declaration := `Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
