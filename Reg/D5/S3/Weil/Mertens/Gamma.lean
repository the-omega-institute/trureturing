import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.Gamma
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Weil.Mertens.Gamma
open MeasureTheory Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

-- The parameter telescope is empty; the state is the original integration variable.
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature
  Law R := (∫ t in Ioi (0 : ℝ), (R.readout () () t : ℝ)) = deriv Real.Gamma 1

def actual : Realization signature :=
  realize signature
    (fun (_ : Unit) (_ : Unit) (t : ℝ) => Real.log t * Real.exp (-t))
    (fun e => nomatch e)

-- Its integral is Γ'(1) + 1, so rejection needs no estimate for Γ'(1).
def rejected : Realization signature :=
  realize signature
    (fun (_ : Unit) (_ : Unit) (t : ℝ) => (deriv Real.Gamma 1 + 1) * Real.exp (-t))
    (fun e => nomatch e)

theorem rejected_integral :
    (∫ t in Ioi (0 : ℝ), (rejected.readout () () t : ℝ)) = deriv Real.Gamma 1 + 1 := by
  change (∫ t in Ioi (0 : ℝ), (deriv Real.Gamma 1 + 1) * Real.exp (-t)) = _
  rw [integral_const_mul]
  have h : (∫ t in Ioi (0 : ℝ), Real.exp (-t)) = 1 := by
    simpa using integral_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) 0
  rw [h, mul_one]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change (∫ t in Ioi (0 : ℝ), (rejected.readout () () t : ℝ)) = deriv Real.Gamma 1 at h
  rw [rejected_integral] at h
  linarith

def registration : Registration arena
    ((∫ t in Ioi (0 : ℝ), Real.log t * Real.exp (-t)) = deriv Real.Gamma 1) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.integral_log_mul_exp_neg_eq_deriv_Gamma, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (1 : ℝ), Real.exp 1, ?_⟩
    change Real.log 1 * Real.exp (-1) ≠ Real.log (Real.exp 1) * Real.exp (-Real.exp 1)
    simp only [Real.log_one, zero_mul, Real.log_exp, one_mul]
    exact ne_of_lt (Real.exp_pos _)

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.integral_log_mul_exp_neg_eq_deriv_Gamma) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun (_ : Unit) (_ : Unit) (t : ℝ) => Real.log t * Real.exp (-t))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "integral_log_mul_exp_neg_eq_deriv_Gamma") "Reg.D5.S3.Weil.Mertens.Gamma/Reg.D5.S3.Weil.Mertens.Gamma.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Weil.Mertens.Gamma.registration,
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
    (fun (_ : Unit) (_ : Unit) (t : ℝ) => Real.log t * Real.exp (-t))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Weil.Mertens.Gamma, definition := none, coordinates := #[], readouts := #[{ path := #["fn", "arg", "arg", "body"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Weil.Mertens.Gamma, declaration := `integral_log_mul_exp_neg_eq_deriv_Gamma, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Weil.Mertens.Gamma, declaration := `Reg.D5.S3.Weil.Mertens.Gamma.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Weil.Mertens.Gamma, declaration := `Reg.D5.S3.Weil.Mertens.Gamma.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Weil.Mertens.Gamma, declaration := `Reg.D5.S3.Weil.Mertens.Gamma.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Weil.Mertens.Gamma, declaration := `Reg.D5.S3.Weil.Mertens.Gamma.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Weil.Mertens.Gamma.registration_1.canonicalArenaFact, `Reg.D5.S3.Weil.Mertens.Gamma.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Weil.Mertens.Gamma.registration_1.sourceBridgeFact, `Reg.D5.S3.Weil.Mertens.Gamma.registration_1.observationFact0, `Reg.D5.S3.Weil.Mertens.Gamma.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Weil.Mertens.Gamma.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Weil.Mertens.Gamma.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Weil.Mertens.Gamma.registration_1.anchorEnumeration }


#print axioms registration
end
end Reg.D5.S3.Weil.Mertens.Gamma


noncomputable def Reg.D5.S3.Weil.Mertens.Gamma.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Weil.Mertens.Gamma.arena
noncomputable def Reg.D5.S3.Weil.Mertens.Gamma.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"Mertens\",\"Gamma\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"Mertens\",\"Gamma\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Weil.Mertens.Gamma, declaration := `Reg.D5.S3.Weil.Mertens.Gamma.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.Mertens.Gamma, declaration := `Reg.D5.S3.Weil.Mertens.Gamma.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Weil.Mertens.Gamma.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Weil.Mertens.Gamma.arena
noncomputable def Reg.D5.S3.Weil.Mertens.Gamma.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"Mertens\",\"Gamma\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"Mertens\",\"Gamma\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Weil.Mertens.Gamma, declaration := `Reg.D5.S3.Weil.Mertens.Gamma.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.Mertens.Gamma, declaration := `Reg.D5.S3.Weil.Mertens.Gamma.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Weil.Mertens.Gamma.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} Reg.D5.S3.Weil.Mertens.Gamma.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Weil.Mertens.Gamma.arena
    (@Eq.{1} Real
      (@MeasureTheory.integral.{0, 0} Real Real Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
        (@MeasureTheory.Measure.restrict.{0} Real
          (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
          (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)
          (@Set.Ioi.{0} Real Real.instPreorder
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
        fun (t : Real) =>
        @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Real.log t)
          (Real.exp (@Neg.neg.{0} Real Real.instNeg t)))
      (@deriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
        Real.instAddCommGroup
        (@Semiring.toModule.{0} Real
          (@DivisionSemiring.toSemiring.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real
              (@Field.toSemifield.{0} Real
                (@NormedField.toField.{0} Real
                  (@NontriviallyNormedField.toNormedField.{0} Real
                    (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)))))))
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        Real.Gamma (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
    Reg.D5.S3.Weil.Mertens.Gamma.registration)

noncomputable def Reg.D5.S3.Weil.Mertens.Gamma.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"integral_log_mul_exp_neg_eq_deriv_Gamma\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"Mertens\",\"Gamma\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Weil.Mertens.Gamma, declaration := `integral_log_mul_exp_neg_eq_deriv_Gamma, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Weil.Mertens.Gamma, declaration := `Reg.D5.S3.Weil.Mertens.Gamma.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Weil.Mertens.Gamma.arena
  (@Eq.{1} Real
    (@MeasureTheory.integral.{0, 0} Real Real Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
      (@MeasureTheory.Measure.restrict.{0} Real
        (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
        (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)
        (@Set.Ioi.{0} Real Real.instPreorder
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
      fun (t : Real) =>
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Real.log t)
        (Real.exp (@Neg.neg.{0} Real Real.instNeg t)))
    (@deriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.instAddCommGroup
      (@Semiring.toModule.{0} Real
        (@DivisionSemiring.toSemiring.{0} Real
          (@Semifield.toDivisionSemiring.{0} Real
            (@Field.toSemifield.{0} Real
              (@NormedField.toField.{0} Real
                (@NontriviallyNormedField.toNormedField.{0} Real
                  (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)))))))
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      Real.Gamma (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  Reg.D5.S3.Weil.Mertens.Gamma.registration)

noncomputable def Reg.D5.S3.Weil.Mertens.Gamma.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Weil.Mertens.Gamma.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Weil.Mertens.Gamma.registration_1.observation0 : (t : Real) →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
    Reg.D5.S3.Weil.Mertens.Gamma.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (t : Real) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Weil.Mertens.Gamma.signature Reg.D5.S3.Weil.Mertens.Gamma.actual PUnit.unit.{1} PUnit.unit.{1} t

noncomputable def Reg.D5.S3.Weil.Mertens.Gamma.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"integral_log_mul_exp_neg_eq_deriv_Gamma\"],\"part\":\"type\",\"path\":[\"function\",\"argument\",\"argument\",\"body\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"Mertens\",\"Gamma\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Weil.Mertens.Gamma, declaration := `integral_log_mul_exp_neg_eq_deriv_Gamma, part := .type, path := [.function, .argument, .argument, .body], levels := [] }
  { owner := `Reg.D5.S3.Weil.Mertens.Gamma, declaration := `Reg.D5.S3.Weil.Mertens.Gamma.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Weil.Mertens.Gamma.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Weil.Mertens.Gamma.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Weil.Mertens.Gamma.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"Mertens\",\"Gamma\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Weil.Mertens.Gamma.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"Mertens\",\"Gamma\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"integral_log_mul_exp_neg_eq_deriv_Gamma\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Weil.Mertens.Gamma, declaration := `Reg.D5.S3.Weil.Mertens.Gamma.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Weil.Mertens.Gamma, declaration := `integral_log_mul_exp_neg_eq_deriv_Gamma, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Weil.Mertens.Gamma.registration).actual (Reg.D5.S3.Weil.Mertens.Gamma.registration).variation.2.choose (Reg.D5.S3.Weil.Mertens.Gamma.registration).variation.1 (Reg.D5.S3.Weil.Mertens.Gamma.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Weil.Mertens.Gamma.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"Mertens\",\"Gamma\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"Mertens\",\"Gamma\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Weil.Mertens.Gamma, declaration := `Reg.D5.S3.Weil.Mertens.Gamma.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.Mertens.Gamma, declaration := `Reg.D5.S3.Weil.Mertens.Gamma.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
