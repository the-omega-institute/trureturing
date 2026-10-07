import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.Asymptotics.CosineIntegralGram
import Reg.Support.DependentFamily

open MeasureTheory
open _root_.D5.S3.Fourier.Asymptotics.CosineIntegralLattice (cosineIntegral)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram

abbrev signature : Signature where
  Params := Σ _ : ℝ, ℝ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p z => cosineIntegral (p.1 * |z|) * cosineIntegral (p.2 * |z|))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The whole original conjunction, on the whole real line and at every positive pair. -/
def arena : Arena where
  signature := signature
  Law r := ∀ a b : ℝ, 0 < a → 0 < b →
    Integrable (fun z : ℝ => r.readout () ⟨a, b⟩ z) ∧
      (∫ z : ℝ, r.readout () ⟨a, b⟩ z) = Real.pi / max a b

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := (h 1 1 zero_lt_one zero_lt_one).2
  have hp := Real.pi_pos
  norm_num [rejected, realize] at hz
  linarith

/-- A constant integrand on infinite Lebesgue volume has zero Bochner integral;
the original positive Gram mass therefore forces actual state dependence. -/
theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  by_contra h
  push Not at h
  have hc : (fun z : ℝ => cosineIntegral (1 * |z|) * cosineIntegral (1 * |z|)) =
      fun _ : ℝ => cosineIntegral (1 * |(0 : ℝ)|) * cosineIntegral (1 * |(0 : ℝ)|) := by
    funext z
    exact h ⟨1, 1⟩ z 0
  have hm := (_root_.D5.S3.Fourier.Asymptotics.CosineIntegralGram.result 1 1
    zero_lt_one zero_lt_one).2
  rw [hc] at hm
  simp [measureReal_def, Real.volume_univ] at hm
  exact Real.pi_ne_zero hm.symm

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Fourier.Asymptotics.CosineIntegralGram.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Fourier.Asymptotics.CosineIntegralGram.result) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ p z => cosineIntegral (p.1 * |z|) * cosineIntegral (p.2 * |z|))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Fourier") "Asymptotics") "CosineIntegralGram") "result") "Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram/Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration,
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
    (fun _ p z => cosineIntegral (p.1 * |z|) * cosineIntegral (p.2 * |z|))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Fourier.Asymptotics.CosineIntegralGram, definition := none, coordinates := #[0, 1], readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "body"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Fourier.Asymptotics.CosineIntegralGram, declaration := `D5.S3.Fourier.Asymptotics.CosineIntegralGram.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1.canonicalArenaFact, `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1.sourceBridgeFact, `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1.observationFact0, `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram


noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.arena
noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineIntegralGram\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineIntegralGram\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.arena
noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineIntegralGram\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineIntegralGram\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.arena Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.actual)
    Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration)

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineIntegralGram\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineIntegralGram\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Fourier.Asymptotics.CosineIntegralGram, declaration := `D5.S3.Fourier.Asymptotics.CosineIntegralGram.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.arena Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.actual)
  Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration)

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1.observation0 : (a b : Real) →
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) a →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) b →
      (z : Real) →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.signature PUnit.unit.{1}
          (@Sigma.mk.{0, 0} Real (fun (x : Real) => Real) a b) :=
  fun (a b : Real)
    (a_1 : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) a)
    (a_2 : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) b)
    (z : Real) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.signature Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.actual
    PUnit.unit.{1} (@Sigma.mk.{0, 0} Real (fun (x : Real) => Real) a b) z

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineIntegralGram\",\"result\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"function\",\"argument\",\"body\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineIntegralGram\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Fourier.Asymptotics.CosineIntegralGram, declaration := `D5.S3.Fourier.Asymptotics.CosineIntegralGram.result, part := .type, path := [.body, .body, .body, .body, .function, .argument, .function, .argument, .body], levels := [] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineIntegralGram\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineIntegralGram\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineIntegralGram\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Fourier.Asymptotics.CosineIntegralGram, declaration := `D5.S3.Fourier.Asymptotics.CosineIntegralGram.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration).actual (Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration).variation.2.choose (Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration).variation.1 (Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineIntegralGram\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineIntegralGram\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
