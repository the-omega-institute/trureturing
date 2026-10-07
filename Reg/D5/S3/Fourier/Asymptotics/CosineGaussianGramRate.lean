import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.Asymptotics.CosineGaussianGramRate
import Reg.Support.DependentFamily

open MeasureTheory
open _root_.D5.S3.Fourier.Asymptotics.CosineIntegralLattice (cosineIntegral)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate

/-- All four original real parameters and every real integration state are retained. -/
abbrev signature : Signature where
  Params := Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, ℝ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p (z : ℝ) => Real.exp (-p.2.2.1 * (z / p.2.2.2) ^ 2))
    (fun e => nomatch e)

/-- This intervention changes the Gaussian role across its complete parameter family. -/
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (2 : ℝ)) (fun e => nomatch e)

/-- Both occurrences of the Gaussian are replaced by the same readout family.
The cosine integrals, target Gram mass, bound, and hypotheses are fixed source operands. -/
def arena : Arena where
  signature := signature
  Law r := ∀ a b beta R : ℝ, 0 < a → 0 < b → 0 < beta → 0 < R →
    Integrable (fun z : ℝ =>
      cosineIntegral (a * |z|) * cosineIntegral (b * |z|) *
        (r.readout () ⟨a, b, beta, R⟩ z : ℝ)) ∧
    |(∫ z : ℝ, cosineIntegral (a * |z|) * cosineIntegral (b * |z|) *
        (r.readout () ⟨a, b, beta, R⟩ z : ℝ)) - Real.pi / max a b| ≤
      8 * (beta + 1) / (a * b * R)

theorem rejected_integrable (a b beta R : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun z : ℝ =>
      cosineIntegral (a * |z|) * cosineIntegral (b * |z|) *
        (rejected.readout () ⟨a, b, beta, R⟩ z : ℝ)) :=
  (_root_.D5.S3.Fourier.Asymptotics.CosineIntegralGram.result a b ha hb).1.mul_const 2

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbound := (h 1 1 1 100 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)).2
  change |(∫ z : ℝ, cosineIntegral (1 * |z|) * cosineIntegral (1 * |z|) * 2) -
    Real.pi / max 1 1| ≤ 8 * (1 + 1) / (1 * 1 * 100) at hbound
  rw [integral_mul_const,
    (_root_.D5.S3.Fourier.Asymptotics.CosineIntegralGram.result 1 1
      (by norm_num) (by norm_num)).2] at hbound
  norm_num at hbound
  have habs := le_abs_self (Real.pi * 2 - Real.pi)
  linarith [Real.pi_gt_three]

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j h
    exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ)⟩, (0 : ℝ), (1 : ℝ), ?_⟩
  change Real.exp (-(1 : ℝ) * (0 / 1) ^ 2) ≠
    Real.exp (-(1 : ℝ) * (1 / 1) ^ 2)
  intro h
  have hexponent := Real.exp_injective h
  norm_num at hexponent

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.result,
    rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.result) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ p (z : ℝ) => Real.exp (-p.2.2.1 * (z / p.2.2.2) ^ 2)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Fourier") "Asymptotics") "CosineGaussianGramRate") "result") "Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate/Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration,
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
    (fun _ p (z : ℝ) => Real.exp (-p.2.2.1 * (z / p.2.2.2) ^ 2)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Fourier.Asymptotics.CosineGaussianGramRate, definition := none, coordinates := #[0, 1, 2, 3], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "body", "arg"], stateBinder := 8, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Fourier.Asymptotics.CosineGaussianGramRate, declaration := `D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1.canonicalArenaFact, `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1.sourceBridgeFact, `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1.observationFact0, `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1.anchorEnumeration }


end Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate


noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.arena
noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineGaussianGramRate\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineGaussianGramRate\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.arena
noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineGaussianGramRate\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineGaussianGramRate\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.arena) (Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration).actual

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineGaussianGramRate\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineGaussianGramRate\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Fourier.Asymptotics.CosineGaussianGramRate, declaration := `D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration).bridge

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1.observation0 : (a b beta R : Real) →
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) a →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) b →
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) beta →
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) R →
          (z : Real) →
            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.signature PUnit.unit.{1}
              (@Sigma.mk.{0, 0} Real
                (fun (x : Real) => @Sigma.{0, 0} Real fun (x : Real) => @Sigma.{0, 0} Real fun (x : Real) => Real) a
                (@Sigma.mk.{0, 0} Real (fun (x : Real) => @Sigma.{0, 0} Real fun (x : Real) => Real) b
                  (@Sigma.mk.{0, 0} Real (fun (x : Real) => Real) beta R))) :=
  fun (a b beta R : Real)
    (a_1 : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) a)
    (a_2 : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) b)
    (a_3 : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) beta)
    (a_4 : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) R)
    (z : Real) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.signature
    Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Real
      (fun (x : Real) => @Sigma.{0, 0} Real fun (x : Real) => @Sigma.{0, 0} Real fun (x : Real) => Real) a
      (@Sigma.mk.{0, 0} Real (fun (x : Real) => @Sigma.{0, 0} Real fun (x : Real) => Real) b
        (@Sigma.mk.{0, 0} Real (fun (x : Real) => Real) beta R)))
    z

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineGaussianGramRate\",\"result\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"function\",\"argument\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineGaussianGramRate\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Fourier.Asymptotics.CosineGaussianGramRate, declaration := `D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.result, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .function, .argument, .function, .argument, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineGaussianGramRate\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineGaussianGramRate\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineGaussianGramRate\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Fourier.Asymptotics.CosineGaussianGramRate, declaration := `D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration).actual (Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration).variation.2.choose (Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration).variation.1 (Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineGaussianGramRate\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineGaussianGramRate\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
