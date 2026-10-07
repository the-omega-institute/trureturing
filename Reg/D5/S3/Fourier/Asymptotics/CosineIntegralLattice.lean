import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.Asymptotics.CosineIntegralGram
import Reg.Support.DependentFamily

open MeasureTheory Filter
open _root_.D5.S3.Fourier.Asymptotics.CosineIntegralLattice (cosineIntegral)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice

abbrev signature : Signature where
  Params := ℝ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ z n => cosineIntegral (z * (n + 1)) ^ 2) (fun e => nomatch e)

/-- Every rejected fiber is summable. Its weighted mass is z², so no single
constant works at every positive spacing. -/
def rejected : Realization signature :=
  realize signature (fun _ z n => if n = 0 then z else 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 0 < z →
    Summable (fun n : ℕ => r.readout () z n) ∧
      z * (∑' n : ℕ, r.readout () z n) ≤ C

theorem rejected_summable (z : ℝ) : Summable (fun n : ℕ => rejected.readout () z n) := by
  exact (hasSum_ite_eq (0 : ℕ) z).summable

theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨C, hC, h⟩
  have hb := (h (C + 1) (by linarith)).2
  simp [rejected, realize] at hb
  nlinarith [sq_nonneg C]

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  by_contra h
  push Not at h
  obtain ⟨C, hC, hs⟩ := _root_.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.result
  have hzero (z : ℝ) (hz : 0 < z) : cosineIntegral z ^ 2 = 0 := by
    have he : (fun n : ℕ => cosineIntegral (z * (n + 1)) ^ 2) =
        fun _ : ℕ => cosineIntegral z ^ 2 := by
      funext n
      simpa [actual, realize] using h z n 0
    have ht := (hs z hz).1
    rw [he] at ht
    exact (summable_const_iff (cosineIntegral z ^ 2)).mp ht
  have he : (fun z : ℝ => cosineIntegral (1 * |z|) * cosineIntegral (1 * |z|)) =ᵐ[volume]
      fun _ => (0 : ℝ) := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with z hz
    have hz0 : z ≠ 0 := by simpa using hz
    simpa [pow_two] using hzero |z| (abs_pos.mpr hz0)
  have hm := (_root_.D5.S3.Fourier.Asymptotics.CosineIntegralGram.result 1 1
    zero_lt_one zero_lt_one).2
  rw [integral_congr_ae he] at hm
  simp at hm
  exact Real.pi_ne_zero hm.symm

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.result) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ z n => cosineIntegral (z * (n + 1)) ^ 2) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Fourier") "Asymptotics") "CosineIntegralLattice") "result") "Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice/Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration,
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
    (fun _ z n => cosineIntegral (z * (n + 1)) ^ 2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Fourier.Asymptotics.CosineIntegralLattice, definition := none, coordinates := #[1], readouts := #[{ path := #["arg", "body", "arg", "body", "body", "fn", "arg", "fn", "arg", "body"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Fourier.Asymptotics.CosineIntegralLattice, declaration := `D5.S3.Fourier.Asymptotics.CosineIntegralLattice.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1.canonicalArenaFact, `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1.sourceBridgeFact, `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1.observationFact0, `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice


noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.arena
noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineIntegralLattice\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineIntegralLattice\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.arena
noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineIntegralLattice\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineIntegralLattice\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.arena) (Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration).actual

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineIntegralLattice\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineIntegralLattice\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Fourier.Asymptotics.CosineIntegralLattice, declaration := `D5.S3.Fourier.Asymptotics.CosineIntegralLattice.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration).bridge

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1.observation0 : (C z : Real) →
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) z →
    (n : Nat) →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.signature PUnit.unit.{1} z :=
  fun (C z : Real)
    (a : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) z)
    (n : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.signature
    Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.actual PUnit.unit.{1} z n

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineIntegralLattice\",\"result\"],\"part\":\"type\",\"path\":[\"argument\",\"body\",\"argument\",\"body\",\"body\",\"function\",\"argument\",\"function\",\"argument\",\"body\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineIntegralLattice\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Fourier.Asymptotics.CosineIntegralLattice, declaration := `D5.S3.Fourier.Asymptotics.CosineIntegralLattice.result, part := .type, path := [.argument, .body, .argument, .body, .body, .function, .argument, .function, .argument, .body], levels := [] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineIntegralLattice\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineIntegralLattice\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineIntegralLattice\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Fourier.Asymptotics.CosineIntegralLattice, declaration := `D5.S3.Fourier.Asymptotics.CosineIntegralLattice.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration).actual (Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration).variation.2.choose (Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration).variation.1 (Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineIntegralLattice\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineIntegralLattice\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
