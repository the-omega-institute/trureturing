import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit
open Filter LeanInformationAudit Matrix Topology
open scoped BigOperators ComplexOrder Matrix Matrix.Norms.L2Operator MatrixOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit

universe u

@[reducible] def survivalSignature : Signature where
  Params := Σ d : ℕ, Matrix (Fin d) (Fin d) ℂ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (Fin p.1) (Fin p.1) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization survivalSignature :=
  realize survivalSignature
    (fun _ p N => (p.2ᴴ) ^ N * p.2 ^ N)
    (fun e => nomatch e)

def rejected : Realization survivalSignature :=
  realize survivalSignature
    (fun _ p N => (p.2ᴴ) ^ N * p.2 ^ N + 1)
    (fun e => nomatch e)

def arena : Arena where
  signature := survivalSignature
  Law R := ∀ {d : ℕ} {ι : Type u} [Fintype ι]
    (Q : Matrix (Fin d) (Fin d) ℂ)
    (L : ι → Matrix (Fin d) (Fin d) ℂ)
    (_hcomp : Qᴴ * Q + ∑ x, (L x)ᴴ * L x = 1),
    Tendsto (fun N => R.readout () ⟨d, Q⟩ N) atTop
        (𝓝 (darkProjection Q L)) ∧
      ∀ ρ : Matrix (Fin d) (Fin d) ℂ,
        Tendsto (fun N => (ρ * ((Qᴴ) ^ N * Q ^ N)).trace) atTop
          (𝓝 (ρ * darkProjection Q L).trace)

theorem actual_law : arena.{u}.Law actual := by
  intro d ι _ Q L hcomp
  exact finite_detection_survival_limit Q L hcomp

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let Q : Matrix (Fin 1) (Fin 1) ℂ := 1
  let L : ULift.{u} Empty → Matrix (Fin 1) (Fin 1) ℂ := fun e => nomatch e.down
  have hcomp : Qᴴ * Q + ∑ x, (L x)ᴴ * L x = 1 := by
    simp [Q]
  have hbad := (h (ι := ULift.{u} Empty) Q L hcomp).1
  have hgood := (finite_detection_survival_limit Q L hcomp).1
  have hshift : Tendsto (fun N => (Qᴴ) ^ N * Q ^ N + 1) atTop
      (𝓝 (darkProjection Q L + 1)) := hgood.add tendsto_const_nhds
  have heq : darkProjection Q L = darkProjection Q L + 1 := by
    apply tendsto_nhds_unique hbad
    simpa only [rejected, realize, survivalSignature] using hshift
  have hentry := congrFun (congrFun heq 0) 0
  simp at hentry

theorem sensitivity_proof : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    cases i
    cases j
    exact (hji rfl).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence survivalSignature actual := by
  intro i
  cases i
  refine ⟨⟨1, 0⟩, 0, 1, ?_⟩
  intro h
  have hentry := congrFun (congrFun h 0) 0
  norm_num [actual, realize, survivalSignature, Matrix.mul_apply,
    dotProduct, Fin.sum_univ_one] at hentry

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.finite_detection_survival_limit.{u_1}) (type_of% (realize.{0, 0, 0, 0, 0} survivalSignature
    (fun _ p N => (p.2ᴴ) ^ N * p.2 ^ N)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Measurement") "FiniteDetectionSurvivalLimit") "finite_detection_survival_limit") "Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit/Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1})⟩,
  objectArena := .source ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} survivalSignature
    (fun _ p N => (p.2ᴴ) ^ N * p.2 ^ N)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, definition := none, coordinates := #[0, 3], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn", "arg", "body"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.finite_detection_survival_limit, part := .type, path := [], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1] }], facts := [`Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1.observationFact0, `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1.anchorEnumeration }


#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof

namespace DarkBlock

abbrev signature := survivalSignature

abbrev actual := Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.actual

abbrev rejected := Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.rejected

def arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} {ι : Type u} [Fintype ι]
    (Q : Matrix (Fin d) (Fin d) ℂ)
    (L : ι → Matrix (Fin d) (Fin d) ℂ)
    (_hcomp : Qᴴ * Q + ∑ x, (L x)ᴴ * L x = 1) (_hd : d ≠ 0),
    ∃ (g : ℝ) (c : ℕ → ℝ),
      0 < g ∧ g ≤ 1 ∧
      (∀ N, 0 ≤ c N) ∧
      (∀ N, c N ≤ 1) ∧
      (∀ N, c (N + d) ≤ (1 - g) * c N) ∧
      (∀ N, darkProjection Q L ≤ R.readout () ⟨d, Q⟩ N) ∧
      (∀ N, R.readout () ⟨d, Q⟩ N - darkProjection Q L =
        (1 - darkProjection Q L) * R.readout () ⟨d, Q⟩ N *
          (1 - darkProjection Q L)) ∧
      0 ≤ 1 - darkProjection Q L ∧
      (∀ N, R.readout () ⟨d, Q⟩ N - darkProjection Q L ≤
        c N • (1 - darkProjection Q L)) ∧
      (∀ N, ‖R.readout () ⟨d, Q⟩ N - darkProjection Q L‖ ≤ c N) ∧
      1 - g = c d ∧
      R.readout () ⟨d, Q⟩ d - darkProjection Q L ≤
        (1 - g) • (1 - darkProjection Q L) ∧
      (∀ n k, c (n + k * d) ≤ (1 - g) ^ k) ∧
      (∀ N, c N ≤ (1 - g) ^ (N / d)) ∧
      (∀ n k, R.readout () ⟨d, Q⟩ (n + k * d) - darkProjection Q L ≤
        (1 - g) ^ k • (1 - darkProjection Q L)) ∧
      (∀ N, R.readout () ⟨d, Q⟩ N - darkProjection Q L ≤
        (1 - g) ^ (N / d) • (1 - darkProjection Q L))

theorem actual_law : arena.{u}.Law actual := by
  intro d ι _ Q L hcomp hd
  exact dark_block_contraction Q L hcomp hd

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let Q : Matrix (Fin 1) (Fin 1) ℂ := 1
  let L : ULift.{u} Empty → Matrix (Fin 1) (Fin 1) ℂ := fun e => nomatch e.down
  have hcomp : Qᴴ * Q + ∑ x, (L x)ᴴ * L x = 1 := by simp [Q]
  obtain ⟨_g, _c, _hg, _hg1, _hc0, _hc1, _hcstep, _hP, hfactor, _hPc,
    _hcontract, _hnorm, _hgap, _hblock, _hciter, _hcquotient, _hiterated, _hquotient⟩ :=
    h Q L hcomp one_ne_zero
  have hD : darkSpace Q L = ⊤ := by
    apply top_unique
    intro v _
    simp only [darkSpace, Submodule.mem_iInf, LinearMap.mem_ker]
    intro _ x
    exact nomatch x.down
  have hP : darkProjection Q L = 1 := by
    simp only [darkProjection, hD, Submodule.starProjection_top', map_one]
  have hbad := hfactor 0
  simp only [rejected,
    Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.rejected,
    realize, signature, Q, pow_zero, mul_one, hP] at hbad
  have hentry := congrFun (congrFun hbad 0) 0
  norm_num [Matrix.ofNat_apply, Matrix.one_apply] at hentry

theorem sensitivity_proof : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    cases i
    cases j
    exact (hji rfl).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual :=
  Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.dependence_proof

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_2.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.dark_block_contraction.{u_1}) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ p N => (p.2ᴴ) ^ N * p.2 ^ N)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Measurement") "FiniteDetectionSurvivalLimit") "dark_block_contraction") "Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit/Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1})⟩,
  objectArena := .source ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ p N => (p.2ᴴ) ^ N * p.2 ^ N)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, definition := none, coordinates := #[0, 3], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "body", "arg"], stateBinder := 9, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.dark_block_contraction, part := .type, path := [], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1] }], facts := [`Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2.canonicalArenaFact, `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2.sourceBridgeFact, `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2.observationFact0, `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2.anchorEnumeration }


#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end DarkBlock

end Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit


noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1.canonicalArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.arena.{u_1}
noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1.canonicalArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionSurvivalLimit\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionSurvivalLimit\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1.canonicalObjectArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.arena.{u_1}
noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1.canonicalObjectArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionSurvivalLimit\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionSurvivalLimit\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2.canonicalArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.arena.{u_1}
noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2.canonicalArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionSurvivalLimit\",\"DarkBlock\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionSurvivalLimit\",\"DarkBlock\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2.canonicalObjectArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.arena.{u_1}
noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2.canonicalObjectArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionSurvivalLimit\",\"DarkBlock\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionSurvivalLimit\",\"DarkBlock\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1.sourceLaw.{u_1} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.arena.{u_1}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.arena.{u_1}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.arena.{u_1}
      Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.actual)
    Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration.{u_1})

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1.sourceBridgeFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionSurvivalLimit\",\"finite_detection_survival_limit\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionSurvivalLimit\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.finite_detection_survival_limit, part := .type, path := [], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.arena.{u_1}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.arena.{u_1}
    Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.actual)
  Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration.{u_1})

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1.observation0.{u_1} : {d : Nat} →
  {ι : Type u_1} →
    [inst : Fintype.{u_1} ι] →
      (Q : Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) →
        (L : ι → Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) →
          (hcomp :
              @Eq.{1} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                (@HAdd.hAdd.{0, 0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                  (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                  (@instHAdd.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                    (@Matrix.add.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAdd))
                  (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                    (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                    (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin d) (Fin d) (Fin d) Complex
                      (Fin.fintype d) Complex.instMul Complex.instAddCommMonoid)
                    (@Matrix.conjTranspose.{0, 0, 0} (Fin d) (Fin d) Complex
                      (@InvolutiveStar.toStar.{0} Complex
                        (@StarAddMonoid.toInvolutiveStar.{0} Complex
                          (@AddCommMonoid.toAddMonoid.{0} Complex
                            (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                                    Complex.instNonUnitalCommRing)))))
                          (@StarRing.toStarAddMonoid.{0} Complex
                            (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                                  Complex.instNonUnitalCommRing)))
                            Complex.instStarRing)))
                      Q)
                    Q)
                  (@Finset.sum.{u_1, 0} ι (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                    (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                    (@Finset.univ.{u_1} ι inst) fun (x : ι) =>
                    @HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                      (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                      (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin d) (Fin d) (Fin d) Complex
                        (Fin.fintype d) Complex.instMul Complex.instAddCommMonoid)
                      (@Matrix.conjTranspose.{0, 0, 0} (Fin d) (Fin d) Complex
                        (@InvolutiveStar.toStar.{0} Complex
                          (@StarAddMonoid.toInvolutiveStar.{0} Complex
                            (@AddCommMonoid.toAddMonoid.{0} Complex
                              (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                                (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                                      Complex.instNonUnitalCommRing)))))
                            (@StarRing.toStarAddMonoid.{0} Complex
                              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                                    Complex.instNonUnitalCommRing)))
                              Complex.instStarRing)))
                        (L x))
                      (L x)))
                (@OfNat.ofNat.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (nat_lit 1)
                  (@One.toOfNat1.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                    (@Matrix.one.{0, 0} (Fin d) Complex (instDecidableEqFin d) Complex.instZero Complex.instOne)))) →
            (N : Nat) →
              D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.survivalSignature PUnit.unit.{1}
                (@Sigma.mk.{0, 0} Nat (fun (d : Nat) => Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) d Q) :=
  fun {d : Nat} {ι : Type u_1} [Fintype.{u_1} ι] (Q : Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
    (L : ι → Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
    (hcomp :
      @Eq.{1} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
        (@HAdd.hAdd.{0, 0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
          (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
          (@instHAdd.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
            (@Matrix.add.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAdd))
          (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
            (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin d) (Fin d) (Fin d) Complex (Fin.fintype d)
              Complex.instMul Complex.instAddCommMonoid)
            (@Matrix.conjTranspose.{0, 0, 0} (Fin d) (Fin d) Complex
              (@InvolutiveStar.toStar.{0} Complex
                (@StarAddMonoid.toInvolutiveStar.{0} Complex
                  (@AddCommMonoid.toAddMonoid.{0} Complex
                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))))
                  (@StarRing.toStarAddMonoid.{0} Complex
                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))
                    Complex.instStarRing)))
              Q)
            Q)
          (@Finset.sum.{u_1, 0} ι (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
            (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
            (@Finset.univ.{u_1} ι inst) fun (x : ι) =>
            @HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
              (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin d) (Fin d) (Fin d) Complex
                (Fin.fintype d) Complex.instMul Complex.instAddCommMonoid)
              (@Matrix.conjTranspose.{0, 0, 0} (Fin d) (Fin d) Complex
                (@InvolutiveStar.toStar.{0} Complex
                  (@StarAddMonoid.toInvolutiveStar.{0} Complex
                    (@AddCommMonoid.toAddMonoid.{0} Complex
                      (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                        (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                              Complex.instNonUnitalCommRing)))))
                    (@StarRing.toStarAddMonoid.{0} Complex
                      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))
                      Complex.instStarRing)))
                (L x))
              (L x)))
        (@OfNat.ofNat.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (nat_lit 1)
          (@One.toOfNat1.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
            (@Matrix.one.{0, 0} (Fin d) Complex (instDecidableEqFin d) Complex.instZero Complex.instOne))))
    (N : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.survivalSignature
    Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat (fun (d : Nat) => Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) d Q) N

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1.observationFact0.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionSurvivalLimit\",\"finite_detection_survival_limit\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"function\",\"function\",\"argument\",\"body\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionSurvivalLimit\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.finite_detection_survival_limit, part := .type, path := [.body, .body, .body, .body, .body, .body, .function, .argument, .function, .function, .argument, .body], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1.varyingLawInput.{u_1} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1.canonicalArenaOperand.{u_1})
noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1.varyingLaw.{u_1}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionSurvivalLimit\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1.statementExclusion.{u_1} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionSurvivalLimit\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionSurvivalLimit\",\"finite_detection_survival_limit\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1)] }
  statementLocation := { owner := `D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.finite_detection_survival_limit, part := .type, path := [], levels := [(.param `u_1)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration.{u_1}).actual (Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration.{u_1}).variation.2.choose (Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration.{u_1}).variation.1 (Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration.{u_1}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionSurvivalLimit\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionSurvivalLimit\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2.sourceLaw.{u_1} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.arena.{u_1}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.arena.{u_1}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.arena.{u_1}
      Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.actual)
    Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration.{u_1})

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2.sourceBridgeFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionSurvivalLimit\",\"dark_block_contraction\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionSurvivalLimit\",\"DarkBlock\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.dark_block_contraction, part := .type, path := [], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2.sourceLaw, part := .value, path := [], levels := [(.param `u_1)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.arena.{u_1}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.arena.{u_1}
    Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.actual)
  Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration.{u_1})

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2.observation0.{u_1} : {d : Nat} →
  {ι : Type u_1} →
    [inst : Fintype.{u_1} ι] →
      (Q : Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) →
        (L : ι → Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) →
          (hcomp :
              @Eq.{1} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                (@HAdd.hAdd.{0, 0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                  (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                  (@instHAdd.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                    (@Matrix.add.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAdd))
                  (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                    (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                    (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin d) (Fin d) (Fin d) Complex
                      (Fin.fintype d) Complex.instMul Complex.instAddCommMonoid)
                    (@Matrix.conjTranspose.{0, 0, 0} (Fin d) (Fin d) Complex
                      (@InvolutiveStar.toStar.{0} Complex
                        (@StarAddMonoid.toInvolutiveStar.{0} Complex
                          (@AddCommMonoid.toAddMonoid.{0} Complex
                            (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                                    Complex.instNonUnitalCommRing)))))
                          (@StarRing.toStarAddMonoid.{0} Complex
                            (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                                  Complex.instNonUnitalCommRing)))
                            Complex.instStarRing)))
                      Q)
                    Q)
                  (@Finset.sum.{u_1, 0} ι (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                    (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
                    (@Finset.univ.{u_1} ι inst) fun (x : ι) =>
                    @HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                      (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                      (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin d) (Fin d) (Fin d) Complex
                        (Fin.fintype d) Complex.instMul Complex.instAddCommMonoid)
                      (@Matrix.conjTranspose.{0, 0, 0} (Fin d) (Fin d) Complex
                        (@InvolutiveStar.toStar.{0} Complex
                          (@StarAddMonoid.toInvolutiveStar.{0} Complex
                            (@AddCommMonoid.toAddMonoid.{0} Complex
                              (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                                (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                                      Complex.instNonUnitalCommRing)))))
                            (@StarRing.toStarAddMonoid.{0} Complex
                              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                                    Complex.instNonUnitalCommRing)))
                              Complex.instStarRing)))
                        (L x))
                      (L x)))
                (@OfNat.ofNat.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (nat_lit 1)
                  (@One.toOfNat1.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
                    (@Matrix.one.{0, 0} (Fin d) Complex (instDecidableEqFin d) Complex.instZero Complex.instOne)))) →
            (hd : @Ne.{1} Nat d (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
              (g : Real) →
                (c : Nat → Real) →
                  (N : Nat) →
                    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                      Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.survivalSignature PUnit.unit.{1}
                      (@Sigma.mk.{0, 0} Nat (fun (d : Nat) => Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) d Q) :=
  fun {d : Nat} {ι : Type u_1} [Fintype.{u_1} ι] (Q : Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
    (L : ι → Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
    (hcomp :
      @Eq.{1} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
        (@HAdd.hAdd.{0, 0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
          (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
          (@instHAdd.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
            (@Matrix.add.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAdd))
          (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
            (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin d) (Fin d) (Fin d) Complex (Fin.fintype d)
              Complex.instMul Complex.instAddCommMonoid)
            (@Matrix.conjTranspose.{0, 0, 0} (Fin d) (Fin d) Complex
              (@InvolutiveStar.toStar.{0} Complex
                (@StarAddMonoid.toInvolutiveStar.{0} Complex
                  (@AddCommMonoid.toAddMonoid.{0} Complex
                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))))
                  (@StarRing.toStarAddMonoid.{0} Complex
                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))
                    Complex.instStarRing)))
              Q)
            Q)
          (@Finset.sum.{u_1, 0} ι (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
            (@Matrix.addCommMonoid.{0, 0, 0} (Fin d) (Fin d) Complex Complex.instAddCommMonoid)
            (@Finset.univ.{u_1} ι inst) fun (x : ι) =>
            @HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
              (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin d) (Fin d) (Fin d) Complex
                (Fin.fintype d) Complex.instMul Complex.instAddCommMonoid)
              (@Matrix.conjTranspose.{0, 0, 0} (Fin d) (Fin d) Complex
                (@InvolutiveStar.toStar.{0} Complex
                  (@StarAddMonoid.toInvolutiveStar.{0} Complex
                    (@AddCommMonoid.toAddMonoid.{0} Complex
                      (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                        (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                              Complex.instNonUnitalCommRing)))))
                    (@StarRing.toStarAddMonoid.{0} Complex
                      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))
                      Complex.instStarRing)))
                (L x))
              (L x)))
        (@OfNat.ofNat.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) (nat_lit 1)
          (@One.toOfNat1.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
            (@Matrix.one.{0, 0} (Fin d) Complex (instDecidableEqFin d) Complex.instZero Complex.instOne))))
    (hd : @Ne.{1} Nat d (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (g : Real) (c : Nat → Real)
    (N : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.survivalSignature
    Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat (fun (d : Nat) => Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) d Q) N

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2.observationFact0.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionSurvivalLimit\",\"dark_block_contraction\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"function\",\"argument\",\"body\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionSurvivalLimit\",\"DarkBlock\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.dark_block_contraction, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .argument, .body, .argument, .body, .argument, .argument, .argument, .argument, .argument, .function, .argument, .body, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2.observation0, part := .value, path := [], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2.varyingLawInput.{u_1} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2.canonicalArenaOperand.{u_1})
noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2.varyingLaw.{u_1}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionSurvivalLimit\",\"DarkBlock\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2.statementExclusion.{u_1} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionSurvivalLimit\",\"DarkBlock\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionSurvivalLimit\",\"dark_block_contraction\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2.varyingLaw, part := .value, path := [], levels := [(.param `u_1)] }
  statementLocation := { owner := `D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.dark_block_contraction, part := .type, path := [], levels := [(.param `u_1)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration.{u_1}).actual (Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration.{u_1}).variation.2.choose (Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration.{u_1}).variation.1 (Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration.{u_1}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionSurvivalLimit\",\"DarkBlock\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"FiniteDetectionSurvivalLimit\",\"DarkBlock\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit, declaration := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.DarkBlock.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))
