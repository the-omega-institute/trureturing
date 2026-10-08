import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Thermal.PositiveOneModeWilliamson
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Thermal.PositiveOneModeWilliamson
open Matrix LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Quantum.Thermal.PositiveOneModeWilliamson

@[reducible] def signature : Signature where
  Params := Unit
  State _ := Matrix (Fin 2) (Fin 2) ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Matrix (Fin 2) (Fin 2) ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ M => M.transpose * physicalJ2 * M) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (a b c : ℝ),
    (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℝ).PosDef →
      ∃ (ω : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ),
        0 < ω ∧
        R.readout () () M = physicalJ2 ∧
        M.transpose * !![a, b; b, c] * M =
            ω • (1 : Matrix (Fin 2) (Fin 2) ℝ)

theorem actual_law : arena.Law actual := by
  intro a b c hS
  change ∃ (ω : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ),
    0 < ω ∧ M.transpose * physicalJ2 * M = physicalJ2 ∧
    M.transpose * !![a, b; b, c] * M =
      ω • (1 : Matrix (Fin 2) (Fin 2) ℝ)
  exact positive_one_mode_williamson a b c hS

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs : (!![(1 : ℝ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
    convert (Matrix.PosDef.one : (1 : Matrix (Fin 2) (Fin 2) ℝ).PosDef) using 1
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num
  obtain ⟨ω, M, _, hsymp, _⟩ := h 1 0 1 hs
  have hentry := congrFun (congrFun hsymp (0 : Fin 2)) (1 : Fin 2)
  change (0 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 1 at hentry
  norm_num at hentry

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    cases i
    cases j
    exact (hji rfl).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), (0 : Matrix (Fin 2) (Fin 2) ℝ),
    (1 : Matrix (Fin 2) (Fin 2) ℝ), ?_⟩
  intro h
  have he := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
  simp [actual, realize, signature, physicalJ2] at he

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Thermal.PositiveOneModeWilliamson.positive_one_mode_williamson) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ _ M => M.transpose * physicalJ2 * M) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Thermal") "PositiveOneModeWilliamson") "positive_one_mode_williamson") "Reg.D5.S3.Quantum.Thermal.PositiveOneModeWilliamson/Reg.D5.S3.Quantum.Thermal.PositiveOneModeWilliamson.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Thermal.PositiveOneModeWilliamson.registration,
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
    (fun _ _ M => M.transpose * physicalJ2 * M) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Thermal.PositiveOneModeWilliamson, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "fn", "arg", "fn", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end Reg.D5.S3.Quantum.Thermal.PositiveOneModeWilliamson
