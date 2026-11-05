import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.Bloch.QubitBloch
import Reg.Support.DependentFamily

open _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
set_option maxHeartbeats 1000000
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open scoped Classical
noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.Bloch.QubitBloch
universe u
abbrev Vec := EuclideanSpace ℝ (Fin 3)
abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
abbrev Tuple := Fin 4 → Bool → Mat

abbrev vectorSignature : Signature where
  Params := Unit
  State _ := Vec
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Mat
  Anchor := Empty
  finiteAnchor := inferInstance

def vectorActual : Realization vectorSignature :=
  realize vectorSignature (fun _ _ a => B a) (fun e => nomatch e)
def vectorRejected : Realization vectorSignature :=
  realize vectorSignature (fun _ _ _ => 1) (fun e => nomatch e)

theorem vectorDependence : ObservationalDependence vectorSignature vectorActual := by
  intro i
  refine ⟨(), 0, !₂[0,0,1], ?_⟩
  intro h
  have hh := congrArg (fun A : Mat => A 0 0) h
  norm_num [vectorActual, realize, B_formula, Matrix.cons_val_succ, Matrix.cons_val_zero] at hh

@[reducible] def formulaArena : Arena where
  signature := vectorSignature
  Law R := ∀ a : Vec, R.readout () () a = !![(a 2 : ℂ), (a 0 : ℂ) - Complex.I * (a 1 : ℂ); (a 0 : ℂ) + Complex.I * (a 1 : ℂ), -(a 2 : ℂ)]
theorem formulaPositive : formulaArena.Law vectorActual := by
  intro a; exact B_formula a
theorem formulaNegative : ¬ formulaArena.Law vectorRejected := by
  intro h
  have hh := h 0
  have he := congrArg (fun A : Mat => A 0 0) hh
  norm_num [vectorRejected, realize, B_formula, Matrix.one_apply] at he
  change (1 : ℂ) = 0 at he
  norm_num at he

def formulaEvidence : Registration formulaArena
    (type_of% (@_root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_formula)) where
  actual := vectorActual
  bridge := Iff.rfl
  variation := ⟨formulaPositive, vectorRejected, formulaNegative⟩
  sensitivity := ⟨fun i => ⟨vectorRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, formulaNegative⟩,
    fun i => nomatch i⟩
  dependence := vectorDependence

noncomputable def formulaRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_formula)
    (type_of% (realize vectorSignature (fun _ _ a => B a) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_formula
    "Reg.D5.S3.Quantum.Measurement.Bloch.QubitBloch/Reg.D5.S3.Quantum.Measurement.Bloch.QubitBloch.formulaArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.Measurement.Bloch.QubitBloch.formulaEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨formulaArena⟩,
  objectArena := .source ⟨formulaArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source formulaArena ⟨formulaEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize vectorSignature (fun _ _ a => B a) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.Bloch.QubitBloch, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms formulaRegistration

end Reg.D5.S3.Quantum.Measurement.Bloch.QubitBloch
