import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitSeptitMaximumPurity

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitSeptitMaximumPurity
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitSeptitMaximumPurity
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritPerturbationAttainment
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped ComplexOrder
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Matrix (Fin 4 × Fin 7) (Fin 4 × Fin 7) ℂ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ rho => (rho * rho).trace.re) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law O :=
    (∀ rho : Matrix (Fin 4 × Fin 7) (Fin 4 × Fin 7) ℂ,
      (rho.PosSemidef ∧ rho.trace = 1) → APPT rho →
        O.readout () () rho ≤ (1 / 25 : ℝ)) ∧
    (sSup {p : ℝ | ∃ rho : Matrix (Fin 4 × Fin 7) (Fin 4 × Fin 7) ℂ,
      (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧
        (rho * rho).trace.re = p} = (1 / 25 : ℝ)) ∧
    ∃ rho : Matrix (Fin 4 × Fin 7) (Fin 4 × Fin 7) ℂ,
      rho = diagonal (fun ij : Fin 4 × Fin 7 =>
        if ij = (0, 0) then (3 / 30 : ℂ) else (1 / 30 : ℂ)) ∧
      (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧
        (rho * rho).trace.re = (1 / 25 : ℝ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨rho, _, hd, ha, _⟩ := result.2.2
  have hb := h.1 rho hd ha
  change (1 : ℝ) ≤ 1 / 25 at hb
  norm_num at hb
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize, Matrix.trace_one, Fintype.card_prod]
def familyRegistration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := actual_dependence

def resultRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitSeptitMaximumPurity.result)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitSeptitMaximumPurity.result.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitSeptitMaximumPurity.familyRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ rho => (rho * rho).trace.re) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitSeptitMaximumPurity,
    definition := some {
      owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitSeptitMaximumPurity,
      name := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitSeptitMaximumPurity.claim,
      path := #[] },
    coordinates := #[],
    readouts := #[{
      path := #["fn", "arg", "body", "body", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms familyRegistration
end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitSeptitMaximumPurity
