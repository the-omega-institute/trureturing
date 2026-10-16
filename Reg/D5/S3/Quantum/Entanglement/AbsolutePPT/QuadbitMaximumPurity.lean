import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity

open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritPerturbationAttainment
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature
    (fun _ _ (rho : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) =>
      (rho * rho).trace.re)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

/-- The whole original closed claim is retained. Only the purity observation in
the universal upper bound is varied; the supremum and explicit attainment
clauses remain part of the law. -/
abbrev arena : Arena where
  signature := signature
  Law O :=
    (∀ rho : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ,
      (rho.PosSemidef ∧ rho.trace = 1) → APPT rho →
        O.readout () () rho ≤ (2 / 27 : ℝ)) ∧
    (sSup {p : ℝ | ∃ rho : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ,
      (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧
        (rho * rho).trace.re = p} = (2 / 27 : ℝ)) ∧
    ∃ rho : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ,
      rho = diagonal (fun ij : Fin 4 × Fin 4 =>
        if ij = (0, 0) then (1 / 6 : ℂ) else (1 / 18 : ℂ)) ∧
      (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧
        (rho * rho).trace.re = (2 / 27 : ℝ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨rho, _hdiag, hdensity, happt, _hpurity⟩ := result.2.2
  have hle := h.1 rho hdensity happt
  change (1 : ℝ) ≤ (2 / 27 : ℝ) at hle
  norm_num at hle

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ), 1, ?_⟩
  norm_num [actual, realize, Matrix.trace_one, Fintype.card_prod]

def registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity.result)
      (type_of% (realize.{0,0,0,0,0} signature
        (fun _ _ (rho : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) =>
          (rho * rho).trace.re)
        (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity.result.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature
    (fun _ _ (rho : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) =>
      (rho * rho).trace.re)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity,
    definition := some {
      owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity,
      name := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity.claim,
      path := #[] },
    coordinates := #[],
    readouts := #[{
      path := #["fn", "arg", "body", "body", "body", "fn", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[
    { name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity
