import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Dynamics.OddSquareFullInverseNorm
import Reg.Support.SingleDependentReadout

/-! Full-family source audit of the finite Euclidean amplification estimate. -/

namespace Reg.D5.S3.Quantum.Dynamics.OddSquareFullInverseNorm

open _root_.D5.S3.Quantum.Dynamics.OddSquareFullInverseNorm
open _root_.D5.S3.Quantum.Dynamics.OddSquareGreenMass
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open Lean Elab Command

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := ℕ × ℕ × ℕ
  State _ := ℕ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (Fin p.1) (Fin p.1) ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p t => (lowerBlock t p.1)⁻¹) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (t : ℕ → ℝ) (n a q : ℕ),
    (∀ i, 0 < t i) → (∀ i, t i ≤ 1) → 1 ≤ q → a + (2 * q + 1) ≤ n →
    (∀ i < 2 * q, t (2 * a + (i + (2 * q + 1))) = t (2 * a + i)) →
    ∃ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 ∧
      (q : ℝ) * (q + 1) ≤
        2 * (n : ℝ) * ‖Matrix.toEuclideanLin (R.readout () (n,a,q) t) v‖

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨v, hv, hb⟩ := h (fun _ => 1) 3 0 1 (by intro i; norm_num)
    (by intro i; norm_num) (by omega) (by omega) (by intro i hi; rfl)
  norm_num [rejected, realize] at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(1,0,1), (fun _ => 1), (fun _ => (1 / 2 : ℝ)), ?_⟩
  intro he
  have hh := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℝ => M 0 0) he
  change ((lowerBlock (fun _ => (1 : ℝ)) 1)⁻¹) 0 0 =
    ((lowerBlock (fun _ => (1 / 2 : ℝ)) 1)⁻¹) 0 0 at hh
  rw [block_inverse (fun _ => (1 : ℝ)) (by intro k; norm_num),
    block_inverse (fun _ => (1 / 2 : ℝ)) (by intro k; norm_num)] at hh
  norm_num [greenMatrix, greenEntry] at hh

def source_registration : Registration arena (type_of% @full_inverse_unit_amplification) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨full_inverse_unit_amplification, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@full_inverse_unit_amplification) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Dynamics.OddSquareFullInverseNorm.full_inverse_unit_amplification.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Dynamics.OddSquareFullInverseNorm.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p t => (lowerBlock t p.1)⁻¹) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.OddSquareFullInverseNorm
    definition := none
    coordinates := #[1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

run_cmd do
  let ty := (← getEnv).find? ``full_inverse_unit_amplification
  let some ci := ty | throwError "missing source"
  let rec visit (e : Expr) (p : Array String) : CommandElabM Unit := do
    if e.getAppFn.constName? == some ``Inv.inv then
      logInfo m!"INVERSE_SOURCE_PATH {p}"
    match e with
    | .forallE _ _ b _ => visit b (p.push "body")
    | .lam _ _ b _ => visit b (p.push "body")
    | .app f x => visit f (p.push "fn"); visit x (p.push "arg")
    | _ => pure ()
  visit ci.type #[]

end
end Reg.D5.S3.Quantum.Dynamics.OddSquareFullInverseNorm
