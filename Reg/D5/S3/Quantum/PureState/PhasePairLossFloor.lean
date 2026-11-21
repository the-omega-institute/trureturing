import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.PureState.PhasePairLossFloor
import Reg.Support.SingleDependentReadout

/-! The cube deficit as an observation on ensembles with fixed weights. -/

namespace Reg.D5.S3.Quantum.PureState.PhasePairLossFloor

open _root_.D5.S3.Quantum.PureState.PhaseProductFidelity
open _root_.D5.S3.Quantum.PureState.PhasePairLossFloor
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

/-- The ensemble size and weights are fixed while the two-coordinate rows vary. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature
    (Σ m : ℕ, Fin m → ℝ) (fun p => Fin p.1 → Fin 2 → ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p v => mixedDeficit cube p.2 v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law S := ∀ (R C : ℝ), 0 ≤ R →
    ((∀ (m : ℕ) (p : Fin m → ℝ) (v : Fin m → Fin 2 → ℂ),
        (∀ i j, 0 ≤ p i * p j) → (∀ i, p i ≠ 0 → ∀ k, ‖v i k‖ ≤ R) →
        C * mixedDeficit simplex p v ≤ S.readout () ⟨m, p⟩ v) ↔
      (if R ≤ 1 then C ≤ 9 * (3 + R^2) / (16 * (2 + R^2)) else C = 3 / 4))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have test := (h 0 (3 / 4) (by norm_num)).mpr (by norm_num)
  have bad := test 1 (fun _ => 1) (fun _ _ => 0) (by intros; norm_num)
    (by intros; simp)
  norm_num [rejected, realize, mixedDeficit, simplex, Fin.sum_univ_one] at bad

private theorem varies : ObservationalDependence signature actual := by
  intro _
  refine ⟨⟨1, fun _ => 1⟩, fun _ _ => 0, fun _ _ => 1, ?_⟩
  change mixedDeficit cube (fun _ : Fin 1 => 1) (fun _ (_ : Fin 2) => 0) ≠
    mixedDeficit cube (fun _ : Fin 1 => 1) (fun _ (_ : Fin 2) => 1)
  norm_num [mixedDeficit, cube, Fin.sum_univ_one, Fin.prod_univ_two]

def evidence : Registration arena (type_of% @mixed_lower_coefficient_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨mixed_lower_coefficient_iff, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := varies

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@mixed_lower_coefficient_iff) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.PureState.PhasePairLossFloor.mixed_lower_coefficient_iff.audit
  realizationName := `Reg.D5.S3.Quantum.PureState.PhasePairLossFloor.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p v => mixedDeficit cube p.2 v)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.PureState.PhasePairLossFloor
    definition := none
    coordinates := #[3, 4]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms evidence
#print axioms registration

end
end Reg.D5.S3.Quantum.PureState.PhasePairLossFloor
