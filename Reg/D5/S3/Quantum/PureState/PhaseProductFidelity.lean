import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.PureState.PhaseProductFidelity
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.PureState.PhaseProductFidelity

open _root_.D5.S3.Quantum.PureState.PhaseProductFidelity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

/-- Dimension, ensemble size and the classical probabilities are held fixed when
the phase vectors of the ensemble vary. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature
    (Σ _ : ℕ, Σ m : ℕ, Fin m → ℝ)
    (fun p => Fin p.2.1 → Fin p.1 → ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p v => mixedDeficit cube p.2.2 v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ}, 0 < n → ∀ C : ℝ,
    (∀ (m : ℕ) (p : Fin m → ℝ) (v : Fin m → Fin n → ℂ),
      (∀ i, 0 ≤ p i) → ∑ i, p i = 1 → (∀ i k, ‖v i k‖ = 1) →
      R.readout () ⟨n,m,p⟩ v ≤ C * mixedDeficit simplex p v) ↔
      ((n : ℝ) + 1)^2 / 4 ≤ C

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have H := (h (n := 1) (by decide) 1).mpr (by norm_num)
  have bad := H 1 (fun _ => 1) (fun _ _ => 1) (by intro; norm_num)
    (by simp) (by intros; simp)
  norm_num [rejected, realize, mixedDeficit, simplex, Fin.sum_univ_one,
    Complex.normSq_apply] at bad

private theorem varies : ObservationalDependence signature actual := by
  intro _
  refine ⟨⟨1, 2, fun _ => 1/2⟩, fun _ _ => 1,
    ![(fun _ => (1 : ℂ)), (fun _ => (-1 : ℂ))], ?_⟩
  change mixedDeficit cube (fun _ : Fin 2 => 1/2) (fun _ (_ : Fin 1) => 1) ≠
    mixedDeficit cube (fun _ : Fin 2 => 1/2)
      ![(fun _ : Fin 1 => (1 : ℂ)), (fun _ => (-1 : ℂ))]
  norm_num [mixedDeficit, cube, Fin.sum_univ_two, Fin.prod_univ_one]

def evidence : Registration arena (type_of% @mixed_coefficient_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨mixed_coefficient_iff, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := varies

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@mixed_coefficient_iff) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.PureState.PhaseProductFidelity.mixed_coefficient_iff.audit
  realizationName := `Reg.D5.S3.Quantum.PureState.PhaseProductFidelity.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p v => mixedDeficit cube p.2.2 v)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.PureState.PhaseProductFidelity
    definition := none
    coordinates := #[0,3,4]
    readouts := #[{
      path := #["body","body","body","fn","arg","body","body","body","body","body","body","fn","arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms evidence
#print axioms registration

end
end Reg.D5.S3.Quantum.PureState.PhaseProductFidelity
