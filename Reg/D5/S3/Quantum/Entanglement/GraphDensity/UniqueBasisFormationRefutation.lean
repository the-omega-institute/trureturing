import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.GraphDensity.UniqueBasisFormationRefutation
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the phase of a positive-weight pure-state ensemble component. -/

namespace Reg.D5.S3.Quantum.Entanglement.GraphDensity.UniqueBasisFormationRefutation

open _root_.D5.S3.Quantum.Entanglement.GraphDensity.UniqueBasisFormationRefutation
open _root_.D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds (Ensemble)
open _root_.D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace PositivePhase

/-- Observe an ensemble vector at its selected slot. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature
    (Σ p : ℕ, Σ q : ℕ, Σ v : Fin p × Fin q → ℂ, Ensemble (rankOneDensity v))
    (fun p => Fin p.2.2.2.N) (fun p => Fin p.1 × Fin p.2.1 → ℂ)

def actual : Realization signature :=
  realize signature (fun _ p i => p.2.2.2.psi i) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the normalization and positive-weight hypotheses of the phase statement. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p q : ℕ} (v : Fin p × Fin q → ℂ)
    (_hv : ∑ x, ‖v x‖ ^ 2 = 1) (e : Ensemble (rankOneDensity v))
    (i : Fin e.N) (_hi : 0 < e.weight i),
    ∃ z : ℂ, ‖z‖ = 1 ∧ R.readout () ⟨p, ⟨q, ⟨v, e⟩⟩⟩ i = z • v

private def singleton : Ensemble (rankOneDensity (fun _ : Fin 1 × Fin 1 => (1 : ℂ))) where
  N := 1
  weight := fun _ => 1
  nonneg := by intro i; norm_num
  le_one := by intro i; norm_num
  total := by simp
  psi := fun _ _ => 1
  unit := by intro i; simp
  average := by simp

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨z, hz, he⟩ := h (fun _ : Fin 1 × Fin 1 => (1 : ℂ)) (by simp)
    singleton ⟨0, by change 0 < 1; decide⟩ (by change (0 : ℝ) < 1; norm_num)
  have hz0 : z = 0 := by
    have he0 := congrFun he (0, 0)
    change (0 : ℂ) = z * 1 at he0
    simpa using he0.symm
  simp [hz0] at hz

private def oppositePhases :
    Ensemble (rankOneDensity (fun _ : Fin 1 × Fin 1 => (1 : ℂ))) where
  N := 2
  weight := fun _ => 1 / 2
  nonneg := by intro i; norm_num
  le_one := by intro i; norm_num
  total := by norm_num [Fin.sum_univ_two]
  psi := fun i _ => if i = 0 then 1 else -1
  unit := by intro i; fin_cases i <;> simp
  average := by
    ext a b
    norm_num [Fin.sum_univ_two, rankOneDensity, Matrix.vecMulVec_apply]

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, ⟨1, ⟨fun _ => 1, oppositePhases⟩⟩⟩,
    ⟨0, by change 0 < 2; decide⟩,
    ⟨1, by change 1 < 2; decide⟩, ?_⟩
  intro he
  have he0 := congrFun he (0, 0)
  change (1 : ℂ) = -1 at he0
  norm_num at he0

def source_registration : Registration arena (type_of% @positive_phase) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive_phase, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@positive_phase) (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Quantum.Entanglement.GraphDensity.UniqueBasisFormationRefutation.PositivePhase.unit
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Entanglement.GraphDensity.UniqueBasisFormationRefutation.PositivePhase
    "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ p i => p.2.2.2.psi i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.GraphDensity.UniqueBasisFormationRefutation
    definition := none
    coordinates := #[0, 1, 2, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end PositivePhase

end
end Reg.D5.S3.Quantum.Entanglement.GraphDensity.UniqueBasisFormationRefutation
