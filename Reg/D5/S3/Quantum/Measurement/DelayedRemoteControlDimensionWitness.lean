import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness
import Reg.Support.SingleDependentReadout

/-! Source-bound audits of the remote-control witness and unit-coordinate identity. -/

namespace Reg.D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness
open _root_.D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the data-measurement vector in its unit-norm condition. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Fin 2 → ℂ) (fun _ => Fin 2 → ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ b => b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The preparation probabilities and witness bound retain every original parameter. -/
abbrev arena : Arena where
  signature := signature
  Law R :=
    ∀ d : Fin 2 → ℂ, ‖(WithLp.toLp 2 d : EuclideanSpace ℂ (Fin 2))‖ = 1 →
      ∃ β δ γ₀ γ₁ : ℝ, ∃ b : Fin 2 → ℂ,
        ‖(WithLp.toLp 2 (R.readout () () b) : EuclideanSpace ℂ (Fin 2))‖ = 1 ∧
          (∀ x : Fin 4, 0 < prepProb d β δ b x) ∧ 4 < S d β δ γ₀ γ₁ b

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hd : ‖(WithLp.toLp 2 ![(1 : ℂ), 0] : EuclideanSpace ℂ (Fin 2))‖ = 1 := by
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  obtain ⟨β, δ, γ₀, γ₁, b, hb, _⟩ := h ![1, 0] hd
  change ‖(WithLp.toLp 2 (0 : Fin 2 → ℂ) : EuclideanSpace ℂ (Fin 2))‖ = 1 at hb
  simp at hb

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : Fin 2 → ℂ), (1 : Fin 2 → ℂ), ?_⟩
  intro h
  have he := congrFun h (0 : Fin 2)
  change (0 : ℂ) = 1 at he
  exact zero_ne_one he

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.result)
      (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    `Reg.D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness "unit",
  realizationName :=
    `Reg.D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.source_registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨source_registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ b => b) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness,
    definition := some {
      owner := `D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness,
      name := `D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.claim,
      path := #[] },
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "arg", "body",
        "arg", "body", "arg", "body", "fn", "arg", "fn", "arg", "arg", "arg"],
      stateBinder := 6,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms signature
#print axioms actual
#print axioms rejected
#print axioms arena
#print axioms rejected_law
#print axioms dependence
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness

namespace Reg.D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.UnitCoordinates
open _root_.D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

/-- Observe the squared coordinate norm appearing in the unit-vector identity. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 2 → ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ d => Complex.normSq (d 0) + Complex.normSq (d 1))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ d : Fin 2 → ℂ,
    ‖(WithLp.toLp 2 d : EuclideanSpace ℂ (Fin 2))‖ = 1 → R.readout () () d = 1

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hd : ‖(WithLp.toLp 2 ![(1 : ℂ), 0] : EuclideanSpace ℂ (Fin 2))‖ = 1 := by
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have hbad := h ![1, 0] hd
  change (0 : ℝ) = 1 at hbad
  exact zero_ne_one hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, ![1, 0], ?_⟩
  change Complex.normSq ((0 : Fin 2 → ℂ) 0) + Complex.normSq ((0 : Fin 2 → ℂ) 1) ≠
    Complex.normSq ((![1, 0] : Fin 2 → ℂ) 0) +
      Complex.normSq ((![1, 0] : Fin 2 → ℂ) 1)
  norm_num

def source_registration : Registration arena (type_of% @unit_coordinates) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨unit_coordinates, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@unit_coordinates) (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    `Reg.D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.UnitCoordinates "unit"
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.UnitCoordinates
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
    (realize signature (fun _ _ d => Complex.normSq (d 0) + Complex.normSq (d 1))
      (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.UnitCoordinates
