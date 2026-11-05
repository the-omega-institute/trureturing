import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Contextuality.SteeringEllipsoidFThreeThreshold
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the sharp three-setting steering threshold. -/

namespace Reg.D5.S3.Quantum.Contextuality.SteeringEllipsoidFThreeThreshold

open _root_.D5.S3.Quantum.Contextuality.SteeringEllipsoidFThreeThreshold
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction (vlen)
open _root_.D5.S3.QuantumBounds.CHSHWitness renaming TwoQubitMatrix → TwoQubit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the maximal three-setting steering value of the source matrix. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => TwoQubit) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ ρ => fThree ρ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Preserve both the universal bound and every sharpness witness. -/
abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ ρ : TwoQubit, ρ.PosSemidef → trace ρ = 1 →
      R.readout () () ρ ≤ max (Real.sqrt (3 * (1 - vlen (centreB ρ)))) 1) ∧
    (∀ t : ℝ, 0 ≤ t → t < 2 / 3 → ∃ ρ : TwoQubit,
      ρ.PosSemidef ∧ trace ρ = 1 ∧ vlen (centreB ρ) = t ∧ 1 < R.readout () () ρ)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨ρ, _, _, _, hbad⟩ := h.2 0 (by norm_num) (by norm_num)
  change (1 : ℝ) < 0 at hbad
  norm_num at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨ρ, _, _, _, hρ⟩ := result.2 0 (by norm_num) (by norm_num)
  refine ⟨(), 0, ρ, ?_⟩
  change fThree 0 ≠ fThree ρ
  have hzero : fThree 0 = 0 := by
    have hvalues : fThreeValues 0 = {0} := by
      ext r
      constructor
      · rintro ⟨α, β, _, _, hr⟩
        simpa using hr
      · rintro rfl
        refine ⟨(fun _ => ![0, 0, 1]), (fun j => Pi.single j 1), ?_, ?_, ?_⟩
        · intro j
          simpa only [abs_one] using
            _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.vlen_e3
              (1 : ℝ)
        · intro j k
          simp only [dotProduct_single, Pi.single_apply, mul_one, eq_comm]
        · simp
    rw [fThree, hvalues, csSup_singleton]
  rw [hzero]
  linarith

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Contextuality.SteeringEllipsoidFThreeThreshold.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Contextuality.SteeringEllipsoidFThreeThreshold.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Contextuality.SteeringEllipsoidFThreeThreshold.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ ρ => fThree ρ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Contextuality.SteeringEllipsoidFThreeThreshold
    definition := some {
      owner := `D5.S3.Quantum.Contextuality.SteeringEllipsoidFThreeThreshold
      name := `D5.S3.Quantum.Contextuality.SteeringEllipsoidFThreeThreshold.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "body", "fn", "arg"]
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
end Reg.D5.S3.Quantum.Contextuality.SteeringEllipsoidFThreeThreshold
