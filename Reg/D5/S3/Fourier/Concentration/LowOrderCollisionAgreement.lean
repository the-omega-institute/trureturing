import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Fourier.Concentration.LowOrderCollisionAgreement

/-! The difference at degree k depends on the last frequency of the integer spectrum. -/

namespace Reg.D5.S3.Fourier.Concentration.LowOrderCollisionAgreement

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.LowOrderCollisionAgreement
open _root_.D5.S3.Fourier.Concentration.FiniteSincCollisionMoment (tailCollisionMass)
open _root_.Reg.Support

noncomputable section

abbrev lastFrequency := SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization lastFrequency :=
  realize lastFrequency (fun _ _ k => (k : ℝ)) (fun e => nomatch e)

def shifted : Realization lastFrequency :=
  realize lastFrequency (fun _ _ k => (k : ℝ) + √2) (fun e => nomatch e)

abbrev lastFrequencyArena : Arena where
  signature := lastFrequency
  Law r := ∀ (k : ℕ), 2 ≤ k →
    let g : Fin 3 → ℝ := ![0, 1, r.readout () () k]
    let g' : Fin 3 → ℝ := ![0, 1, (k : ℝ) + √2]
    let w : Fin 3 → ℝ := ![1/4, 1/4, 1/2]
    (∀ p < k, ∀ t : ℝ, 0 ≤ t → t < 1 →
      tailCollisionMass g w p t = tailCollisionMass g' w p t) ∧
    (∀ t : ℝ, 0 ≤ t → t < 1 → tailCollisionMass g w k t =
      tailCollisionMass g' w k t + 2 * (k : ℝ) * (1/4 : ℝ)^(k-1) * (1/4 : ℝ)^k * (1/2)) ∧
    (∀ p : ℕ, 0 < p →
      let t := 1 / (2 * ((k : ℝ) + 3) * (p : ℝ))
      1 / (16 * (k : ℝ) * √(p : ℝ)) ≤ tailCollisionMass g w p t ∧
        tailCollisionMass g' w p t ≤ 6/(p : ℝ))

private theorem shifted_law : ¬ lastFrequencyArena.Law shifted := by
  intro law
  have h := (law 2 (by decide)).2.1 0 (by norm_num) (by norm_num)
  let g : Fin 3 → ℝ := ![0, 1, (2 : ℝ) + √2]
  let w : Fin 3 → ℝ := ![1/4, 1/4, 1/2]
  change tailCollisionMass g w 2 0 = tailCollisionMass g w 2 0 + _ at h
  norm_num at h

private theorem lastDependence : ObservationalDependence lastFrequency actual := by
  intro i
  cases i
  refine ⟨(), 0, 1, ?_⟩
  change ((0 : ℕ) : ℝ) ≠ ((1 : ℕ) : ℝ)
  norm_num

def lastEvidence :
    Registration lastFrequencyArena (type_of% @low_order_agreement_and_high_order_disparity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨low_order_agreement_and_high_order_disparity, shifted, shifted_law⟩
  sensitivity :=
    SingleDependentReadout.sensitivity lastFrequencyArena.Law actual shifted shifted_law
  dependence := lastDependence

def lastRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@low_order_agreement_and_high_order_disparity) (Realization lastFrequency) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.LowOrderCollisionAgreement.lastUnit
  realizationName := `Reg.D5.S3.Fourier.Concentration.LowOrderCollisionAgreement.lastEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨lastFrequencyArena⟩
  objectArena := .source ⟨lastFrequencyArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source lastFrequencyArena ⟨lastEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize lastFrequency (fun _ _ k => (k : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.LowOrderCollisionAgreement
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "value", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms lastRegistration

end
end Reg.D5.S3.Fourier.Concentration.LowOrderCollisionAgreement
