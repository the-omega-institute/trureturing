import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Decoherence.FourLevelBathObserverFourier
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Decoherence.FourLevelBathObserverFourier

open Matrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Decoherence.FourLevelBathPhysical
open _root_.D5.S3.Quantum.Decoherence.FourLevelBathObserver
open GibbsBathBandwidth (gibbsWeight)

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _ : Bath → ℝ, Σ _ : Bath → System → ℂ, Σ _ : Bath, Option System)
    (fun _ => System) (fun _ => ℝ)

/-- The actual joint Born probability for the Fourier outcome and the bath answer. -/
def actual : Realization signature :=
  realize signature (fun _ s i =>
    (Matrix.trace (orthogonalReadout (fourierColumns s.1 s.2.1 s.2.2.1) s.2.2.2 *
      fourierBranch s.1 (phaseUnitary s.2.1) i s.2.2.1)).re) (fun e => nomatch e)

def zeroReadout : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Bath → ℝ) (z : Bath → System → ℂ)
    (_hGram : (weightedColumns p z)ᴴ * weightedColumns p z = 1)
    (i : System) (k : Bath) (o : Option System),
    R.readout () ⟨p, z, k, o⟩ i = if o = some i then 1 / 4 else 0

private theorem zeroReadout_fails : ¬ arena.Law zeroReadout := by
  intro h
  obtain ⟨E, hE, _, hFeasible⟩ := feasible_fixed_bath_example 1 (by norm_num)
  obtain ⟨z, _, hGram⟩ := (fixed_bath_pinching_iff 1 E hE).1 hFeasible
  have hzero := h (gibbsWeight 1 E) z hGram 0 0 (some 0)
  change (0 : ℝ) = (if some (0 : System) = some 0 then 1 / 4 else 0) at hzero
  norm_num at hzero

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  obtain ⟨E, hE, _, hFeasible⟩ := feasible_fixed_bath_example 1 (by norm_num)
  let p := gibbsWeight 1 E
  obtain ⟨z, _, hGram⟩ := (fixed_bath_pinching_iff 1 E hE).1 hFeasible
  refine ⟨⟨p, z, 0, some 0⟩, 0, 1, ?_⟩
  change
    (Matrix.trace (orthogonalReadout (fourierColumns p z 0) (some 0) *
      fourierBranch p (phaseUnitary z) 0 0)).re ≠
    (Matrix.trace (orthogonalReadout (fourierColumns p z 0) (some 0) *
      fourierBranch p (phaseUnitary z) 1 0)).re
  rw [fourier_decoder_born p z hGram 0 0 (some 0),
    fourier_decoder_born p z hGram 1 0 (some 0)]
  have h01 : some (0 : System) ≠ some 1 := by decide
  norm_num [h01]

def source_registration : Registration arena (type_of% @fourier_decoder_born) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fourier_decoder_born, zeroReadout, zeroReadout_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual zeroReadout
    zeroReadout_fails
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@fourier_decoder_born) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Decoherence.FourLevelBathObserverFourier.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Decoherence.FourLevelBathObserverFourier.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ s i =>
    (Matrix.trace (orthogonalReadout (fourierColumns s.1 s.2.1 s.2.2.1) s.2.2.2 *
      fourierBranch s.1 (phaseUnitary s.2.1) i s.2.2.1)).re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Decoherence.FourLevelBathObserverFourier
    definition := none
    coordinates := #[0, 1, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Decoherence.FourLevelBathObserverFourier
