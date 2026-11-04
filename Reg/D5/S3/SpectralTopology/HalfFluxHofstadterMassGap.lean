import LeanInformationAuditInterface.Contract.Registration
import D5.S3.SpectralTopology.HalfFluxHofstadterMassGap
import Reg.Support.SingleDependentReadout

/-! Source-bound registrations of the Bloch Hermiticity and uniform mass gap. -/

namespace Reg.D5.S3.SpectralTopology.HalfFluxHofstadterMassGap

open _root_.D5.S3.SpectralTopology.HalfFluxHofstadterMassGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Hermiticity

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℝ)
    (fun _ => ℝ) (fun _ => Matrix (Fin 4) (Fin 4) ℂ)

def actual : Realization signature :=
  realize signature (fun _ p m => bloch p.1 p.2 m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Matrix.single 0 1 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ k₁ k₂ m : ℝ, (R.readout () ⟨k₁, k₂⟩ m).IsHermitian

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 1) (h 0 0 0)
  norm_num [rejected, realize, Matrix.conjTranspose_apply, Matrix.single] at he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, 0⟩, 0, 1, ?_⟩
  intro he
  have hd := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0) he
  norm_num [actual, realize, bloch] at hd

def source_registration : Registration arena (type_of% @bloch_isHermitian) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨bloch_isHermitian, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@bloch_isHermitian) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.SpectralTopology.HalfFluxHofstadterMassGap.Hermiticity.unit
  realizationName :=
    `Reg.D5.S3.SpectralTopology.HalfFluxHofstadterMassGap.Hermiticity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p m => bloch p.1 p.2 m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.SpectralTopology.HalfFluxHofstadterMassGap
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms registration

end Hermiticity

namespace MassGap

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℝ)
    (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p m => band p.1 p.2 m 3) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fermiEnergy) (fun e => nomatch e)

/-- Only the universal upper-band observation varies; every other clause is retained. -/
abbrev arena : Arena where
  signature := signature
  Law R :=
    band (Real.pi / 4) (Real.pi / 4) 0 3 = fermiEnergy ∧
      ∀ m : ℝ, -2 ≤ m → m ≤ 2 → m ≠ 0 →
        ∃ δ : ℝ, 0 < δ ∧ ∀ k₁ k₂ : ℝ,
          fermiEnergy + δ ≤ R.readout () ⟨k₁, k₂⟩ m ∧
            band k₁ k₂ m 2 ≤ fermiEnergy - δ

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨δ, hδ, hgap⟩ := h.2 1 (by norm_num) (by norm_num) (by norm_num)
  have hbad := (hgap 0 0).1
  change fermiEnergy + δ ≤ fermiEnergy at hbad
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨Real.pi / 4, Real.pi / 4⟩, 0, 1, ?_⟩
  intro he
  change band (Real.pi / 4) (Real.pi / 4) 0 3 =
    band (Real.pi / 4) (Real.pi / 4) 1 3 at he
  obtain ⟨δ, hδ, hgap⟩ := result.2 1 (by norm_num) (by norm_num) (by norm_num)
  have hbad := (hgap (Real.pi / 4) (Real.pi / 4)).1
  rw [← he, result.1] at hbad
  linarith

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@result) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.SpectralTopology.HalfFluxHofstadterMassGap.MassGap.unit
  realizationName :=
    `Reg.D5.S3.SpectralTopology.HalfFluxHofstadterMassGap.MassGap.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p m => band p.1 p.2 m 3) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.SpectralTopology.HalfFluxHofstadterMassGap
    definition := some {
      owner := `D5.S3.SpectralTopology.HalfFluxHofstadterMassGap
      name := `D5.S3.SpectralTopology.HalfFluxHofstadterMassGap.claim
      path := #[] }
    coordinates := #[5, 6]
    readouts := #[{
      path := #["arg", "body", "body", "body", "body", "arg", "body", "arg",
        "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms registration

end MassGap

end
end Reg.D5.S3.SpectralTopology.HalfFluxHofstadterMassGap
