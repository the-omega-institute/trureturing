import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.Asymptotics.WeightedCumulativeRemainder
import Reg.Support.UniverseSingleReadout

/-! Dependence of the weighted tail estimate on the norm of the remainder. -/

namespace Reg.D5.S3.Fourier.Asymptotics.WeightedCumulativeRemainder

open Finset Set
open scoped Interval
open LeanInformationAudit
open _root_.D5.S3.Fourier.Asymptotics.WeightedCumulativeRemainder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support

noncomputable section
universe u

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} (s : Finset ι) (height : ι → ℝ) (amplitude : ι → ℂ)
    {X T c A B : ℝ} (_ : 1 ≤ X) (_ : X ≤ T) (_ : 1 ≤ c) (_ : 0 ≤ A) (_ : 0 ≤ B)
    (_ : ∀ i ∈ s, height i ∈ Ioc X T) (w w' : ℝ → ℝ)
    (_ : ∀ t ∈ [[X, T]], HasDerivAt w (w' t) t)
    (_ : ContinuousOn w' [[X, T]])
    (_ : ∀ t ∈ [[X, T]], 0 ≤ w t) (_ : ∀ t ∈ [[X, T]], w' t ≤ 0)
    (_ : ∀ t ∈ [[X, T]], w t ≤ 1 / t)
    (baseline : ℂ) (G g : ℝ → ℂ)
    (_ : ∀ t ∈ [[X, T]], HasDerivAt G (g t) t) (_ : ContinuousOn g [[X, T]])
    (_ : ∀ t ∈ [[X, T]],
      ‖baseline + (∑ i ∈ s, if height i ≤ t then amplitude i else 0) - G t‖ ≤
        A * Real.log (c * t) ^ 2 + B * Real.log (2 * t)),
    let size := R.readout () ()
    size ((∑ i ∈ s, (w (height i) : ℂ) * amplitude i) -
      ∫ t in X..T, (w t : ℂ) * g t) ≤
      (2 * A * (Real.log (c * X) ^ 2 + Real.log (c * X) + 1) +
        B * (2 * Real.log (2 * X) + 1)) / X

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have h0 := h (ι := PUnit.{u+1}) ∅ (fun _ => 0) (fun _ => 0)
    (X := 1) (T := 1) (c := 1) (A := 0) (B := 0)
    le_rfl le_rfl le_rfl le_rfl le_rfl (by simp)
    (fun _ => 0) (fun _ => 0) (fun t _ => hasDerivAt_const t 0) continuousOn_const
    (by simp) (by simp) (by simp) 0 (fun _ => 0) (fun _ => 0)
    (fun t _ => hasDerivAt_const t 0) continuousOn_const (by simp)
  norm_num [rejected, realize] at h0

def family : Registration arena.{u} (type_of% @weighted_tail_error_le.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weighted_tail_error_le.{u}, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change ‖(0 : ℂ)‖ ≠ ‖(1 : ℂ)‖
    norm_num

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@weighted_tail_error_le.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Fourier.Asymptotics.WeightedCumulativeRemainder.weighted_tail_error_le.__information_unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.WeightedCumulativeRemainder.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Asymptotics.WeightedCumulativeRemainder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.Asymptotics.WeightedCumulativeRemainder
