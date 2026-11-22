import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Oscillation.SparseOrdinateMass
import Reg.Support.SingleDependentReadout

/-! The squared logarithm in the mass normalization varies with the real cutoff. -/

namespace Reg.D5.S3.Analytic.Oscillation.SparseOrdinateMass

open _root_.D5.S3.Analytic.Oscillation.SparseOrdinateMass
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)
open LeanInformationAudit Filter
open scoped Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

abbrev normalizerSignature : Signature := signature Unit (fun _ => ℝ) (fun _ => ℝ)

def normalizer : Realization normalizerSignature :=
  realize normalizerSignature (fun _ _ T => Real.log T ^ 2) (fun e => nomatch e)

private def unscaled : Realization normalizerSignature :=
  realize normalizerSignature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem normalizer_dependence : ObservationalDependence normalizerSignature normalizer := by
  intro _
  refine ⟨(), 1, 2, ?_⟩
  change Real.log 1 ^ 2 ≠ Real.log 2 ^ 2
  rw [Real.log_one, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  exact (pow_pos (Real.log_pos (show (1 : ℝ) < 2 by norm_num)) 2).ne

private theorem oneFinite (T : ℝ) : {_j : ULift.{u} Unit | (1 : ℝ) ≤ T}.Finite :=
  Set.toFinite _

private theorem one_cutoff (a : ℝ) :
    (fun T => cutoffSum (fun _ : ULift.{u} Unit => 1) oneFinite (fun _ => a) T)
      =ᶠ[atTop] fun _ => a := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hcut : (oneFinite T).toFinset = Finset.univ := by
    ext j
    simp [hT]
  unfold cutoffSum
  rw [hcut]
  simp

private theorem one_count :
    Tendsto (fun T => cutoffSum (fun _ : ULift.{u} Unit => 1) oneFinite (fun _ => 1) T /
      (T * Real.log T)) atTop (𝓝 0) := by
  have hden := tendsto_id.atTop_mul_atTop₀ Real.tendsto_log_atTop
  apply (hden.const_div_atTop 1).congr'
  filter_upwards [one_cutoff.{u} 1] with T hT
  exact congrArg (fun x => x / (T * Real.log T)) hT.symm

abbrev cutoffArena : Arena where
  signature := normalizerSignature
  Law R := ∀ {ι : Type u} (γ : ι → ℝ) (m w : ι → ℝ)
    (finite_le : ∀ T : ℝ, {j | γ j ≤ T}.Finite)
    (_hm : ∀ j, 0 ≤ m j) (_hw : ∀ j, 0 ≤ w j)
    (_hw_le : ∀ j, 0 < γ j → w j ≤ m j / γ j)
    (_hcount : Tendsto (fun T : ℝ => cutoffSum γ finite_le m T / (T * Real.log T))
      atTop (𝓝 0)),
    Tendsto (fun T : ℝ => cutoffSum γ finite_le w T / R.readout () () T) atTop (𝓝 0)

private theorem unscaled_cutoff_rejected : ¬ cutoffArena.{u}.Law unscaled := by
  intro law
  have h := law (fun _ : ULift.{u} Unit => 1) (fun _ => 1) (fun _ => 1) oneFinite
    (fun _ => zero_le_one) (fun _ => zero_le_one) (fun _ _ => by simp) one_count
  have h' : Tendsto (fun T =>
      cutoffSum (fun _ : ULift.{u} Unit => 1) oneFinite (fun _ => 1) T) atTop (𝓝 0) := by
    simpa only [unscaled, realize, div_one] using h
  exact zero_ne_one (tendsto_nhds_unique h' (tendsto_const_nhds.congr' (one_cutoff.{u} 1).symm))

def cutoffFamily : Registration cutoffArena.{u} (type_of% @cutoffMass_tendsto_zero.{u}) where
  actual := normalizer
  bridge := Iff.rfl
  variation := ⟨@cutoffMass_tendsto_zero.{u}, unscaled, unscaled_cutoff_rejected.{u}⟩
  sensitivity := sensitivity cutoffArena.{u}.Law normalizer unscaled unscaled_cutoff_rejected.{u}
  dependence := normalizer_dependence

def cutoffAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@cutoffMass_tendsto_zero.{u}) (Realization normalizerSignature) Unit Unit where
  unitName := `D5.S3.Analytic.Oscillation.SparseOrdinateMass.cutoffMass_tendsto_zero.audit
  realizationName :=
    `Reg.D5.S3.Analytic.Oscillation.SparseOrdinateMass.cutoffFamily
  realizationSource := none
  generated := false
  arena := .source ⟨cutoffArena.{u}⟩
  objectArena := .source ⟨cutoffArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cutoffArena.{u} ⟨cutoffFamily.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize normalizerSignature
    (fun _ _ T => Real.log T ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Oscillation.SparseOrdinateMass
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "fn", "arg", "body", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev harmonicArena : Arena where
  signature := normalizerSignature
  Law R := ∀ {ι : Type u} (γ m : ι → ℝ)
    (finite_le : ∀ T : ℝ, {j | γ j ≤ T}.Finite) (_hγ : ∀ j, 0 ≤ γ j)
    (_hm : ∀ j, 0 ≤ m j)
    (_hcount : Tendsto (fun T : ℝ => cutoffSum γ finite_le m T /
      (T * Real.log T)) atTop (𝓝 0)),
    Tendsto (fun T : ℝ => cutoffSum γ finite_le
      (fun j => m j * γ j / (1 / 4 + γ j ^ 2)) T / R.readout () () T) atTop (𝓝 0)

private theorem unscaled_harmonic_rejected : ¬ harmonicArena.{u}.Law unscaled := by
  intro law
  have h := law (fun _ : ULift.{u} Unit => 1) (fun _ => 1) oneFinite
    (fun _ => zero_le_one) (fun _ => zero_le_one) one_count
  have h' : Tendsto (fun T =>
      cutoffSum (fun _ : ULift.{u} Unit => 1) oneFinite (fun _ => (4 : ℝ) / 5) T)
      atTop (𝓝 0) := by
    have heq : (1 : ℝ) * 1 / (1 / 4 + 1 ^ 2) = 4 / 5 := by norm_num
    simpa only [unscaled, realize, div_one, heq] using h
  have hz := tendsto_nhds_unique h'
    (tendsto_const_nhds.congr' (one_cutoff.{u} ((4 : ℝ) / 5)).symm)
  norm_num at hz

def harmonicFamily : Registration harmonicArena.{u} (type_of% @harmonicMass_tendsto_zero.{u}) where
  actual := normalizer
  bridge := Iff.rfl
  variation := ⟨@harmonicMass_tendsto_zero.{u}, unscaled, unscaled_harmonic_rejected.{u}⟩
  sensitivity :=
    sensitivity harmonicArena.{u}.Law normalizer unscaled unscaled_harmonic_rejected.{u}
  dependence := normalizer_dependence

def harmonicAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@harmonicMass_tendsto_zero.{u}) (Realization normalizerSignature) Unit Unit where
  unitName := `D5.S3.Analytic.Oscillation.SparseOrdinateMass.harmonicMass_tendsto_zero.audit
  realizationName :=
    `Reg.D5.S3.Analytic.Oscillation.SparseOrdinateMass.harmonicFamily
  realizationSource := none
  generated := false
  arena := .source ⟨harmonicArena.{u}⟩
  objectArena := .source ⟨harmonicArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source harmonicArena.{u} ⟨harmonicFamily.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize normalizerSignature
    (fun _ _ T => Real.log T ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Oscillation.SparseOrdinateMass
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "fn", "fn", "arg", "body", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Analytic.Oscillation.SparseOrdinateMass
