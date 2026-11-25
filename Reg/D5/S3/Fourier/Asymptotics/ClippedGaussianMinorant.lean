import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Asymptotics.ClippedGaussianMinorant

/-! Dependence on the Gaussian readout in the moving-window limit. -/

namespace Reg.D5.S3.Fourier.Asymptotics.ClippedGaussianMinorant

open Filter MeasureTheory
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Asymptotics.ClippedGaussianMinorant
open _root_.Reg.Support

noncomputable section

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ u => Real.exp (-u^2)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change Real.exp (-(0:ℝ)^2) ≠ Real.exp (-(1:ℝ)^2)
  apply Real.exp_injective.ne
  norm_num

namespace Window

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (V A : ℕ → ℝ), (∀ᶠ n in atTop, 0 < V n) →
    let scale := fun n : ℕ => Real.sqrt ((n : ℝ)*V n)
    let radius := fun n => A n*scale n
    let readout := R.readout () ()
    Tendsto (fun n => scale n *
      (∫ t in -(A n)..A n, (max 0 (1-V n*t^2/2))^(2*n)) -
      ∫ u in -(radius n)..radius n, readout u) atTop (𝓝 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have hv : ∀ᶠ n : ℕ in atTop, 0 < (1:ℝ) := Eventually.of_forall fun _ => zero_lt_one
  have hr : Tendsto (fun n : ℕ => (1:ℝ) * Real.sqrt ((n:ℝ)*1)) atTop atTop := by
    simpa [Function.comp_def] using (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hfull := (clipped_gaussian_full_limit_iff (fun _ => 1) (fun _ => 1) hv).mpr hr
  have hz := law (fun _ => 1) (fun _ => 1) hv
  have hz' : Tendsto (fun n : ℕ => Real.sqrt ((n:ℝ)*1) *
      (∫ t in -(1:ℝ)..1, (max 0 (1-1*t^2/2))^(2*n))) atTop (𝓝 0) := by
    simpa [rejected, realize] using hz
  have he := tendsto_nhds_unique hfull hz'
  rw [show (∫ u : ℝ, Real.exp (-u^2)) = Real.sqrt Real.pi by
    simpa using integral_gaussian 1] at he
  exact (Real.sqrt_pos.mpr Real.pi_pos).ne' he

def evidence : Registration arena (type_of% @clipped_gaussian_window_error) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@clipped_gaussian_window_error, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@clipped_gaussian_window_error) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.ClippedGaussianMinorant.Window.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.ClippedGaussianMinorant.Window.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Asymptotics.ClippedGaussianMinorant
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Window

namespace FullLimit

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (V A : ℕ → ℝ), (∀ᶠ n in atTop, 0 < V n) →
    let scale := fun n : ℕ => Real.sqrt ((n : ℝ)*V n)
    let radius := fun n => A n*scale n
    let readout := R.readout () ()
    Tendsto (fun n => scale n *
      (∫ t in -(A n)..A n, (max 0 (1-V n*t^2/2))^(2*n))) atTop
      (𝓝 (∫ u : ℝ, readout u)) ↔ Tendsto radius atTop atTop

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have hv : ∀ᶠ n : ℕ in atTop, 0 < (1:ℝ) := Eventually.of_forall fun _ => zero_lt_one
  have hh := law (fun _ => 1) (fun _ => 0) hv
  have hr : Tendsto (fun _ : ℕ => (0:ℝ)) atTop atTop := by
    simpa using hh.mp (by simp [rejected, realize])
  have hbad := hr.eventually_ge_atTop (1:ℝ)
  obtain ⟨_, hn⟩ := hbad.exists
  norm_num at hn

def evidence : Registration arena (type_of% @clipped_gaussian_full_limit_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@clipped_gaussian_full_limit_iff, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@clipped_gaussian_full_limit_iff) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.ClippedGaussianMinorant.FullLimit.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.ClippedGaussianMinorant.FullLimit.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Asymptotics.ClippedGaussianMinorant
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FullLimit

end

end Reg.D5.S3.Fourier.Asymptotics.ClippedGaussianMinorant
