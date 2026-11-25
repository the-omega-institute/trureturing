import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Asymptotics.CyclicGrowingCoupledFit

/-! Dependence of the coupled moment limit on the finite sampled matrix. -/

namespace Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingCoupledFit

open Filter Matrix Finset
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Asymptotics.CyclicGrowingCoupledFit
open _root_.Reg.Support

noncomputable section

namespace Limit

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => (Finset ℝ × ℕ) × ℝ)
  (fun _ => Matrix (Fin 3) (Fin 3) ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ state => coupledMomentMatrix state.1.1 state.1.2 state.2)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {h : ℕ → ℝ}, Tendsto h atTop (𝓝 0) →
    Tendsto (fun n : ℕ => (n : ℝ) * h n) atTop (𝓝 0) →
    Tendsto (fun n : ℕ => (n : ℝ)^3 * ((n : ℝ) * h n)^4) atTop (𝓝 0) →
    ∀ S : Finset ℝ, let readout := R.readout () ()
    Tendsto (fun n : ℕ => readout ((S, n), h n)) atTop
      (𝓝 !![(2 : ℝ), 2/3, 0; 2/3, 2/5, 0; 0, ∑ r ∈ S, r^2, (S.card : ℝ)])

private theorem zero_mesh :
    Tendsto (fun n : ℕ => (n : ℝ) * (0 : ℝ)) atTop (𝓝 0) := by simp

private theorem zero_scale :
    Tendsto (fun n : ℕ => (n : ℝ)^3 * ((n : ℝ) * (0 : ℝ))^4) atTop (𝓝 0) := by simp

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (h := fun _ => 0) tendsto_const_nhds zero_mesh zero_scale ∅
  have ht := tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hh (0 : Fin 3)) (0 : Fin 3)
  change Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 2) at ht
  have he := tendsto_nhds_unique tendsto_const_nhds ht
  norm_num at he

private theorem observed_values_differ :
    actual.readout () () ((∅, 1), 0) ≠ actual.readout () () (({0}, 1), 0) := by
  intro eq
  have e := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 2 2) eq
  change coupledMomentMatrix ∅ 1 0 2 2 = coupledMomentMatrix {0} 1 0 2 2 at e
  simp only [coupledMomentMatrix, sum_empty, sum_singleton, Matrix.add_apply, Matrix.zero_apply,
    add_zero] at e
  change _ = _ + rearWeight 0 0 ^ 3 at e
  norm_num [rearWeight] at e

def evidence : Registration arena (type_of% @coupledMatrix_tendsto) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@coupledMatrix_tendsto, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    exact ⟨(), ((∅, 1), 0), (({0}, 1), 0), observed_values_differ⟩

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@coupledMatrix_tendsto) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingCoupledFit.Limit.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingCoupledFit.Limit.evidence
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
    owner := `D5.S3.Fourier.Asymptotics.CyclicGrowingCoupledFit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Limit

namespace Fit

abbrev signature := UniverseSingleReadout.signature Unit
  (fun _ => ((Finset ℝ × ℕ) × ℝ) × (Fin 3 → ℝ)) (fun _ => Fin 3 → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ state => coupledMoments state.1.1.1 state.1.1.2 state.1.2 state.2)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {h : ℕ → ℝ}, Tendsto h atTop (𝓝 0) →
    Tendsto (fun n : ℕ => (n : ℝ) * h n) atTop (𝓝 0) →
    Tendsto (fun n : ℕ => (n : ℝ)^3 * ((n : ℝ) * h n)^4) atTop (𝓝 0) →
    ∀ {S : Finset ℝ}, S.Nonempty → ∀ rhs : ℕ → Fin 3 → ℝ,
      let readout := R.readout () ()
      ∀ᶠ n : ℕ in atTop, ∃! v : Fin 3 → ℝ, readout (((S, n), h n), v) = rhs n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := h (h := fun _ => 0) tendsto_const_nhds Limit.zero_mesh Limit.zero_scale
    (S := {0}) (by simp) (fun _ => 1)
  obtain ⟨n, hn⟩ := eventually_atTop.mp hf
  obtain ⟨v, hv, _⟩ := hn n le_rfl
  have he : (0 : Fin 3 → ℝ) = 1 := hv
  have hzero := congrFun he (0 : Fin 3)
  norm_num at hzero

private theorem observed_values_differ :
    ∃ a b, actual.readout () () a ≠ actual.readout () () b := by
  have hzero := coupledFit_eventually (h := fun _ => 0) tendsto_const_nhds
    Limit.zero_mesh Limit.zero_scale (S := {0}) (by simp) (fun _ => 0)
  have hone := coupledFit_eventually (h := fun _ => 0) tendsto_const_nhds
    Limit.zero_mesh Limit.zero_scale (S := {0}) (by simp) (fun _ => 1)
  obtain ⟨n, hn⟩ := eventually_atTop.mp (hzero.and hone)
  obtain ⟨⟨v, hv, _⟩, ⟨w, hw, _⟩⟩ := hn n le_rfl
  refine ⟨((({0}, n), 0), v), ((({0}, n), 0), w), ?_⟩
  change coupledMoments {0} n 0 v ≠ coupledMoments {0} n 0 w
  rw [show coupledMoments {0} n 0 v = 0 from hv,
      show coupledMoments {0} n 0 w = 1 from hw]
  intro e
  have h := congrFun e (0 : Fin 3)
  norm_num at h

def evidence : Registration arena (type_of% @coupledFit_eventually) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@coupledFit_eventually, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    obtain ⟨a, b, h⟩ := observed_values_differ
    exact ⟨(), a, b, h⟩

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@coupledFit_eventually) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingCoupledFit.Fit.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingCoupledFit.Fit.evidence
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
    owner := `D5.S3.Fourier.Asymptotics.CyclicGrowingCoupledFit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Fit

end

end Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingCoupledFit
