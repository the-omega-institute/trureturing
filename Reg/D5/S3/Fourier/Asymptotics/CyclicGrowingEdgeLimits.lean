import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Asymptotics.CyclicGrowingEdgeLimits

/-! Readout dependence of critical-scale fitted coefficient and boundary limits. -/

namespace Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingEdgeLimits

open Filter Matrix Finset
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Asymptotics.CyclicGrowingEdgeLimits
open _root_.Reg.Support

noncomputable section

private theorem zero_scale :
    Tendsto (fun n : ℕ => (n : ℝ)^5 * (0 : ℝ)^2) atTop (𝓝 0) := by simp

private theorem zero_nonempty : ({0} : Finset ℝ).Nonempty := by simp
private theorem one_nonempty : ({1} : Finset ℝ).Nonempty := by simp

namespace Coefficients

abbrev State := (Finset ℝ × ℕ) × ℝ

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => State)
  (fun _ => Fin 3 → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ state => coefficientFit state.1.1 state.1.2 state.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {h : ℕ → ℝ} {K : ℝ},
    Tendsto (fun n : ℕ => (n : ℝ)^5 * (h n)^2) atTop (𝓝 K) →
    ∀ S : Finset ℝ, S.Nonempty →
    let readout := R.readout () ()
    Tendsto (fun n => readout ((S,n),h n)) atTop (𝓝 (limitCoefficients S K))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ht := h (h := fun _ => 0) (K := 0) zero_scale {0} zero_nonempty
  have hh := tendsto_pi_nhds.1 ht (0 : Fin 3)
  change Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (3/4)) at hh
  have he := tendsto_nhds_unique tendsto_const_nhds hh
  norm_num at he

private theorem observed_values_differ :
    ∃ x y : State, actual.readout () () x ≠ actual.readout () () y := by
  by_contra! h
  have h0 := coefficient_tendsto (h := fun _ => 0) (K := 0) zero_scale {0} zero_nonempty
  have h1 := coefficient_tendsto (h := fun _ => 0) (K := 0) zero_scale {1} one_nonempty
  change Tendsto (fun n => actual.readout () () (({0},n),0)) atTop (𝓝 (limitCoefficients {0} 0)) at h0
  change Tendsto (fun n => actual.readout () () (({1},n),0)) atTop (𝓝 (limitCoefficients {1} 0)) at h1
  have heq : (fun n => actual.readout () () (({0},n),0)) =
      (fun n => actual.readout () () (({1},n),0)) := funext fun n => h _ _
  rw [heq] at h0
  have e := congrFun (tendsto_nhds_unique h0 h1) (2 : Fin 3)
  norm_num [limitCoefficients] at e

def evidence : Registration arena (type_of% @coefficient_tendsto) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@coefficient_tendsto, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    obtain ⟨x,y,hxy⟩ := observed_values_differ
    exact ⟨(), x, y, hxy⟩

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@coefficient_tendsto) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingEdgeLimits.Coefficients.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingEdgeLimits.Coefficients.evidence
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
    owner := `D5.S3.Fourier.Asymptotics.CyclicGrowingEdgeLimits
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

end Coefficients

namespace Refinement

abbrev signature := Coefficients.signature
abbrev actual := Coefficients.actual
abbrev rejected := Coefficients.rejected

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {h : ℕ → ℝ} {K : ℝ},
    Tendsto (fun n : ℕ => (n : ℝ)^5 * (h n)^2) atTop (𝓝 K) →
    ∀ S : Finset ℝ, S.Nonempty →
    let readout := R.readout () ()
    Tendsto (fun n : ℕ => fun i : Fin 2 => (n : ℝ) *
      (readout ((S,n),h n) i.castSucc - latticeCoeffs n i)) atTop (𝓝 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp := h (h := fun _ => 0) (K := 0) zero_scale {0} zero_nonempty
  have ha := refined_coefficients (h := fun _ => 0) (K := 0) zero_scale {0} zero_nonempty
  have hp0 := tendsto_pi_nhds.1 hp (0 : Fin 2)
  have ha0 := tendsto_pi_nhds.1 ha (0 : Fin 2)
  change Tendsto (fun n : ℕ => (n : ℝ) * (0 - latticeCoeffs n 0)) atTop (𝓝 0) at hp0
  change Tendsto (fun n : ℕ => (n : ℝ) *
    (coefficientFit {0} n 0 0 - latticeCoeffs n 0)) atTop (𝓝 0) at ha0
  have hscaled : Tendsto (fun n : ℕ => (n : ℝ) * coefficientFit {0} n 0 0)
      atTop (𝓝 0) := by
    apply (show Tendsto (fun n : ℕ =>
      (n : ℝ) * (coefficientFit {0} n 0 0 - latticeCoeffs n 0) -
      (n : ℝ) * (0 - latticeCoeffs n 0)) atTop (𝓝 0) by
      simpa only [sub_zero] using ha0.sub hp0).congr
    intro n
    ring
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hn
  have hzero : Tendsto (fun n => coefficientFit {0} n 0 0) atTop (𝓝 0) := by
    apply (show Tendsto (fun n : ℕ => ((n : ℝ) * coefficientFit {0} n 0 0) *
      (n : ℝ)⁻¹) atTop (𝓝 0) by simpa only [mul_zero] using hscaled.mul hi).congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show 0 < n from hn).ne'
    field_simp [hn0]
  have ht := coefficient_tendsto (h := fun _ => 0) (K := 0) zero_scale {0} zero_nonempty
  have ht0 := tendsto_pi_nhds.1 ht (0 : Fin 3)
  change Tendsto (fun n => coefficientFit {0} n 0 0) atTop (𝓝 (3/4)) at ht0
  have he := tendsto_nhds_unique hzero ht0
  norm_num at he

def evidence : Registration arena (type_of% @refined_coefficients) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@refined_coefficients, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    obtain ⟨x,y,hxy⟩ := Coefficients.observed_values_differ
    exact ⟨(), x, y, hxy⟩

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@refined_coefficients) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingEdgeLimits.Refinement.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingEdgeLimits.Refinement.evidence
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
    owner := `D5.S3.Fourier.Asymptotics.CyclicGrowingEdgeLimits
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

end Refinement

namespace FrontEdge

abbrev State := ((Finset ℝ × ℕ) × ℝ) × ℝ

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => State)
  (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ state => boundaryValue state.1.1.1 state.1.1.2 state.1.2 state.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {h : ℕ → ℝ} {K : ℝ},
    Tendsto (fun n : ℕ => (n : ℝ)^5 * (h n)^2) atTop (𝓝 K) →
    ∀ S : Finset ℝ, S.Nonempty → ∀ r : ℝ,
    let readout := R.readout () ()
    Tendsto (fun n : ℕ => (n : ℝ)^2 * readout (((S,n),h n),r)) atTop (𝓝 ((3/4)*(1-2*r)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ht := h (h := fun _ => 0) (K := 0) zero_scale {0} zero_nonempty 0
  change Tendsto (fun n : ℕ => (n : ℝ)^2 * 0) atTop (𝓝 ((3/4)*(1-2*0))) at ht
  have hconst : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (3/4)) := by
    simpa only [mul_zero, sub_zero, mul_one] using ht
  have he := tendsto_nhds_unique tendsto_const_nhds hconst
  norm_num at he

private theorem observed_values_differ :
    ∃ x y : State, actual.readout () () x ≠ actual.readout () () y := by
  by_contra! h
  have h0 := scaled_boundary_value (h := fun _ => 0) (K := 0) zero_scale {0} zero_nonempty 0
  have h1 := scaled_boundary_value (h := fun _ => 0) (K := 0) zero_scale {0} zero_nonempty 1
  have ht0 : Tendsto (fun n : ℕ => (n : ℝ)^2 * actual.readout () () ((({0},n),0),0))
      atTop (𝓝 (3/4)) := by
    change Tendsto (fun n : ℕ => (n : ℝ)^2 * boundaryValue {0} n 0 0) atTop (𝓝 (3/4))
    convert h0 using 1 <;> norm_num [limitCoefficients]
  have ht1 : Tendsto (fun n : ℕ => (n : ℝ)^2 * actual.readout () () ((({0},n),0),1))
      atTop (𝓝 (-3/4)) := by
    change Tendsto (fun n : ℕ => (n : ℝ)^2 * boundaryValue {0} n 0 1) atTop (𝓝 (-3/4))
    convert h1 using 1 <;> norm_num [limitCoefficients]
  have heq : (fun n : ℕ => (n : ℝ)^2 * actual.readout () () ((({0},n),0),0)) =
      (fun n : ℕ => (n : ℝ)^2 * actual.readout () () ((({0},n),0),1)) := by
    funext n
    rw [h ((({0},n),0),0) ((({0},n),0),1)]
  rw [heq] at ht0
  have he := tendsto_nhds_unique ht0 ht1
  norm_num at he

def evidence : Registration arena (type_of% @scaled_boundary_value) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@scaled_boundary_value, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    obtain ⟨x,y,hxy⟩ := observed_values_differ
    exact ⟨(), x, y, hxy⟩

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@scaled_boundary_value) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingEdgeLimits.FrontEdge.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingEdgeLimits.FrontEdge.evidence
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
    owner := `D5.S3.Fourier.Asymptotics.CyclicGrowingEdgeLimits
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FrontEdge

namespace RearEdge

abbrev State := ((Finset ℝ × ℕ) × ℝ) × ℝ

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => State)
  (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ state => rearValue state.1.1.1 state.1.1.2 state.1.2 state.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {h : ℕ → ℝ} {K : ℝ},
    Tendsto (fun n : ℕ => (n : ℝ)^5 * (h n)^2) atTop (𝓝 K) →
    ∀ S : Finset ℝ, S.Nonempty → ∀ r : ℝ,
    let readout := R.readout () ()
    Tendsto (fun n : ℕ => (n : ℝ)^3 * readout (((S,n),h n),r)) atTop (𝓝 (limitCoefficients S K 2 - 3*r^2/4))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ht := h (h := fun _ => 0) (K := 0) zero_scale {0} zero_nonempty 1
  change Tendsto (fun n : ℕ => (n : ℝ)^3 * 0) atTop
    (𝓝 (limitCoefficients {0} 0 2 - 3*(1 : ℝ)^2/4)) at ht
  have hconst : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (-3/4)) := by
    convert ht using 1 <;> norm_num [limitCoefficients]
  have he := tendsto_nhds_unique tendsto_const_nhds hconst
  norm_num at he

private theorem observed_values_differ :
    ∃ x y : State, actual.readout () () x ≠ actual.readout () () y := by
  by_contra! h
  have h0 := scaled_rear_value (h := fun _ => 0) (K := 0) zero_scale {0} zero_nonempty 0
  have h1 := scaled_rear_value (h := fun _ => 0) (K := 0) zero_scale {0} zero_nonempty 1
  have ht0 : Tendsto (fun n : ℕ => (n : ℝ)^3 * actual.readout () () ((({0},n),0),0))
      atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => (n : ℝ)^3 * rearValue {0} n 0 0) atTop (𝓝 0)
    convert h0 using 1 <;> norm_num [limitCoefficients]
  have ht1 : Tendsto (fun n : ℕ => (n : ℝ)^3 * actual.readout () () ((({0},n),0),1))
      atTop (𝓝 (-3/4)) := by
    change Tendsto (fun n : ℕ => (n : ℝ)^3 * rearValue {0} n 0 1) atTop (𝓝 (-3/4))
    convert h1 using 1 <;> norm_num [limitCoefficients]
  have heq : (fun n : ℕ => (n : ℝ)^3 * actual.readout () () ((({0},n),0),0)) =
      (fun n : ℕ => (n : ℝ)^3 * actual.readout () () ((({0},n),0),1)) := by
    funext n
    rw [h ((({0},n),0),0) ((({0},n),0),1)]
  rw [heq] at ht0
  have he := tendsto_nhds_unique ht0 ht1
  norm_num at he

def evidence : Registration arena (type_of% @scaled_rear_value) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@scaled_rear_value, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    obtain ⟨x,y,hxy⟩ := observed_values_differ
    exact ⟨(), x, y, hxy⟩

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@scaled_rear_value) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingEdgeLimits.RearEdge.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingEdgeLimits.RearEdge.evidence
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
    owner := `D5.S3.Fourier.Asymptotics.CyclicGrowingEdgeLimits
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RearEdge

end

end Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingEdgeLimits
