import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Linear.ReflectingHeatInterpolation
import Reg.Support.SingleDependentReadout
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Source observations of the reflecting nodal factors and squared-norm bound. -/

namespace Reg.D5.S3.Observer.Linear.ReflectingHeatInterpolation

open _root_.D5.S3.Observer.Linear.ReflectingHeatInterpolation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support
open _root_.D5.S3.Observer.Linear.ReflectingHeatStripBound
open LeanInformationAudit MeasureTheory Polynomial Polynomial.Chebyshev

noncomputable section

namespace Nodal

abbrev signature := SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ[X])

def actual : Realization signature :=
  realize signature (fun _ _ n => nodalPolynomial n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ), R.readout () () n =
    (U ℝ (↑(n - 1 : ℕ))).comp (C (1 / 2) * (X - C 2))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h₁ := h 1
  change (0 : ℝ[X]) = (U ℝ 0).comp (C (1 / 2) * (X - C 2)) at h₁
  simp at h₁

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 1, 2, ?_⟩
  change nodalPolynomial 1 ≠ nodalPolynomial 2
  intro h
  have h₂ := congrArg (Polynomial.eval (2 : ℝ)) h
  rw [nodalPolynomial_eq_chebyshev 1, nodalPolynomial_eq_chebyshev 2] at h₂
  norm_num [U_zero, U_one] at h₂

def family : Registration arena (type_of% @nodalPolynomial_eq_chebyshev) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨nodalPolynomial_eq_chebyshev, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@nodalPolynomial_eq_chebyshev) (Realization signature) Type Unit where
  unitName := `D5.S3.Observer.Linear.ReflectingHeatInterpolation.nodalPolynomial_eq_chebyshev.__information_unit
  realizationName := `Reg.D5.S3.Observer.Linear.ReflectingHeatInterpolation.Nodal.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => nodalPolynomial n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.ReflectingHeatInterpolation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Nodal


private theorem distinct_three_cell_rates :
    rate 3 (0 : Mode 3) ≠ rate 3 (1 : Mode 3) :=
  fun h => (by decide : (0 : Mode 3) ≠ 1) (rate_injective (by decide) h)

private theorem derivative_three_first :
    nodalDerivative 3 (0 : Mode 3) = rate 3 (0 : Mode 3) - rate 3 (1 : Mode 3) := by
  have h : Finset.univ.erase (0 : Mode 3) = {1} := by decide
  simp [nodalDerivative, h]

private theorem derivative_three_last :
    nodalDerivative 3 (1 : Mode 3) = rate 3 (1 : Mode 3) - rate 3 (0 : Mode 3) := by
  have h : Finset.univ.erase (1 : Mode 3) = {0} := by decide
  simp [nodalDerivative, h]

private theorem omitted_two_cells : omittedPolynomial 2 (0 : Mode 2) = 1 := by
  have h : Finset.univ.erase (0 : Mode 2) = ∅ := by decide
  simp [omittedPolynomial, h]
namespace Derivative

abbrev signature := SingleDependentReadout.signature (ℕ) (Mode) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ n j => nodalDerivative n j) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (j : Mode n), |R.readout () n j| = (n : ℝ) /
      (2 * Real.sin (((j.val + 1 : ℕ) : ℝ) * Real.pi / n) ^ 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 3 0
  change |(0 : ℝ)| = _ at he
  have hz : |nodalDerivative 3 0| = 0 := by
    rw [abs_nodalDerivative 3 0, ← he, abs_zero]
  rw [abs_eq_zero, derivative_three_first, sub_eq_zero] at hz
  exact distinct_three_cell_rates hz

def family : Registration arena (type_of% @abs_nodalDerivative) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨abs_nodalDerivative, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(3 : ℕ), (0 : Mode 3), (1 : Mode 3), ?_⟩
    change nodalDerivative 3 0 ≠ nodalDerivative 3 1
    rw [derivative_three_first, derivative_three_last]
    intro h
    exact distinct_three_cell_rates (by linarith)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@abs_nodalDerivative) (Realization signature) Type Unit where
  unitName := `D5.S3.Observer.Linear.ReflectingHeatInterpolation.abs_nodalDerivative.__information_unit
  realizationName := `Reg.D5.S3.Observer.Linear.ReflectingHeatInterpolation.Derivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n j => nodalDerivative n j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.ReflectingHeatInterpolation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Derivative
namespace Uniform

abbrev signature := SingleDependentReadout.signature (ℕ) (Mode) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ n j => rate n j) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (j : Mode n),
    (n : ℝ) / 2 ≤ |nodalDerivative n j| ∧
    |nodalDerivative n j| ≤ (n : ℝ) ^ 3 / 8 ∧
    4 / (n : ℝ) ^ 2 ≤ R.readout () n j ∧ 4 / (n : ℝ) ^ 2 ≤ 4 - rate n j

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h 3 0).2.2.1
  change (4 : ℝ) / 3 ^ 2 ≤ 0 at he
  norm_num at he

def family : Registration arena (type_of% @uniform_nodal_factors) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨uniform_nodal_factors, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    exact ⟨(3 : ℕ), (0 : Mode 3), (1 : Mode 3), distinct_three_cell_rates⟩

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@uniform_nodal_factors) (Realization signature) Type Unit where
  unitName := `D5.S3.Observer.Linear.ReflectingHeatInterpolation.uniform_nodal_factors.__information_unit
  realizationName := `Reg.D5.S3.Observer.Linear.ReflectingHeatInterpolation.Uniform.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n j => rate n j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.ReflectingHeatInterpolation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Uniform
namespace Endpoint

abbrev signature := SingleDependentReadout.signature (ℕ) (Mode) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ n j => rate n j) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (j : Mode n),
    (n : ℝ) / (weight n j * |nodalDerivative n j|) = rate n j * weight n j ∧
    4 / (n : ℝ) ^ 2 ≤ R.readout () n j * weight n j

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h 3 0).2
  change (4 : ℝ) / 3 ^ 2 ≤ 0 * weight 3 0 at he
  norm_num at he

def family : Registration arena (type_of% @endpoint_normalization) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨endpoint_normalization, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    exact ⟨(3 : ℕ), (0 : Mode 3), (1 : Mode 3), distinct_three_cell_rates⟩

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@endpoint_normalization) (Realization signature) Type Unit where
  unitName := `D5.S3.Observer.Linear.ReflectingHeatInterpolation.endpoint_normalization.__information_unit
  realizationName := `Reg.D5.S3.Observer.Linear.ReflectingHeatInterpolation.Endpoint.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n j => rate n j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.ReflectingHeatInterpolation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Endpoint
namespace Growth

abbrev signature := SingleDependentReadout.signature ((n : ℕ) × Mode n) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p ω => Real.sqrt (rate p.1 p.2 ^ 2 + ω ^ 2)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (j : Mode n) (ω : ℝ) (ζ : ℂ)
    (_hζ : ζ ≠ 0) (_hroot : ζ + ζ⁻¹ = (ω : ℂ) * Complex.I - 2) (_hunit : 1 ≤ ‖ζ‖),
    ‖(omittedPolynomial n j).eval ((ω : ℂ) * Complex.I)‖ ≤
      (n : ℝ) * ‖ζ‖ ^ (n - 1) / R.readout () ⟨n, j⟩ ω

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 2 0 0 (-1) (by norm_num) (by push_cast; norm_num) (by simp)
  change ‖(omittedPolynomial 2 0).eval _‖ ≤ _ / (0 : ℝ) at he
  norm_num [omitted_two_cells] at he

def family : Registration arena (type_of% @norm_omittedPolynomial_eval) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨norm_omittedPolynomial_eval, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨⟨2, 0⟩, (0 : ℝ), (1 : ℝ), ?_⟩
    change Real.sqrt (rate 2 (0 : Mode 2) ^ 2 + (0 : ℝ) ^ 2) ≠
      Real.sqrt (rate 2 (0 : Mode 2) ^ 2 + (1 : ℝ) ^ 2)
    intro h
    have hs := congrArg (fun x : ℝ => x ^ 2) h
    simp only [Real.sq_sqrt (by positivity : 0 ≤ rate 2 (0 : Mode 2) ^ 2 + (0 : ℝ) ^ 2),
      Real.sq_sqrt (by positivity : 0 ≤ rate 2 (0 : Mode 2) ^ 2 + (1 : ℝ) ^ 2)] at hs
    norm_num at hs

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@norm_omittedPolynomial_eval) (Realization signature) Type Unit where
  unitName := `D5.S3.Observer.Linear.ReflectingHeatInterpolation.norm_omittedPolynomial_eval.__information_unit
  realizationName := `Reg.D5.S3.Observer.Linear.ReflectingHeatInterpolation.Growth.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p ω => Real.sqrt (rate p.1 p.2 ^ 2 + ω ^ 2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.ReflectingHeatInterpolation
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Growth

private theorem outer_root_at_frequency (ω : ℝ) :
    ∃ ζ : ℂ, ζ ≠ 0 ∧ ζ + ζ⁻¹ = (ω : ℂ) * Complex.I - 2 ∧ 1 ≤ ‖ζ‖ := by
  let c := (ω : ℂ) * Complex.I - 2
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (c ^ 2 - 4) (n := 2) (by decide)
  let z := (c + s) / 2
  let y := (c - s) / 2
  have hmul : z * y = 1 := by
    dsimp [z, y]
    linear_combination -hs / 4
  have hz : z ≠ 0 := by
    intro h
    simp [h] at hmul
  have hy : y = z⁻¹ := by
    field_simp [hz]
    rw [mul_comm]
    exact hmul
  have he : z + z⁻¹ = c := by rw [← hy]; dsimp [z, y]; ring
  by_cases h : 1 ≤ ‖z‖
  · exact ⟨z, hz, he, h⟩
  · refine ⟨z⁻¹, inv_ne_zero hz, ?_, ?_⟩
    · rw [inv_inv, add_comm, he]
    · rw [norm_inv]
      exact one_le_inv₀ (norm_pos_iff.mpr hz) |>.2 (le_of_not_ge h)
namespace SquaredNorm

abbrev signature := SingleDependentReadout.signature (ℕ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ n A => ((n : ℝ) * A) ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (j : Mode n) (M : ℂ → ℂ)
    (_hM_meas : Measurable (fun ω : ℝ => M (ω : ℂ))) {A B : ℝ}
    (_hM : ∀ ω : ℝ, ∃ ζ : ℂ, ζ ≠ 0 ∧
      ζ + ζ⁻¹ = (ω : ℂ) * Complex.I - 2 ∧ 1 ≤ ‖ζ‖ ∧
      ‖M (ω : ℂ)‖ ≤ A * (1 + B * |ω|) / ‖ζ‖ ^ n),
    MemLp (fun ω : ℝ => momentInterpolant n j M (ω : ℂ)) 2 volume ∧
    (∫ ω : ℝ, ‖momentInterpolant n j M (ω : ℂ)‖ ^ 2) ≤
      2 * R.readout () n A * Real.pi * ((n : ℝ) ^ 2 / 4 + 2 * B ^ 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h 2 0 (fun _ => 0) measurable_const (A := 0) (B := 0) (by
    intro ω
    obtain ⟨ζ, hz, he, hn⟩ := outer_root_at_frequency ω
    exact ⟨ζ, hz, he, hn, by simp⟩)).2
  change (∫ ω : ℝ, ‖momentInterpolant 2 0 (fun _ => 0) (ω : ℂ)‖ ^ 2) ≤
    2 * (-1 : ℝ) * Real.pi * ((2 : ℝ) ^ 2 / 4 + 2 * (0 : ℝ) ^ 2) at he
  simp [momentInterpolant] at he
  nlinarith [Real.pi_pos]

def family : Registration arena (type_of% @momentInterpolant_L2_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨momentInterpolant_L2_bound, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(2 : ℕ), (0 : ℝ), (1 : ℝ), ?_⟩
    change ((2 : ℝ) * 0) ^ (2 : ℕ) ≠ ((2 : ℝ) * 1) ^ (2 : ℕ)
    norm_num

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@momentInterpolant_L2_bound) (Realization signature) Type Unit where
  unitName := `D5.S3.Observer.Linear.ReflectingHeatInterpolation.momentInterpolant_L2_bound.__information_unit
  realizationName := `Reg.D5.S3.Observer.Linear.ReflectingHeatInterpolation.SquaredNorm.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n A => ((n : ℝ) * A) ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.ReflectingHeatInterpolation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn",
        "arg", "fn", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SquaredNorm

end

end Reg.D5.S3.Observer.Linear.ReflectingHeatInterpolation
