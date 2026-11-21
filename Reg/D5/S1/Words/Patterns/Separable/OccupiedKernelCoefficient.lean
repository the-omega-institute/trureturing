import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Patterns.Separable.OccupiedKernelCoefficient
import Reg.Support.DependentFamily

namespace Reg.D5.S1.Words.Patterns.Separable.OccupiedKernelCoefficient

open _root_.D5.S1.Words.Patterns.Separable.ActualCardinality
open _root_.D5.S1.Words.Patterns.Separable.OccupiedComparison
open _root_.D5.S1.Words.Patterns.Separable.OccupiedKernelCoefficient
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => kernelWeight n) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature
  Law R := ∃ C > (0 : ℝ), ∀ m : ℕ, 2 ≤ m →
    |R.readout () () (m-1)-C/((m:ℝ)*Real.sqrt m)| ≤ (21/16)/((m:ℝ)^2*Real.sqrt m)

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨C, hC, h⟩
  have bnd := h 2 (by decide)
  change |(-1 : ℝ) - C / ((2 : ℝ) * Real.sqrt 2)| ≤
    (21/16)/((2 : ℝ)^2*Real.sqrt 2) at bnd
  have hs : 1 ≤ Real.sqrt (2 : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs₀ : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hc : 0 < C / ((2 : ℝ) * Real.sqrt 2) := by positivity
  have hu : (21/16 : ℝ)/((2 : ℝ)^2*Real.sqrt 2) < 1 := by
    apply (div_lt_iff₀ (by positivity)).2
    linarith
  rw [abs_of_neg (by linarith)] at bnd
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  change kernelWeight 1 ≠ kernelWeight 2
  have hS1 : Nat.largeSchroder 1 = 2 := by
    rw [Nat.largeSchroder_succ 0, ← Nat.range_succ_eq_Iic]
    simp [Nat.largeSchroder_zero]
  have hS2 : Nat.largeSchroder 2 = 6 := by
    rw [Nat.largeSchroder_succ 1, ← Nat.range_succ_eq_Iic]
    norm_num [Finset.sum_range_succ, Nat.largeSchroder_zero, hS1]
  have h1 : kernelWeight 1 = 2 * rho^2 := by
    simp only [kernelWeight, shapeWeight, Nat.add_one_ne_zero, ite_false, add_zero]
    rw [actual_schroder_cardinality.2.1 2 (by decide)]
    norm_num [hS1]
    ring
  have h2 : kernelWeight 2 = 6 * rho^3 := by
    simp only [kernelWeight, shapeWeight, Nat.add_one_ne_zero, ite_false, add_zero]
    rw [actual_schroder_cardinality.2.1 3 (by decide)]
    norm_num [hS2]
    ring
  have hb₀ : 0 < b := by
    unfold b
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hn := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have hb : b ≤ (1/2 : ℝ) := by
    unfold b
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hn := sq_nonneg (Real.sqrt (2 : ℝ) - 3/2)
    nlinarith
  have hρ₀ : 0 < rho := by unfold rho; positivity
  have hρ : rho ≤ (1/4 : ℝ) := by
    unfold rho
    nlinarith only [mul_nonneg (sub_nonneg.mpr hb) (show (0 : ℝ) ≤ 1/2+b by linarith)]
  rw [h1, h2]
  apply ne_of_gt
  have hfac : (6 : ℝ) * rho < 2 := by linarith
  have h := mul_lt_mul_of_pos_right hfac (pow_pos hρ₀ 2)
  nlinarith only [h]

def family : Registration arena (type_of% @actual_kernel_weight_strict_remainder) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_kernel_weight_strict_remainder, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_kernel_weight_strict_remainder) (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S1.Words.Patterns.Separable.OccupiedKernelCoefficient.unit
  realizationName := `Reg.D5.S1.Words.Patterns.Separable.OccupiedKernelCoefficient.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => kernelWeight n) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Patterns.Separable.OccupiedKernelCoefficient
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S1.Words.Patterns.Separable.OccupiedKernelCoefficient
