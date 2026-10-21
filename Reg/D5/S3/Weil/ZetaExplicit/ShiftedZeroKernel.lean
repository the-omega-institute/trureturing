import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaExplicit.ShiftedZeroKernel
import Reg.Support.DependentFamily

/-! Source-bound audit of the logarithmic frequency dependence in the kernel bound. -/

namespace Reg.D5.S3.Weil.ZetaExplicit.ShiftedZeroKernel

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Zeta23 Zeta23.WeilEF LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ s => Real.log (|s| + 3)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

/-- Observe the frequency-dependent logarithm in the upper bound, retaining
both original conclusion clauses and all the original local-count hypotheses. -/
def arena : Arena where
  signature := signature
  Law R := ∀ (Z : ZeroConfig) {A : ℝ}, 1 ≤ A →
    (∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A * Real.log (|t| + 3)) → ∀ s : ℝ,
    Summable (fun ρ : Z.carrier =>
      (Z.mult ρ : ℝ) / (1 + (s - (gammaOf ρ).re) ^ 2)) ∧
    (∑' ρ : Z.carrier, (Z.mult ρ : ℝ) / (1 + (s - (gammaOf ρ).re) ^ 2)) ≤
      27 * A * totalWeight * R.readout () () s

private def emptyConfig : ZeroConfig where
  carrier := ∅
  mult := 0
  one_le_mult := by simp
  strip := by simp
  reflect_mem := by simp
  mult_reflect := by simp
  finite_window := by simp

private theorem totalWeight_positive : 0 < totalWeight := by
  have h := summable_weight.sum_le_tsum ({0} : Finset ℤ) (fun j _ =>
    div_nonneg (Real.log_nonneg (by linarith [abs_nonneg (j : ℝ)])) (by positivity))
  have hlog : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  norm_num [totalWeight] at h ⊢
  linarith

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hlocal : ∀ t : ℝ, (emptyConfig.N t (t + 1) : ℝ) ≤
      (1 : ℝ) * Real.log (|t| + 3) := by
    intro t
    simpa [emptyConfig, ZeroConfig.N, ZeroConfig.window] using
      Real.log_nonneg (show 1 ≤ |t| + 3 by linarith [abs_nonneg t])
  have hbad := (h emptyConfig (A := 1) (by norm_num) hlocal 0).2
  have he : IsEmpty emptyConfig.carrier := by
    change IsEmpty {z : ℂ // z ∈ (∅ : Set ℂ)}
    infer_instance
  haveI := he
  simp only [rejected, realize, mul_one, tsum_empty] at hbad
  nlinarith [totalWeight_positive]

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  change Real.log (|0| + 3 : ℝ) ≠ Real.log (|1| + 3 : ℝ)
  norm_num only [abs_zero, abs_one, zero_add]
  exact ne_of_lt (Real.log_lt_log (by norm_num) (by norm_num))

def sourceRegistration : Registration arena (type_of% (@shifted_zero_kernel_summable_tsum_le)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨shifted_zero_kernel_summable_tsum_le, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro e
      exact nomatch e
  dependence := actual_dependence

def registration_1 : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@shifted_zero_kernel_summable_tsum_le) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaExplicit.ShiftedZeroKernel.shifted_zero_kernel_summable_tsum_le
  realizationName := `Reg.D5.S3.Weil.ZetaExplicit.ShiftedZeroKernel.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => Real.log (|s| + 3)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaExplicit.ShiftedZeroKernel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms sourceRegistration
#print axioms registration_1

end
end Reg.D5.S3.Weil.ZetaExplicit.ShiftedZeroKernel
