import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Hardy.FiniteBlaschkeBound
import Reg.Support.SingleDependentReadout

/-! The value of a bounded holomorphic function at the evaluation point. -/

namespace Reg.D5.S3.Analytic.Hardy.FiniteBlaschkeBound

open _root_.D5.S3.Analytic.Hardy.FiniteBlaschkeBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support
open LeanInformationAudit Metric
open scoped ComplexConjugate

noncomputable section
universe u

abbrev signature := SingleDependentReadout.signature (ℂ → ℂ) (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ f z => f z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} (s : Finset ι) (a : ι → ℂ)
    {M : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (_hf : DifferentiableOn ℂ f (ball 0 1))
    (_hM : ∀ w ∈ ball 0 1, ‖f w‖ ≤ M)
    (_ha : ∀ k ∈ s, a k ∈ ball 0 1)
    (_hzero : ∀ k ∈ s, f (a k) = 0)
    (_hinj : Function.Injective a) (_hz : z ∈ ball 0 1),
    ‖R.readout () f z‖ ≤ M * ∏ k ∈ s, ‖(z - a k) / (1 - conj (a k) * z)‖

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hbad := h (∅ : Finset (ULift.{u} Unit)) (fun _ => 0)
    (M := 0) (f := fun _ => 0) (z := 0) (differentiableOn_const _)
    (by simp) (by simp) (by simp) (fun _ _ _ => Subsingleton.elim _ _) (by simp)
  norm_num [rejected, realize] at hbad

def family : Registration arena (type_of% @norm_le_mul_prod.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨norm_le_mul_prod, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    exact ⟨id, (0 : ℂ), (1 : ℂ), (zero_ne_one : (0 : ℂ) ≠ 1)⟩

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@norm_le_mul_prod.{u})
    (type_of% (realize signature (fun _ f z => f z) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Analytic.Hardy.FiniteBlaschkeBound.norm_le_mul_prod.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Hardy.FiniteBlaschkeBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ f z => f z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Hardy.FiniteBlaschkeBound
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Analytic.Hardy.FiniteBlaschkeBound
