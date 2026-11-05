import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Interpolation.SublinearMomentGrowth
import Reg.Support.SingleDependentReadout

/-! Full-function source realization through the enrolled dependent-family template. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Finset Filter Real
open scoped BigOperators ComplexConjugate Topology

namespace Reg.D5.S3.Analytic.Interpolation.SublinearMomentGrowth

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.Interpolation.SublinearMomentGrowth
open LeanInformationAudit

/-- Observe the entire real function, so the original argument t and the full
family of hypotheses remain in the law. -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℝ → ℝ) (fun _ => ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ F => F) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun t : ℝ => exp (2 * |t|)) (fun e => nomatch e)

/-- All original binders and premises survive; only the concluded function
readout is varied. This is an actual source arena, not a Prop mirror. -/
def arena : Arena where
  signature := signature
  Law R := ∀ (F : ℝ → ℝ) (m : ℝ → ℕ),
    Continuous F →
    (∀ t : ℝ, F (-t) = F t) →
    (∀ᶠ D : ℝ in atTop, 1 ≤ m D) →
    Tendsto (fun D : ℝ => (m D : ℝ) / D) atTop (𝓝 0) →
    (∀ᶠ D : ℝ in atTop,
      ∀ (n : ℕ) (x : Fin n → ℝ) (a : Fin n → ℂ),
        (∀ i, 0 ≤ x i ∧ x i ≤ D) →
        (∀ r : ℕ, r < m D → ∑ i, a i * ((x i : ℂ) ^ r) = 0) →
        0 ≤ (∑ i, ∑ j, a i * conj (a j) * (F (x i - x j) : ℂ)).re) →
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ, |R.readout () () F t| ≤ C * exp (ε * |t|)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hm : ∀ᶠ D : ℝ in atTop, 1 ≤ (fun _ : ℝ => (1 : ℕ)) D :=
    Filter.Eventually.of_forall (fun _ => le_rfl)
  have hsub : Tendsto (fun D : ℝ => ((fun _ : ℝ => (1 : ℕ)) D : ℝ) / D)
      atTop (𝓝 0) := by
    simpa only [Nat.cast_one, one_div] using
      (tendsto_inv_atTop_zero : Tendsto (fun D : ℝ => D⁻¹) atTop (𝓝 0))
  have hpos : momentPositive (fun _ : ℝ => 0) (fun _ : ℝ => 1) := by
    apply Filter.Eventually.of_forall
    intro D n x a hx ha
    simp
  obtain ⟨C, hC, hb⟩ := h (fun _ => 0) (fun _ => 1) continuous_const
    (fun _ => rfl) hm hsub hpos 1 zero_lt_one
  have hh := hb (C + 1)
  change |exp (2 * |C + 1|)| ≤ C * exp (1 * |C + 1|) at hh
  rw [abs_of_pos (exp_pos _), abs_of_pos (by linarith : 0 < C + 1), one_mul] at hh
  have he : exp (2 * (C + 1)) = exp (C + 1) * exp (C + 1) := by
    rw [← exp_add]
    congr 1
    ring
  rw [he] at hh
  have hle : exp (C + 1) ≤ C := (mul_le_mul_iff_left₀ (exp_pos (C + 1))).mp hh
  linarith [add_one_le_exp (C + 1)]

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [actual, realize] at hh

def evidence : Registration arena (type_of% (@sublinear_moment_growth)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sublinear_moment_growth, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

/-- Four typed slots: the full theorem term, its realization type, and the
From/Residual carriers. Unknown is an honest residual, not an audit verdict. -/
def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@sublinear_moment_growth) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Interpolation.SublinearMomentGrowth.sublinear_moment_growth.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.SublinearMomentGrowth.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ F => F) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  /- Select the literal F operand inside the concluded |F t|. The first nine
     body steps cross F, m, hF, heven, hm, hsub, hpos, epsilon and its proof.
     Then enter Exists C, its body, the right conjunct, and forall t.
     F is lexical binder 0: both its state and output are the whole function.
     The selected operand is the complete function F. -/
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.SublinearMomentGrowth
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.Interpolation.SublinearMomentGrowth
