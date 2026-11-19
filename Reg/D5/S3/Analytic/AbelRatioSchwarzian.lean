import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.AbelRatioSchwarzian
import Reg.Support.SingleDependentReadout

noncomputable section
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set
open scoped Topology

namespace Reg.D5.S3.Analytic.AbelRatioSchwarzian
open _root_.D5.S3.Analytic.AbelRatioSchwarzian

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ _ z => decide (z ≠ 0)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ z => false) (fun e => nomatch e)

/-- The complete original telescope and all conclusions; only the selected
native observation is varied. -/
def arena : Arena where
  signature := signature
  Law R := ∀ (U : Set ℂ) (hU : IsOpen U)
    (y p q W t : ℂ → ℂ)
    (hy : ∀ x ∈ U, DifferentiableAt ℂ y x ∧ DifferentiableAt ℂ (deriv y) x)
    (hy0 : ∀ x ∈ U, y x ≠ 0)
    (hp : ∀ x ∈ U, DifferentiableAt ℂ p x)
    (hW : ∀ x ∈ U, HasDerivAt W (-p x * W x) x)
    (hW0 : ∀ x ∈ U, W x ≠ 0)
    (ht : ∀ x ∈ U, HasDerivAt t (W x / y x ^ 2) x)
    (hODE : ∀ x ∈ U,
      deriv (deriv y) x + p x * deriv y x + q x * y x = 0)
    (x : ℂ) (hx : x ∈ U) ,
    R.readout () () (deriv t x) = true ∧
      HasDerivAt (deriv t)
        ((-p x - 2 * (deriv y x / y x)) * deriv t x) x ∧
      HasDerivAt (deriv (deriv t))
        ((-deriv p x - 2 * (-p x * (deriv y x / y x) - q x -
          (deriv y x / y x) ^ 2) + (-p x - 2 * (deriv y x / y x)) ^ 2) *
            deriv t x) x ∧
      preSchwarzian t x = -p x - 2 * (deriv y x / y x) ∧
      schwarzian t x = 2 * q x - deriv p x - (1 / 2 : ℂ) * p x ^ 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hy : ∀ x ∈ (univ : Set ℂ),
      DifferentiableAt ℂ (fun _ : ℂ => (1 : ℂ)) x ∧
      DifferentiableAt ℂ (deriv (fun _ : ℂ => (1 : ℂ))) x := by
    intro x _
    have he : deriv (fun _ : ℂ => (1 : ℂ)) = fun _ => 0 := by
      funext z
      simp
    rw [he]
    exact ⟨differentiableAt_const _, differentiableAt_const _⟩
  have hh := h univ isOpen_univ (fun _ => 1) (fun _ => 0) (fun _ => 0)
    (fun _ => 1) id hy
    (by intros; exact one_ne_zero)
    (by intros; exact differentiableAt_const _)
    (by intro x _; simpa using hasDerivAt_const x (1 : ℂ))
    (by intros; exact one_ne_zero)
    (by intro x _; simpa using hasDerivAt_id x)
    (by intros; simp) 0 (mem_univ _)
  simpa [rejected, realize] using hh.1


private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% @abel_ratio_schwarzian) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq] using @abel_ratio_schwarzian,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@abel_ratio_schwarzian) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.AbelRatioSchwarzian.unit
  realizationName := `Reg.D5.S3.Analytic.AbelRatioSchwarzian.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => decide (z ≠ 0)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.AbelRatioSchwarzian
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.AbelRatioSchwarzian
