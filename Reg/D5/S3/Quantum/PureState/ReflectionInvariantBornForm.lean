import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.PureState.ReflectionInvariantBornForm
import Reg.Support.DependentFamily
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Source-bound audit of the Born form obtained from one reflection.
The readout is the Born weight `‖⟪φ, ψ⟫‖ ^ 2` on the right of the conclusion, as a function of
`ψ` at a fixed space and vector `φ`; the reading and all five hypotheses on it stay in the law
verbatim. The Born weight itself satisfies the five
hypotheses on a complex line, which refutes the zero readout. -/

namespace Reg.D5.S3.Quantum.PureState.ReflectionInvariantBornForm

open _root_.D5.S3.Quantum.PureState.ReflectionInvariantBornForm
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

/-! ## The Born weight satisfies the five hypotheses -/

section BornWeight
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem inner_self_of_norm_one {φ : E} (hφ : ‖φ‖ = 1) : ⟪φ, φ⟫_ℂ = 1 := by
  rw [inner_self_eq_norm_sq_to_K, hφ]
  simp

theorem born_smul (φ : E) (c : ℂ) (ψ : E) :
    ‖⟪φ, c • ψ⟫_ℂ‖ ^ 2 = ‖c‖ ^ 2 * ‖⟪φ, ψ⟫_ℂ‖ ^ 2 := by
  rw [inner_smul_right, norm_mul, mul_pow]

theorem born_parallelogram (φ ψ χ : E) :
    ‖⟪φ, ψ + χ⟫_ℂ‖ ^ 2 + ‖⟪φ, ψ - χ⟫_ℂ‖ ^ 2 = 2 * ‖⟪φ, ψ⟫_ℂ‖ ^ 2 + 2 * ‖⟪φ, χ⟫_ℂ‖ ^ 2 := by
  rw [inner_add_right, inner_sub_right]
  have h := parallelogram_law_with_norm ℂ ⟪φ, ψ⟫_ℂ ⟪φ, χ⟫_ℂ
  nlinarith [h]

theorem born_reflection (φ ψ : E) (hφ : ‖φ‖ = 1) :
    ‖⟪φ, (2 * ⟪φ, ψ⟫_ℂ) • φ - ψ⟫_ℂ‖ ^ 2 = ‖⟪φ, ψ⟫_ℂ‖ ^ 2 := by
  rw [inner_sub_right, inner_smul_right, inner_self_of_norm_one hφ]
  congr 2
  ring

theorem born_self (φ : E) (hφ : ‖φ‖ = 1) : ‖⟪φ, φ⟫_ℂ‖ ^ 2 = 1 := by
  rw [inner_self_of_norm_one hφ]
  simp

end BornWeight

/-! ## A complex line in universe `u` -/

/-- The one-dimensional complex Euclidean space in universe `u`. -/
abbrev Line : Type u := EuclideanSpace ℂ (ULift.{u} Unit)

/-- The unit vector of the line. -/
def unitVector : Line.{u} := EuclideanSpace.single ⟨()⟩ 1

theorem norm_unitVector : ‖unitVector.{u}‖ = 1 := by
  rw [unitVector, PiLp.norm_single, norm_one]

namespace BornWeight

abbrev signature : Signature where
  Params := Σ E : Type u, Σ _ : NormedAddCommGroup E, Σ _ : InnerProductSpace ℂ E, E
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature
    (fun _ p ψ => letI := p.2.1; letI := p.2.2.1; ‖⟪p.2.2.2, ψ⟫_ℂ‖ ^ 2) (fun e => nomatch e)

def zero : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the complete space, reading and hypothesis telescope of
`eq_norm_inner_sq_of_reflection_invariant`; only the Born weight is read out. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {E : Type u} [g : NormedAddCommGroup E] [i : InnerProductSpace ℂ E]
    (φ : E) (f : E → ℝ),
    (∀ (c : ℂ) (ψ : E), f (c • ψ) = ‖c‖ ^ 2 * f ψ) →
    (∀ (z : ℂ) (w : E), ⟪φ, w⟫_ℂ = 0 →
      f (z • φ + w) + f (z • φ - w) = 2 * f (z • φ) + 2 * f w) →
    (∀ ψ : E, ‖ψ‖ = 1 → f ((2 * ⟪φ, ψ⟫_ℂ) • φ - ψ) = f ψ) →
    f φ = 1 →
    (∀ ψ : E, ‖ψ‖ = 1 → ⟪φ, ψ⟫_ℂ = 0 → f ψ = 0) →
    ∀ ψ : E, f ψ = r.readout () ⟨E, g, i, φ⟩ ψ

theorem rejected_law : ¬ arena.{u}.Law zero := by
  intro h
  have hh := h (E := Line.{u}) unitVector
    (fun ψ => ‖⟪unitVector.{u}, ψ⟫_ℂ‖ ^ 2)
    (fun c ψ => born_smul unitVector c ψ)
    (fun z w _ => born_parallelogram unitVector (z • unitVector) w)
    (fun ψ _ => born_reflection unitVector ψ norm_unitVector)
    (born_self unitVector norm_unitVector)
    (fun ψ _ h0 => by simp only [h0, norm_zero]; norm_num)
    unitVector
  rw [born_self _ norm_unitVector] at hh
  exact one_ne_zero hh

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨Line.{u}, inferInstance, inferInstance, unitVector⟩, unitVector, 0, ?_⟩
  change ‖⟪unitVector.{u}, unitVector.{u}⟫_ℂ‖ ^ 2 ≠ ‖⟪unitVector.{u}, (0 : Line.{u})⟫_ℂ‖ ^ 2
  rw [born_self _ norm_unitVector, inner_zero_right]
  norm_num

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @eq_norm_inner_sq_of_reflection_invariant.{u}

def source_registration : Registration arena.{u} sourceStatement.{u} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@eq_norm_inner_sq_of_reflection_invariant.{u}, zero, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨zero, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end BornWeight

def eq_norm_inner_sq_of_reflection_invariant_registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@eq_norm_inner_sq_of_reflection_invariant.{u})
      (Realization BornWeight.signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.PureState.ReflectionInvariantBornForm.BornWeight.unit
  realizationName :=
    `Reg.D5.S3.Quantum.PureState.ReflectionInvariantBornForm.BornWeight.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨BornWeight.arena.{u}⟩
  objectArena := .source ⟨BornWeight.arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source BornWeight.arena.{u} ⟨BornWeight.source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize BornWeight.signature.{u}
      (fun _ p ψ => letI := p.2.1; letI := p.2.2.1; ‖⟪p.2.2.2, ψ⟫_ℂ‖ ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.PureState.ReflectionInvariantBornForm
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.PureState.ReflectionInvariantBornForm
