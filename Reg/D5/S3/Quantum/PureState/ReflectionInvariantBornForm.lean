import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.PureState.ReflectionInvariantBornForm
import Reg.Support.DependentFamily
import Reg.Support.RealScalarLift

/-! Source-bound audit of the Born form obtained from one reflection.
The readout is the Born weight `‖⟪φ, ψ⟫‖ ^ 2` on the right of the conclusion, as a function of
`ψ` at a fixed scalar field, space and vector `φ`; the reading and all five hypotheses on it stay
in the law verbatim. The Born weight itself satisfies the five hypotheses on the real line,
which refutes the zero readout. -/

namespace Reg.D5.S3.Quantum.PureState.ReflectionInvariantBornForm

open _root_.D5.S3.Quantum.PureState.ReflectionInvariantBornForm
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section
universe u v

/-! ## The Born weight satisfies the five hypotheses -/

section BornWeight
variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

theorem inner_self_of_norm_one {φ : E} (hφ : ‖φ‖ = 1) : ⟪φ, φ⟫_𝕜 = 1 := by
  rw [inner_self_eq_norm_sq_to_K, hφ]
  simp

theorem born_smul (φ : E) (c : 𝕜) (ψ : E) :
    ‖⟪φ, c • ψ⟫_𝕜‖ ^ 2 = ‖c‖ ^ 2 * ‖⟪φ, ψ⟫_𝕜‖ ^ 2 := by
  rw [inner_smul_right, norm_mul, mul_pow]

theorem born_parallelogram (φ ψ χ : E) :
    ‖⟪φ, ψ + χ⟫_𝕜‖ ^ 2 + ‖⟪φ, ψ - χ⟫_𝕜‖ ^ 2 = 2 * ‖⟪φ, ψ⟫_𝕜‖ ^ 2 + 2 * ‖⟪φ, χ⟫_𝕜‖ ^ 2 := by
  rw [inner_add_right, inner_sub_right]
  have h := parallelogram_law_with_norm 𝕜 ⟪φ, ψ⟫_𝕜 ⟪φ, χ⟫_𝕜
  nlinarith [h]

theorem born_reflection (φ ψ : E) (hφ : ‖φ‖ = 1) :
    ‖⟪φ, (2 * ⟪φ, ψ⟫_𝕜) • φ - ψ⟫_𝕜‖ ^ 2 = ‖⟪φ, ψ⟫_𝕜‖ ^ 2 := by
  rw [inner_sub_right, inner_smul_right, inner_self_of_norm_one hφ]
  congr 2
  ring

theorem born_self (φ : E) (hφ : ‖φ‖ = 1) : ‖⟪φ, φ⟫_𝕜‖ ^ 2 = 1 := by
  rw [inner_self_of_norm_one hφ]
  simp

end BornWeight

/-! ## The real line as a model in arbitrary universes -/

/-- The real numbers lifted to universe `u`, with the shared `RCLike` structure. -/
abbrev LiftReal : Type u := ULift.{u} ℝ

/-- The real line lifted to universe `v`, an inner product space over `LiftReal`. -/
abbrev Line : Type v := ULift.{v} ℝ

/-- The unit vector `1` of the line. -/
def unitVector : Line.{v} := ⟨1⟩

theorem norm_unitVector : ‖unitVector.{v}‖ = 1 := by
  change ‖(1 : ℝ)‖ = 1
  exact norm_one

namespace BornWeight

set_option linter.checkUnivs false in
abbrev signature : Signature where
  Params := Σ 𝕜 : Type u, Σ E : Type v, Σ _ : RCLike 𝕜, Σ _ : NormedAddCommGroup E,
    Σ _ : InnerProductSpace 𝕜 E, E
  State p := p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u, v} :=
  realize signature
    (fun _ p ψ => letI := p.2.2.1; letI := p.2.2.2.1; letI := p.2.2.2.2.1;
      ‖inner p.1 p.2.2.2.2.2 ψ‖ ^ 2) (fun e => nomatch e)

def zero : Realization signature.{u, v} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

set_option linter.checkUnivs false in
/-- Retain the complete scalar field, space, reading and hypothesis telescope of
`eq_norm_inner_sq_of_reflection_invariant`; only the Born weight is read out. -/
abbrev arena : Arena where
  signature := signature.{u, v}
  Law r := ∀ {𝕜 : Type u} {E : Type v} [i1 : RCLike 𝕜] [i2 : NormedAddCommGroup E]
    [i3 : InnerProductSpace 𝕜 E] (φ : E) (f : E → ℝ),
    (∀ (c : 𝕜) (ψ : E), f (c • ψ) = ‖c‖ ^ 2 * f ψ) →
    (∀ w : E, ⟪φ, w⟫_𝕜 = 0 → f (φ + w) + f (φ - w) = 2 * f φ + 2 * f w) →
    (∀ ψ : E, ‖ψ‖ = 1 → f ((2 * ⟪φ, ψ⟫_𝕜) • φ - ψ) = f ψ) →
    f φ = 1 →
    (∀ ψ : E, ‖ψ‖ = 1 → ⟪φ, ψ⟫_𝕜 = 0 → f ψ = 0) →
    ∀ ψ : E, f ψ = r.readout () ⟨𝕜, E, i1, i2, i3, φ⟩ ψ

/-- On the real line the Born weight satisfies the five hypotheses and is one at the unit
vector, so the zero readout is not lawful. -/
theorem rejected_law : ¬ arena.{u, v}.Law zero := by
  intro h
  have hh := h (𝕜 := LiftReal.{u}) (E := Line.{v}) unitVector
    (fun ψ => ‖⟪unitVector.{v}, ψ⟫_(LiftReal.{u})‖ ^ 2)
    (fun c ψ => born_smul unitVector c ψ)
    (fun w _ => born_parallelogram unitVector unitVector w)
    (fun ψ _ => born_reflection unitVector ψ norm_unitVector)
    (born_self unitVector norm_unitVector)
    (fun ψ _ h0 => by simp only [h0, norm_zero]; norm_num)
    unitVector
  rw [born_self _ norm_unitVector] at hh
  exact one_ne_zero hh

theorem dependence : ObservationalDependence signature.{u, v} actual := by
  intro i
  refine ⟨⟨LiftReal.{u}, Line.{v}, inferInstance, inferInstance, inferInstance, unitVector⟩,
    unitVector, 0, ?_⟩
  change ‖⟪unitVector.{v}, unitVector.{v}⟫_(LiftReal.{u})‖ ^ 2
    ≠ ‖⟪unitVector.{v}, (0 : Line.{v})⟫_(LiftReal.{u})‖ ^ 2
  rw [born_self _ norm_unitVector, inner_zero_right]
  norm_num

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @eq_norm_inner_sq_of_reflection_invariant.{u, v}

def source_registration : Registration arena.{u, v} sourceStatement.{u, v} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@eq_norm_inner_sq_of_reflection_invariant.{u, v}, zero, rejected_law⟩
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
      (@eq_norm_inner_sq_of_reflection_invariant.{u, v})
      (Realization BornWeight.signature.{u, v}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.PureState.ReflectionInvariantBornForm.BornWeight.unit
  realizationName :=
    `Reg.D5.S3.Quantum.PureState.ReflectionInvariantBornForm.BornWeight.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨BornWeight.arena.{u, v}⟩
  objectArena := .source ⟨BornWeight.arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source BornWeight.arena.{u, v} ⟨BornWeight.source_registration.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize BornWeight.signature.{u, v}
      (fun _ p ψ => letI := p.2.2.1; letI := p.2.2.2.1; letI := p.2.2.2.2.1;
        ‖inner p.1 p.2.2.2.2.2 ψ‖ ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.PureState.ReflectionInvariantBornForm
    definition := none
    coordinates := #[0, 1, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg"]
      stateBinder := 12
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.PureState.ReflectionInvariantBornForm
