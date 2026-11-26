import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.NonobtuseFamilyFixedVector
import Reg.Support.DependentFamily
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Source-bound audit of the fixed least-norm vector of a nonobtuse unit family. -/

namespace Reg.D5.S3.Quantum.AURICOmega.NonobtuseFamilyFixedVector

open _root_.D5.S3.Quantum.AURICOmega.NonobtuseFamilyFixedVector
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section
universe u

/-- The one-dimensional Euclidean line in universe `u`. -/
abbrev Line : Type u := EuclideanSpace ℝ (ULift.{u} Unit)

/-- The unit vector of the line. -/
def unitVector : Line.{u} := EuclideanSpace.single ⟨()⟩ 1

theorem norm_unitVector : ‖unitVector.{u}‖ = 1 := by
  rw [unitVector, PiLp.norm_single, norm_one]

theorem unitVector_ne_zero : unitVector.{u} ≠ 0 := by
  intro h
  have hn := norm_unitVector.{u}
  rw [h, norm_zero] at hn
  norm_num at hn

/-! The symmetry applied to the least-norm point, for
`exists_fixed_ne_zero_of_pairwise_inner_nonneg`. -/
namespace FixedPoint

abbrev signature : Signature where
  Params := Σ E : Type u, Σ _ : NormedAddCommGroup E, Σ _ : InnerProductSpace ℝ E, E ≃ₗᵢ[ℝ] E
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature
    (fun _ p s => letI := p.2.1; letI := p.2.2.1; p.2.2.2 s) (fun e => nomatch e)

def zero : Realization signature.{u} :=
  realize signature (fun _ p _ => letI := p.2.1; (0 : p.1)) (fun e => nomatch e)

/-- Retain the complete space, family and hypothesis telescope of
`exists_fixed_ne_zero_of_pairwise_inner_nonneg`. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {E : Type u} [g : NormedAddCommGroup E] [i : InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (S : Set E), S.Nonempty → (∀ s ∈ S, ‖s‖ = 1) →
    (∀ s ∈ S, ∀ t ∈ S, 0 ≤ ⟪s, t⟫_ℝ) →
    ∃ m : E, m ≠ 0 ∧ m ∈ closure (convexHull ℝ S) ∧
      (∀ x ∈ closure (convexHull ℝ S), ‖m‖ ≤ ‖x‖) ∧
      (∀ x ∈ closure (convexHull ℝ S), ‖m‖ ^ 2 ≤ ⟪x, m⟫_ℝ) ∧
      (∀ U : E ≃ₗᵢ[ℝ] E, U '' S ⊆ S → r.readout () ⟨E, g, i, U⟩ m = m)

theorem rejected_law : ¬ arena.{u}.Law zero := by
  intro h
  obtain ⟨m, hm0, -, -, -, hfix⟩ := h ({unitVector.{u}} : Set Line.{u})
    (Set.singleton_nonempty _)
    (fun s hs => by rw [Set.mem_singleton_iff.mp hs]; exact norm_unitVector)
    (fun s _ t _ => by
      rw [Set.mem_singleton_iff.mp ‹s ∈ _›, Set.mem_singleton_iff.mp ‹t ∈ _›]
      exact real_inner_self_nonneg)
  have h0 : (0 : Line.{u}) = m :=
    hfix (LinearIsometryEquiv.refl ℝ Line.{u}) (by simp)
  exact hm0 h0.symm

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨Line.{u}, inferInstance, inferInstance, LinearIsometryEquiv.refl ℝ Line.{u}⟩,
    unitVector, 0, ?_⟩
  exact unitVector_ne_zero

def source_registration :
    Registration arena.{u}
      (type_of% @exists_fixed_ne_zero_of_pairwise_inner_nonneg.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_fixed_ne_zero_of_pairwise_inner_nonneg.{u}, zero, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨zero, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end FixedPoint

def exists_fixed_ne_zero_of_pairwise_inner_nonneg_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_fixed_ne_zero_of_pairwise_inner_nonneg.{u})
      (Realization FixedPoint.signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.NonobtuseFamilyFixedVector.exists_fixed_ne_zero_of_pairwise_inner_nonneg_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.NonobtuseFamilyFixedVector.FixedPoint.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨FixedPoint.arena.{u}⟩
  objectArena := .source ⟨FixedPoint.arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source FixedPoint.arena.{u} ⟨FixedPoint.source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize FixedPoint.signature.{u}
      (fun _ p s => letI := p.2.1; letI := p.2.2.1; p.2.2.2 s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.NonobtuseFamilyFixedVector
    definition := none
    coordinates := #[0, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg", "arg", "arg", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.AURICOmega.NonobtuseFamilyFixedVector
