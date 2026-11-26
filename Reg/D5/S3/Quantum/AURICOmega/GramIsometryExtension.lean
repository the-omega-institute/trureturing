import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.GramIsometryExtension
import Reg.Support.DependentFamily
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Source-bound audit of the isometric extension of Gram-preserving permutations. -/

namespace Reg.D5.S3.Quantum.AURICOmega.GramIsometryExtension

open _root_.D5.S3.Quantum.AURICOmega.GramIsometryExtension
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section
universe u v

/-- The one-dimensional Euclidean line in universe `v`. -/
abbrev Line : Type v := EuclideanSpace ℝ (ULift.{v} Unit)

/-- The unit vector of the line. -/
def unitVector : Line.{v} := EuclideanSpace.single ⟨()⟩ 1

theorem unitVector_ne_zero : unitVector.{v} ≠ 0 := by
  intro h
  have hn := congrArg norm h
  rw [unitVector, PiLp.norm_single, norm_zero] at hn
  norm_num at hn

/-- The family `true ↦ e`, `false ↦ -e` on the line. -/
def signFamily (b : ULift.{u} Bool) : Line.{v} := if b.down then unitVector else -unitVector

/-- The exchange of the two indices. -/
def flip : Equiv.Perm (ULift.{u} Bool) where
  toFun b := ⟨!b.down⟩
  invFun b := ⟨!b.down⟩
  left_inv b := by cases b with | up b => cases b <;> rfl
  right_inv b := by cases b with | up b => cases b <;> rfl

theorem signFamily_flip (b : ULift.{u} Bool) :
    signFamily.{u, v} (flip b) = -signFamily.{u, v} b := by
  cases b with
  | up b => cases b <;> simp [signFamily, flip]

theorem signFamily_span : Submodule.span ℝ (Set.range signFamily.{u, v}) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  have hx : x = x ⟨()⟩ • unitVector.{v} := by
    ext j
    cases j
    simp [unitVector]
  rw [hx]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨true⟩, rfl⟩)

theorem signFamily_gram (a b : ULift.{u} Bool) :
    ⟪signFamily.{u, v} (flip a), signFamily.{u, v} (flip b)⟫_ℝ =
      ⟪signFamily.{u, v} a, signFamily.{u, v} b⟫_ℝ := by
  rw [signFamily_flip, signFamily_flip, inner_neg_neg]

/-! The isometry applied to a family member, for
`existsUnique_linearIsometryEquiv_of_gram_preserving`. -/
namespace Extension

abbrev signature : Signature where
  Params := Σ E : Type v, Σ _ : NormedAddCommGroup E, Σ _ : InnerProductSpace ℝ E, E ≃ₗᵢ[ℝ] E
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature
    (fun _ p s => letI := p.2.1; letI := p.2.2.1; p.2.2.2 s) (fun e => nomatch e)

def identity : Realization signature.{v} :=
  realize signature (fun _ _ s => s) (fun e => nomatch e)

/-- Retain the complete index, space, family and permutation telescope of
`existsUnique_linearIsometryEquiv_of_gram_preserving`. -/
abbrev arena : Arena where
  signature := signature.{v}
  Law r := ∀ {ι : Type u} {E : Type v} [g : NormedAddCommGroup E] [i : InnerProductSpace ℝ E]
    (φ : ι → E), Submodule.span ℝ (Set.range φ) = ⊤ → ∀ σ : Equiv.Perm ι,
    (∀ a b : ι, ⟪φ (σ a), φ (σ b)⟫_ℝ = ⟪φ a, φ b⟫_ℝ) →
    ∃! U : E ≃ₗᵢ[ℝ] E, ∀ a : ι, r.readout () ⟨E, g, i, U⟩ (φ a) = φ (σ a)

theorem rejected_law : ¬ arena.{u, v}.Law identity := by
  intro h
  obtain ⟨U, hU, -⟩ := h signFamily.{u, v} signFamily_span flip signFamily_gram
  have hh : signFamily.{u, v} ⟨true⟩ = signFamily.{u, v} (flip ⟨true⟩) := hU ⟨true⟩
  rw [signFamily_flip] at hh
  change unitVector.{v} = -unitVector.{v} at hh
  have h2 : (2 : ℝ) • unitVector.{v} = 0 := by
    rw [two_smul]
    nth_rewrite 1 [hh]
    exact neg_add_cancel _
  exact unitVector_ne_zero ((smul_eq_zero.mp h2).resolve_left two_ne_zero)

theorem dependence : ObservationalDependence signature.{v} actual := by
  intro i
  refine ⟨⟨Line.{v}, inferInstance, inferInstance, LinearIsometryEquiv.refl ℝ Line.{v}⟩,
    unitVector, 0, ?_⟩
  exact unitVector_ne_zero

def source_registration :
    Registration arena.{u, v}
      (type_of% @existsUnique_linearIsometryEquiv_of_gram_preserving.{u, v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@existsUnique_linearIsometryEquiv_of_gram_preserving.{u, v}, identity,
    rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨identity, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Extension

def existsUnique_linearIsometryEquiv_of_gram_preserving_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@existsUnique_linearIsometryEquiv_of_gram_preserving.{u, v})
      (Realization Extension.signature.{v}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.GramIsometryExtension.existsUnique_linearIsometryEquiv_of_gram_preserving_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.GramIsometryExtension.Extension.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Extension.arena.{u, v}⟩
  objectArena := .source ⟨Extension.arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Extension.arena.{u, v} ⟨Extension.source_registration.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize Extension.signature.{v}
      (fun _ p s => letI := p.2.1; letI := p.2.2.1; p.2.2.2 s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.GramIsometryExtension
    definition := none
    coordinates := #[1, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.AURICOmega.GramIsometryExtension
