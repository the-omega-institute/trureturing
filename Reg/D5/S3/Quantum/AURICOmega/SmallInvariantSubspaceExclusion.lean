import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.SmallInvariantSubspaceExclusion
import Reg.Support.DependentFamily
import Mathlib.Analysis.Quaternion
import Mathlib.Analysis.CStarAlgebra.Basic

/-! Source-bound audit of the exclusion of small invariant subspaces.

The audited observation is the action `T x` inside the invariance hypothesis. The model used
for the rejected law is left multiplication by unit quaternions, carried to the Euclidean space
indexed by `ULift (Fin 4)`; it satisfies every hypothesis of the theorem simultaneously. -/

namespace Reg.D5.S3.Quantum.AURICOmega.SmallInvariantSubspaceExclusion

open _root_.D5.S3.Quantum.AURICOmega.SmallInvariantSubspaceExclusion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped Quaternion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section
universe u

/-- Left multiplication by a unit quaternion, as a linear isometry of `ℍ`. -/
def lmul (q : unitary ℍ[ℝ]) : ℍ[ℝ] ≃ₗᵢ[ℝ] ℍ[ℝ] where
  toFun v := (q : ℍ[ℝ]) * v
  invFun v := star (q : ℍ[ℝ]) * v
  map_add' a b := mul_add _ _ _
  map_smul' c a := by simp
  left_inv v := by
    change star (q : ℍ[ℝ]) * ((q : ℍ[ℝ]) * v) = v
    rw [← mul_assoc, Unitary.star_mul_self_of_mem q.prop, one_mul]
  right_inv v := by
    change (q : ℍ[ℝ]) * (star (q : ℍ[ℝ]) * v) = v
    rw [← mul_assoc, Unitary.mul_star_self_of_mem q.prop, one_mul]
  norm_map' v := by
    change ‖(q : ℍ[ℝ]) * v‖ = ‖v‖
    rw [norm_mul, CStarRing.norm_coe_unitary, one_mul]

/-- Euclidean four-space in universe `u`. -/
abbrev Space : Type u := EuclideanSpace ℝ (ULift.{u} (Fin 4))

/-- An orthonormal frame identifying `ℍ` with `Space`. -/
def frame : ℍ[ℝ] ≃ₗᵢ[ℝ] Space.{u} :=
  ((stdOrthonormalBasis ℝ ℍ[ℝ]).reindex
    ((finCongr Quaternion.finrank_eq_four).trans Equiv.ulift.symm)).repr

/-- Left multiplication by unit quaternions, read in the frame. -/
def leftAction : unitary ℍ[ℝ] →* (Space.{u} ≃ₗᵢ[ℝ] Space.{u}) where
  toFun q := frame.symm.trans ((lmul q).trans frame)
  map_one' := LinearIsometryEquiv.ext fun v => by
    change frame.{u} (((1 : unitary ℍ[ℝ]) : ℍ[ℝ]) * frame.{u}.symm v) = v
    rw [OneMemClass.coe_one, one_mul, LinearIsometryEquiv.apply_symm_apply]
  map_mul' a b := LinearIsometryEquiv.ext fun v => by
    change frame.{u} (((a * b : unitary ℍ[ℝ]) : ℍ[ℝ]) * frame.{u}.symm v) =
      frame.{u} ((a : ℍ[ℝ]) * frame.{u}.symm (frame.{u} ((b : ℍ[ℝ]) * frame.{u}.symm v)))
    rw [LinearIsometryEquiv.symm_apply_apply, Submonoid.coe_mul, mul_assoc]

theorem leftAction_apply (q : unitary ℍ[ℝ]) (v : Space.{u}) :
    leftAction q v = frame ((q : ℍ[ℝ]) * frame.symm v) := rfl

/-- The unit quaternion `i`. -/
def uI : unitary ℍ[ℝ] :=
  ⟨⟨0, 1, 0, 0⟩, Unitary.mem_iff.mpr ⟨by ext <;> simp, by ext <;> simp⟩⟩

/-- The unit quaternion `j`. -/
def uJ : unitary ℍ[ℝ] :=
  ⟨⟨0, 0, 1, 0⟩, Unitary.mem_iff.mpr ⟨by ext <;> simp, by ext <;> simp⟩⟩

theorem uI_mul_uI : uI * uI = -1 := by
  apply Subtype.ext
  change ((⟨0, 1, 0, 0⟩ : ℍ[ℝ]) * ⟨0, 1, 0, 0⟩) = -1
  ext <;> simp

theorem uI_ne_neg_one : uI ≠ -1 := by
  intro h
  have h1 := congrArg (fun q : unitary ℍ[ℝ] => (q : ℍ[ℝ]).re) h
  change (0 : ℝ) = ((-1 : unitary ℍ[ℝ]) : ℍ[ℝ]).re at h1
  rw [Unitary.coe_neg, OneMemClass.coe_one] at h1
  norm_num at h1

/-- The group of the model: all left multiplications by unit quaternions. -/
def group : Subgroup (Space.{u} ≃ₗᵢ[ℝ] Space.{u}) := leftAction.range

theorem frame_one_ne_zero : frame.{u} 1 ≠ 0 := by
  intro h
  exact one_ne_zero (frame.{u}.map_eq_zero_iff.mp h)

theorem group_finrank : Module.finrank ℝ Space.{u} ≤ 4 := by
  simp [Space, finrank_euclideanSpace]

theorem group_fix : ∀ v : Space.{u}, (∀ T ∈ group.{u}, T v = v) → v = 0 := by
  intro v hv
  have h := hv (leftAction (-1)) ⟨-1, rfl⟩
  rw [leftAction_apply, Unitary.coe_neg, OneMemClass.coe_one, neg_one_mul, map_neg,
    LinearIsometryEquiv.apply_symm_apply] at h
  have h2 : (2 : ℝ) • v = 0 := by
    rw [two_smul]; nth_rewrite 1 [← h]; exact neg_add_cancel v
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

theorem leftAction_no_neg (q : unitary ℍ[ℝ]) (hq : q ≠ -1) :
    ∀ v : Space.{u}, leftAction q v = -v → v = 0 := by
  intro v hv
  rw [leftAction_apply, ← LinearIsometryEquiv.eq_symm_apply, map_neg] at hv
  have hw : ((q : ℍ[ℝ]) + 1) * frame.symm v = 0 := by
    rw [add_mul, one_mul, hv, neg_add_cancel]
  rcases mul_eq_zero.mp hw with h | h
  · exfalso
    apply hq
    apply Subtype.ext
    rw [Unitary.coe_neg, OneMemClass.coe_one]
    exact eq_neg_of_add_eq_zero_left h
  · simpa using congrArg frame.{u} h

theorem group_gen :
    Subgroup.closure {T : Space.{u} ≃ₗᵢ[ℝ] Space.{u} |
      T ∈ group.{u} ∧ ∀ v : Space.{u}, T v = -v → v = 0} = group.{u} := by
  apply le_antisymm
  · exact (Subgroup.closure_le _).mpr fun T hT => hT.1
  · rintro _ ⟨q, rfl⟩
    have hgenI : leftAction.{u} uI ∈ Subgroup.closure {T : Space.{u} ≃ₗᵢ[ℝ] Space.{u} |
        T ∈ group.{u} ∧ ∀ v : Space.{u}, T v = -v → v = 0} :=
      Subgroup.subset_closure ⟨⟨uI, rfl⟩, leftAction_no_neg uI uI_ne_neg_one⟩
    by_cases hq : q = -1
    · subst hq
      rw [← uI_mul_uI, map_mul]
      exact Subgroup.mul_mem _ hgenI hgenI
    · exact Subgroup.subset_closure ⟨⟨q, rfl⟩, leftAction_no_neg q hq⟩

theorem group_noncomm : ∃ S ∈ group.{u}, ∃ T ∈ group.{u}, S * T ≠ T * S := by
  refine ⟨leftAction uI, ⟨uI, rfl⟩, leftAction uJ, ⟨uJ, rfl⟩, fun h => ?_⟩
  have h1 := congrArg
    (fun T : Space.{u} ≃ₗᵢ[ℝ] Space.{u} => (frame.{u}.symm (T (frame.{u} 1))).imK) h
  simp only [LinearIsometryEquiv.coe_mul, Function.comp_apply, leftAction_apply,
    LinearIsometryEquiv.symm_apply_apply, mul_one] at h1
  simp [uI, uJ] at h1
  norm_num at h1

/-- A line of `Space`; it is neither `⊥` nor `⊤`. -/
def line : Submodule ℝ Space.{u} := ℝ ∙ frame 1

theorem line_ne_bot : line.{u} ≠ ⊥ := by
  intro h
  exact frame_one_ne_zero ((Submodule.span_singleton_eq_bot).mp h)

theorem line_ne_top : line.{u} ≠ ⊤ := by
  intro h
  have h1 := finrank_span_singleton (K := ℝ) frame_one_ne_zero.{u}
  change Module.finrank ℝ line.{u} = 1 at h1
  rw [h, finrank_top] at h1
  simp [Space, finrank_euclideanSpace] at h1

/-! The action of a group element on a vector, against a fixed isometry. -/
namespace Action

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
  realize signature (fun _ p s => p.2.2.2 s) (fun e => nomatch e)

def identity : Realization signature.{u} :=
  realize signature (fun _ _ s => s) (fun e => nomatch e)

/-- Retain the complete space, group, hypothesis and subspace telescope of
`invariant_submodule_eq_bot_or_top`. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {E : Type u} [i₁ : NormedAddCommGroup E] [i₂ : InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (𝒰 : Subgroup (E ≃ₗᵢ[ℝ] E)),
    Module.finrank ℝ E ≤ 4 →
    (∀ v : E, (∀ T ∈ 𝒰, T v = v) → v = 0) →
    Subgroup.closure {T : E ≃ₗᵢ[ℝ] E | T ∈ 𝒰 ∧ ∀ v : E, T v = -v → v = 0} = 𝒰 →
    (∃ S ∈ 𝒰, ∃ T ∈ 𝒰, S * T ≠ T * S) →
    ∀ X : Submodule ℝ E,
      (∀ T ∈ 𝒰, ∀ x ∈ X, (r.readout () ⟨E, i₁, i₂, T⟩ x : E) ∈ X) →
      X = ⊥ ∨ X = ⊤

theorem rejected_law : ¬ arena.{u}.Law identity := by
  intro h
  rcases h group.{u} group_finrank group_fix group_gen group_noncomm line.{u}
      (fun _ _ _ hx => hx) with h | h
  · exact line_ne_bot h
  · exact line_ne_top h

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  refine ⟨⟨Space.{u}, inferInstance, inferInstance, LinearIsometryEquiv.refl ℝ Space.{u}⟩,
    0, frame 1, ?_⟩
  change (0 : Space.{u}) ≠ frame 1
  exact frame_one_ne_zero.symm

def source_registration :
    Registration arena.{u} (type_of% @invariant_submodule_eq_bot_or_top.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@invariant_submodule_eq_bot_or_top.{u}, identity, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨identity, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Action

def invariant_submodule_eq_bot_or_top_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@invariant_submodule_eq_bot_or_top.{u}) (Realization Action.signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.SmallInvariantSubspaceExclusion.invariant_submodule_eq_bot_or_top_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.SmallInvariantSubspaceExclusion.Action.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Action.arena.{u}⟩
  objectArena := .source ⟨Action.arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Action.arena.{u} ⟨Action.source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Action.signature.{u} (fun _ p s => p.2.2.2 s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.SmallInvariantSubspaceExclusion
    definition := none
    coordinates := #[0, 10]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "domain", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Quantum.AURICOmega.SmallInvariantSubspaceExclusion
