/- GID: D5/S3/Observer/HiddenFlow/VisibleHiddenProjectionCriteria
   generality: G
   mirror-B: D5/B/S3/Observer/HiddenFlow/VisibleHiddenProjectionCriteria
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complementary projections characterize invariant, coinvariant, and reducing subspaces, with a concrete asymmetric leakage witness. -/

import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.FinCases

/- Library-search audit trail (2026-08-24):
   * `rg -n -i 'invariant.*projection|coinvariant|reducing.*projection|QTP|PTQ'
     D5 Golden/Frozen/accepted` found no public or private declaration with the
     three projection criteria or the asymmetric witness below.
   * The seven existing modules in `D5/S3/Observer/HiddenFlow/` were checked;
     their digests concern flow rigidity, recurrent orbits, and hidden-address
     conservation, not complementary-subspace projection criteria.
   * Pinned Mathlib searches for `linearProjOfIsCompl`, `projectionOnto`,
     `IsIdempotentElem`, and invariant submodules found
     `Submodule.projection_apply_of_mem_left`,
     `Submodule.projection_apply_eq_zero_iff`,
     `Submodule.projection_eq_id_sub_projection`, and
     `LinearMap.IsIdempotentElem.range_mem_invtSubmodule_iff`.
   * Mathlib's invariant-range and invariant-kernel results are related but do
     not state the cross-block equations `QTP = 0` and `PTQ = 0`; the proofs
     below reuse the projection membership and kernel lemmas directly.
   * Repository-wide title-key searches for `invariant`, `coinvariant`, and
     `reducing` found only unrelated dynamics, observer, and number-theory uses.
 -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.HiddenFlow.VisibleHiddenProjectionCriteria

/-- The projection onto `V` along its chosen complement `R`. -/
noncomputable def visibleProjection {𝕜 E : Type*} [Field 𝕜]
    [AddCommGroup E] [Module 𝕜 E] (V R : Submodule 𝕜 E) (h : IsCompl V R) :
    Module.End 𝕜 E :=
  V.projection R h

/-- The complementary projection onto `R` along `V`; it equals `1 - P`. -/
noncomputable def hiddenProjection {𝕜 E : Type*} [Field 𝕜]
    [AddCommGroup E] [Module 𝕜 E] (V R : Submodule 𝕜 E) (h : IsCompl V R) :
    Module.End 𝕜 E :=
  R.projection V h.symm

/-- The hidden projection is algebraically the complement of the visible projection. -/
theorem hiddenProjection_eq_one_sub_visibleProjection
    {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (V R : Submodule 𝕜 E) (h : IsCompl V R) :
    hiddenProjection V R h = 1 - visibleProjection V R h := by
  rw [Module.End.one_eq_id]
  exact Submodule.projection_eq_id_sub_projection h

/-- A subspace is invariant when the endomorphism maps each of its vectors back into it. -/
def IsInvariant {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (T : Module.End 𝕜 E) (V : Submodule 𝕜 E) : Prop :=
  ∀ x ∈ V, T x ∈ V

/-- Both halves of a complementary decomposition are invariant under `T`. -/
def IsReducing {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (T : Module.End 𝕜 E) (V R : Submodule 𝕜 E) : Prop :=
  IsInvariant T V ∧ IsInvariant T R

/-- The visible subspace is invariant exactly when its visible-to-hidden block vanishes. -/
theorem visible_invariant_iff_hidden_visible_block_eq_zero
    {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (V R : Submodule 𝕜 E) (h : IsCompl V R) (T : Module.End 𝕜 E) :
    IsInvariant T V ↔
      hiddenProjection V R h ∘ₗ T ∘ₗ visibleProjection V R h = 0 := by
  constructor
  · intro hV
    ext x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    apply Submodule.projection_apply_of_mem_right h.symm
    exact hV _ (Submodule.projection_apply_mem h x)
  · intro hBlock x hx
    apply (Submodule.projection_apply_eq_zero_iff h.symm).mp
    have hAtX := LinearMap.congr_fun hBlock x
    simpa [visibleProjection, hiddenProjection,
      Submodule.projection_apply_of_mem_left h hx] using hAtX

/-- The hidden complement is invariant exactly when its hidden-to-visible block vanishes. -/
theorem hidden_invariant_iff_visible_hidden_block_eq_zero
    {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (V R : Submodule 𝕜 E) (h : IsCompl V R) (T : Module.End 𝕜 E) :
    IsInvariant T R ↔
      visibleProjection V R h ∘ₗ T ∘ₗ hiddenProjection V R h = 0 := by
  constructor
  · intro hR
    ext x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    apply Submodule.projection_apply_of_mem_right h
    exact hR _ (Submodule.projection_apply_mem h.symm x)
  · intro hBlock x hx
    apply (Submodule.projection_apply_eq_zero_iff h).mp
    have hAtX := LinearMap.congr_fun hBlock x
    simpa [visibleProjection, hiddenProjection,
      Submodule.projection_apply_of_mem_left h.symm hx] using hAtX

/-- A complementary decomposition reduces `T` exactly when both cross blocks vanish. -/
theorem reducing_iff_cross_projection_blocks_eq_zero
    {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (V R : Submodule 𝕜 E) (h : IsCompl V R) (T : Module.End 𝕜 E) :
    IsReducing T V R ↔
      visibleProjection V R h ∘ₗ T ∘ₗ hiddenProjection V R h = 0 ∧
        hiddenProjection V R h ∘ₗ T ∘ₗ visibleProjection V R h = 0 := by
  rw [IsReducing,
    visible_invariant_iff_hidden_visible_block_eq_zero V R h T,
    hidden_invariant_iff_visible_hidden_block_eq_zero V R h T]
  exact and_comm

/-- Coordinate projection onto the visible first axis of `Fin 2 → ℚ`. -/
def visibleCoordinateProjection : Module.End ℚ (Fin 2 → ℚ) :=
  (LinearMap.single ℚ (fun _ : Fin 2 => ℚ) 0).comp (LinearMap.proj 0)

/-- Coordinate projection onto the hidden second axis of `Fin 2 → ℚ`. -/
def hiddenCoordinateProjection : Module.End ℚ (Fin 2 → ℚ) :=
  (LinearMap.single ℚ (fun _ : Fin 2 => ℚ) 1).comp (LinearMap.proj 1)

/-- The square-zero update sending the visible first coordinate into the hidden second one. -/
def visibleToHiddenLeak : Module.End ℚ (Fin 2 → ℚ) :=
  (LinearMap.single ℚ (fun _ : Fin 2 => ℚ) 1).comp (LinearMap.proj 0)

/-- One-step visible descent does not prevent leakage from the visible axis into the hidden axis. -/
theorem visible_descent_does_not_prevent_hidden_leakage :
    visibleCoordinateProjection ∘ₗ visibleToHiddenLeak ∘ₗ
        hiddenCoordinateProjection = 0 ∧
      hiddenCoordinateProjection ∘ₗ visibleToHiddenLeak ∘ₗ
        visibleCoordinateProjection ≠ 0 := by
  constructor
  · ext x i
    fin_cases i <;>
      simp [visibleCoordinateProjection, hiddenCoordinateProjection,
        visibleToHiddenLeak]
  · intro hZero
    have hAtBasis := LinearMap.congr_fun hZero (Pi.single 0 (1 : ℚ))
    have hHiddenCoordinate := congrFun hAtBasis 1
    norm_num [visibleCoordinateProjection, hiddenCoordinateProjection,
      visibleToHiddenLeak] at hHiddenCoordinate

example :
    visibleCoordinateProjection + hiddenCoordinateProjection =
      LinearMap.id (R := ℚ) (M := Fin 2 → ℚ) := by
  ext x i
  fin_cases i <;>
    simp [visibleCoordinateProjection, hiddenCoordinateProjection]

#print axioms reducing_iff_cross_projection_blocks_eq_zero

end D5.S3.Observer.HiddenFlow.VisibleHiddenProjectionCriteria
