/- GID: D5/S3/Analysis/SquareSummableProjection
   generality: G
   mirror-B: none(waiver:covered-by-ccrfock-factor-disjointness-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coordinate projections on complex square-summable families indexed by any type. -/

import OmegaBuild.Commands
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic

/-! Omega original.
Coordinate projections on complex square-summable families indexed by any type. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped InnerProductSpace
open ContinuousLinearMap

namespace Omega.SquareSummableProjection

variable {J : Type*}

private abbrev Space (J : Type*) := lp (fun _ : J => ℂ) 2

theorem lp_sq {J : Type*} (x : lp (fun _ : J => ℂ) 2) :
    Summable (fun i => ‖x i‖ ^ 2) ∧ (∑' i, ‖x i‖ ^ 2) = ‖x‖ ^ 2 := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) x
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  exact ⟨h.summable, h.tsum_eq⟩

private def cutVector (P : J → Prop) (ψ : Space J) : Space J := by
  refine ⟨(fun α : J =>
    @ite ℂ (P α) (Classical.propDecidable _) (ψ α) 0), ?_⟩
  apply (memℓp_gen_iff (p := 2) (by norm_num)).mpr
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ (lp_sq ψ).1
  intro α
  split_ifs <;> simp

private theorem cutVector_apply (P : J → Prop) (ψ : Space J) (α : J) :
    cutVector P ψ α =
      @ite ℂ (P α) (Classical.propDecidable _) (ψ α) 0 := by
  unfold cutVector
  rfl

/-- Orthogonal coordinate projection on complex square-summable families. -/
def cut (P : J → Prop) : Space J →L[ℂ] Space J := by
  classical
  refine LinearMap.mkContinuous
    { toFun := cutVector P
      map_add' := fun ψ χ => lp.ext (funext fun α => by
        simp only [cutVector_apply, lp.coeFn_add, Pi.add_apply]; split_ifs <;> simp)
      map_smul' := fun c ψ => lp.ext (funext fun α => by
        simp only [cutVector_apply, lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
        split_ifs <;> simp) } 1 ?_
  intro ψ
  rw [one_mul]
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro α
  change ‖cutVector P ψ α‖ ≤ ‖ψ α‖
  rw [cutVector_apply]
  split_ifs <;> simp

theorem cut_apply (P : J → Prop) (ψ : Space J) (α : J) :
    cut P ψ α =
      @ite ℂ (P α) (Classical.propDecidable _) (ψ α) 0 :=
  cutVector_apply P ψ α

theorem inner_cut (P : J → Prop) (ψ : Space J) :
    ⟪ψ, cut P ψ⟫_ℂ = (‖cut P ψ‖ ^ 2 : ℝ) := by
  have he : ⟪cut P ψ, cut P ψ⟫_ℂ = (‖cut P ψ‖ ^ 2 : ℝ) := by
    rw [inner_self_eq_norm_sq_to_K]
    exact (map_pow Complex.ofRealHom _ _).symm
  rw [← he, lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  simp only [cut_apply, RCLike.inner_apply]
  split_ifs <;> simp

end Omega.SquareSummableProjection
