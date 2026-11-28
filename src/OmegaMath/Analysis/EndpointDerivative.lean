import OmegaBuild.Commands
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Algebra.Order.Field

/-!
Omega original.

A reciprocal-square lower bound on a derivative rules out a finite endpoint limit.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set
open scoped Topology

namespace Omega

/-- A function whose derivative dominates a positive reciprocal square to the right of an
endpoint has no finite limit there. -/
theorem no_finite_limit_of_reciprocal_sq_le_deriv {a b c : ℝ} {F : ℝ → ℝ}
    (hab : a < b) (hc : 0 < c)
    (hF : ∀ x ∈ Ioc a b, DifferentiableAt ℝ F x)
    (hlower : ∀ x ∈ Ioo a b, c / (x - a) ^ 2 ≤ deriv F x) (v : ℝ) :
    ¬ Tendsto F (𝓝[>] a) (𝓝 v) := by
  intro hv
  let G := fun x : ℝ => F x + c / (x - a)
  have hG (x : ℝ) (hx : x ∈ Ioc a b) :
      HasDerivAt G (deriv F x - c / (x - a) ^ 2) x := by
    have hs : HasDerivAt (fun y => y - a) 1 x := (hasDerivAt_id x).sub_const a
    have hf := (hF x hx).hasDerivAt.add ((hasDerivAt_const x c).div hs (sub_pos.mpr hx.1).ne')
    convert hf using 1
    ring
  have hmono : MonotoneOn G (Ioc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioc _ _)
    · exact fun x hx => (hG x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      exact (hG x ⟨hx.1, hx.2.le⟩).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      rw [(hG x ⟨hx.1, hx.2.le⟩).deriv, sub_nonneg]
      exact hlower x hx
  have hright : Tendsto (fun x : ℝ => x - a) (𝓝[>] a) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using (tendsto_id.sub tendsto_const_nhds :
        Tendsto (fun x : ℝ => x - a) (𝓝 a) (𝓝 (a - a))).mono_left nhdsWithin_le_nhds
    · exact Filter.Eventually.mono self_mem_nhdsWithin fun x hx => sub_pos.mpr hx
  have hg : Tendsto G (𝓝[>] a) atTop := by
    simpa [G, div_eq_mul_inv] using
      hv.add_atTop ((tendsto_inv_nhdsGT_zero.comp hright).const_mul_atTop hc)
  have hnear : ∀ᶠ x in 𝓝[>] a, x ∈ Ioc a b := by
    filter_upwards [self_mem_nhdsWithin,
      (gt_mem_nhds hab).filter_mono nhdsWithin_le_nhds] with x hx hxb
    exact ⟨hx, hxb.le⟩
  have hcontra : ∀ᶠ x in 𝓝[>] a, False := by
    filter_upwards [hg.eventually_gt_atTop (G b), hnear] with x hx hx'
    exact (not_lt_of_ge (hmono hx' ⟨hab, le_rfl⟩ hx'.2)) hx
  exact (Filter.Eventually.exists hcontra).elim (fun _ h => h)

end Omega
