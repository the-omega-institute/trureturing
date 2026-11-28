/- GID: D5/S3/Analysis/SymmetricAngleCoordinates
   generality: G
   mirror-B: none(waiver:covered-by-penrose-carter-causal-compactification4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Symmetric angle coordinates and the difference of squares of their tangent derivatives. -/

import OmegaBuild.Commands
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Omega original.

Symmetric angle coordinates and the difference of squares of their tangent
derivatives. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Real Filter
open scoped Topology

namespace OmegaMath.SymmetricAngleCoordinates

noncomputable section

def cosineSum (x y : ℝ) : ℝ := cos x + cos y

def sineQuotient (x y : ℝ) : ℝ := sin x / cosineSum x y

theorem half_angle_bounds {x y : ℝ} (hy : 0 ≤ y) (h : |x| + y < π) :
    -(π / 2) < (x + y) / 2 ∧ (x + y) / 2 < π / 2 ∧
    -(π / 2) < (x - y) / 2 ∧ (x - y) / 2 < π / 2 := by
  have h₁ := le_abs_self x
  have h₂ := neg_abs_le x
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem cosineSum_add_sub (a b : ℝ) :
    cosineSum (a + b) (a - b) = 2 * cos a * cos b := by
  simp only [cosineSum, cos_add, cos_sub]
  ring

theorem sineQuotient_add_sub {a b : ℝ} (ha : cos a ≠ 0) (hb : cos b ≠ 0) :
    sineQuotient (a + b) (a - b) = (tan a + tan b) / 2 ∧
    sineQuotient (a - b) (a + b) = (tan a - tan b) / 2 := by
  have hs : cosineSum (a - b) (a + b) = cosineSum (a + b) (a - b) := by
    simp [cosineSum, add_comm]
  simp only [sineQuotient, hs, cosineSum_add_sub, sin_add, sin_sub, tan_eq_sin_div_cos]
  constructor <;> field_simp

theorem symmetric_derivative_difference {x y : ℝ → ℝ} {s dx dy : ℝ}
    (hx : HasDerivAt x dx s) (hy : HasDerivAt y dy s)
    (hy₀ : 0 ≤ y s) (h : |x s| + y s < π) (w : ℝ) :
    -deriv (fun u => sineQuotient (x u) (y u)) s ^ 2 +
      deriv (fun u => sineQuotient (y u) (x u)) s ^ 2 +
      sineQuotient (y s) (x s) ^ 2 * w ^ 2 =
      (cosineSum (x s) (y s))⁻¹ ^ 2 * (-dx ^ 2 + dy ^ 2 + sin (y s) ^ 2 * w ^ 2) := by
  let p := fun u => (x u + y u) / 2
  let q := fun u => (x u - y u) / 2
  have hp : HasDerivAt p ((dx + dy) / 2) s := (hx.add hy).div_const 2
  have hq : HasDerivAt q ((dx - dy) / 2) s := (hx.sub hy).div_const 2
  have angles (u : ℝ) : p u + q u = x u ∧ p u - q u = y u := by
    dsimp [p, q]
    constructor <;> ring
  obtain ⟨ha, hb, hc, hd⟩ := half_angle_bounds hy₀ h
  have cp : 0 < cos (p s) := cos_pos_of_mem_Ioo ⟨ha, hb⟩
  have cq : 0 < cos (q s) := cos_pos_of_mem_Ioo ⟨hc, hd⟩
  have hcp : ∀ᶠ u in 𝓝 s, cos (p u) ≠ 0 :=
    (continuous_cos.continuousAt.comp hp.continuousAt).eventually_ne cp.ne'
  have hcq : ∀ᶠ u in 𝓝 s, cos (q u) ≠ 0 :=
    (continuous_cos.continuousAt.comp hq.continuousAt).eventually_ne cq.ne'
  have h := (hcp.and hcq).mono (fun u h => by
    have he := sineQuotient_add_sub h.1 h.2
    rw [(angles u).1, (angles u).2] at he
    exact he)
  have hd₁ := (hasDerivAt_tan cp.ne').comp s hp
  have hd₂ := (hasDerivAt_tan cq.ne').comp s hq
  have ht := ((hd₁.add hd₂).div_const 2).congr_of_eventuallyEq (h.mono fun _ h => h.1)
  have hr := ((hd₁.sub hd₂).div_const 2).congr_of_eventuallyEq (h.mono fun _ h => h.2)
  have hf := cosineSum_add_sub (p s) (q s)
  rw [(angles s).1, (angles s).2] at hf
  have hf' : cosineSum (y s) (x s) = 2 * cos (p s) * cos (q s) :=
    (add_comm _ _).trans hf
  rw [ht.deriv, hr.deriv, sineQuotient, hf, hf']
  field_simp [cp.ne', cq.ne']
  ring

end
end OmegaMath.SymmetricAngleCoordinates
