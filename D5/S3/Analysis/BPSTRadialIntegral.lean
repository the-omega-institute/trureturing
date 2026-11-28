/- GID: D5/S3/Analysis/BPSTRadialIntegral
   generality: G
   mirror-B: none(waiver:covered-by-yang-mills-bpsself-dual4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The rational radial integral for the four-dimensional instanton profile. -/

import OmegaBuild.Commands
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Omega original.

The rational radial integral for the four-dimensional instanton profile.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace Omega

/-- The four-dimensional radial integral is independent of the positive scale. -/
theorem bpst_radial_integral {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn (fun r : ℝ ↦ ρ ^ 4 * r ^ 3 / (r ^ 2 + ρ ^ 2) ^ 4) (Ioi 0) ∧
      (∫ r in Ioi (0 : ℝ), ρ ^ 4 * r ^ 3 / (r ^ 2 + ρ ^ 2) ^ 4) = 1 / 12 := by
  let f : ℝ → ℝ := fun r ↦ ρ ^ 4 * r ^ 3 / (r ^ 2 + ρ ^ 2) ^ 4
  let g : ℝ → ℝ := fun r ↦ -(ρ ^ 4 / 4) / (r ^ 2 + ρ ^ 2) ^ 2 +
    (ρ ^ 6 / 6) / (r ^ 2 + ρ ^ 2) ^ 3
  have hd (r : ℝ) (_ : r ∈ Ici (0 : ℝ)) : HasDerivAt g (f r) r := by
    have hp : 0 < r ^ 2 + ρ ^ 2 := by positivity
    have h := ((hasDerivAt_id r).pow 2).add_const (ρ ^ 2)
    have h₁ := (hasDerivAt_const r (-(ρ ^ 4 / 4))).div (h.pow 2) (pow_ne_zero _ hp.ne')
    have h₂ := (hasDerivAt_const r (ρ ^ 6 / 6)).div (h.pow 3) (pow_ne_zero _ hp.ne')
    convert h₁.add h₂ using 1 <;> try rfl
    norm_num [f, Pi.pow_apply]
    field_simp
    ring
  have hn (r : ℝ) (hr : r ∈ Ioi (0 : ℝ)) : 0 ≤ f r := by
    have : 0 ≤ r := hr.le
    dsimp [f]
    positivity
  have ht : Tendsto (fun r : ℝ ↦ r ^ 2 + ρ ^ 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_pow_atTop (by decide))
  have hlim : Tendsto g atTop (𝓝 0) := by
    have h₂ := tendsto_const_nhds (x := -(ρ ^ 4 / 4)) |>.div_atTop
      ((tendsto_pow_atTop (n := 2) (by decide)).comp ht)
    have h₃ := tendsto_const_nhds (x := ρ ^ 6 / 6) |>.div_atTop
      ((tendsto_pow_atTop (n := 3) (by decide)).comp ht)
    simpa [g, Function.comp_def] using h₂.add h₃
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hn hlim, ?_⟩
  change (∫ r in Ioi (0 : ℝ), f r) = _
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd hn hlim]
  dsimp [g]
  field_simp
  ring

end Omega
