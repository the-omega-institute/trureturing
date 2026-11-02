/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Stop-Loss Function of a Measure on ℝ

Given a measure `μ` on ℝ and a threshold `z : ℝ`, the **stop-loss function** is

`stopLoss μ z = ∫ max (x - z) 0 ∂μ`.

The base definition is a totalized real-valued (Bochner) integral over an arbitrary `Measure ℝ`: It
carries no probability or integrability hypothesis, and because the real Bochner integral returns
`0` on non-integrable integrands, `stopLoss μ z` need not be the expected overshoot when
`x ↦ (x - z)⁺` is non-integrable. The probabilistic reading — the expected overshoot of a random
variable `X ∼ μ` above `z` — is justified by the later lemmas, which add the relevant
finite-measure and integrability hypotheses (`stopLoss_integrable`,
`mul_measureReal_Ici_le_stopLoss`).

Under those hypotheses the stop-loss plays a central role in the Hardy-Littlewood-Pólya
characterization of the convex order: `μ ≼cx ν ⟺ stopLoss μ z ≤ stopLoss ν z` pointwise (with equal
means). Its Legendre conjugate in `z` recovers the upper integrated quantile
`∫_t^1 q_μ(u) du = min_z { stopLoss μ z + z · (1 - t) }`.

## Main definitions

* `Measure.stopLoss μ z` — `∫ (x - z)⁺ ∂μ`.

## Main statements

* `Measure.stopLoss_nonneg` — non-negativity (unconditional).
* `Measure.stopLoss_integrable` — `(x - z)⁺` is integrable whenever `id` is.
* `Measure.mul_measureReal_Ici_le_stopLoss` — the Markov-type tail bound
  `(r - s) · μ[r, ∞) ≤ stopLoss μ s`.

## Tags

stop-loss, lower partial moment, convex order, tail bound
-/

@[expose] public section

open MeasureTheory Set Filter Topology

noncomputable section

namespace MeasureTheory.Measure

variable (μ : Measure ℝ)

/-- **Stop-loss function.** `stopLoss μ z = ∫ max (x - z) 0 ∂μ`, the totalized Bochner integral of
the hinge `(x - z)⁺` against an arbitrary measure `μ`. When `x ↦ (x - z)⁺` is `μ`-integrable (e.g.
`μ` a probability measure with finite first moment) this is the expected overshoot of `X ∼ μ` above
the threshold `z`; otherwise the Bochner integral returns `0`. -/
def stopLoss (z : ℝ) : ℝ := ∫ x, max (x - z) 0 ∂μ

variable {μ}

/-- Non-negativity of the stop-loss. -/
lemma stopLoss_nonneg (z : ℝ) : 0 ≤ stopLoss μ z :=
  integral_nonneg (fun _ => le_max_right _ _)

/-- If `x ↦ x` is `μ`-integrable (finite first moment), then `x ↦ max (x - z) 0` is integrable
too. -/
lemma stopLoss_integrable [IsFiniteMeasure μ] (hμ : Integrable (fun x : ℝ => x) μ) (z : ℝ) :
    Integrable (fun x : ℝ => max (x - z) 0) μ := by
  have h1 : Integrable (fun x : ℝ => x - z) μ := hμ.sub (integrable_const z)
  have h2 : Integrable (fun _ : ℝ => (0 : ℝ)) μ := integrable_const 0
  exact h1.sup h2

/-- **Markov-type tail bound through the stop-loss.** The hinge at `s` dominates the scaled
indicator of `[r, ∞)`, so `(r - s) · μ[r, ∞) ≤ stopLoss μ s`. (For `s ≥ r` the left side is
nonpositive and the bound is trivial.) -/
lemma mul_measureReal_Ici_le_stopLoss [IsFiniteMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (s r : ℝ) :
    (r - s) * μ.real (Ici r) ≤ μ.stopLoss s := by
  have hind : ∀ x : ℝ, (Ici r).indicator (fun _ => r - s) x ≤ max (x - s) 0 := by
    intro x
    by_cases hx : x ∈ Ici r
    · rw [indicator_of_mem hx]
      exact le_max_of_le_left (by linarith [mem_Ici.mp hx])
    · rw [indicator_of_notMem hx]
      exact le_max_right _ _
  have hind_int : Integrable ((Ici r).indicator fun _ : ℝ => r - s) μ :=
    (integrable_const (r - s)).indicator measurableSet_Ici
  calc (r - s) * μ.real (Ici r)
      = ∫ x, (Ici r).indicator (fun _ => r - s) x ∂μ := by
        rw [integral_indicator_const _ measurableSet_Ici, smul_eq_mul, mul_comm]
    _ ≤ μ.stopLoss s :=
        integral_mono hind_int (stopLoss_integrable hμ s) hind

end MeasureTheory.Measure

end
