/- GID: D5/S3/Zeros/GapClosingExponent
   generality: G
   mirror-B: D5/B/S3/Zeros/GapClosingExponent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A nonzero leading term fixes the punctured gap-closing exponent. -/

import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/- Library-search audit trail (2026-09-05):
   * Repository searches for gap-closing exponents, twice-multiplicity laws,
     little-o leading powers, and punctured normalized ratios found no equivalent
     theorem. `CriticalZeroTransverseGap` varies the transverse coordinate and
     proves a Taylor remainder in that different direction.
   * Blueprint, digest, exact-module, generalized asymptotic, and all refreshed
     in-flight branch searches found no equivalent declaration or module.
   * Pinned Mathlib provides `Asymptotics.IsLittleO.tendsto_div_nhds_zero`.
     The theorem is the atom-required thin wrapper that extracts the nonzero
     leading coefficient on a punctured neighborhood.
   * Proof shape: bind-only. Admission basis: rule-11-upstream-wrapper, required
     by the atom's claim that the displayed expansion determines exponent `2*m`.
     There are no direct frozen prerequisites. -/

namespace D5.S3.Zeros.GapClosingExponent

open Asymptotics Filter
open scoped Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- If a real-valued gap has a nonzero complex leading coefficient at order
`2 * m`, its normalization by that power converges on the punctured neighborhood
to the strictly positive squared modulus of the coefficient. -/
theorem gap_closing_exponent
    (V : ℝ → ℝ) (c : ℂ) (tStar : ℝ) (m : ℕ)
    (hm : 0 < m) (hc : c ≠ 0)
    (hAsymptotic :
      (fun t : ℝ =>
        V t - Complex.normSq c * |t - tStar| ^ (2 * m))
        =o[𝓝 tStar] (fun t : ℝ => |t - tStar| ^ (2 * m))) :
    Tendsto
        (fun t : ℝ => V t / |t - tStar| ^ (2 * m))
        (𝓝[≠] tStar) (𝓝 (Complex.normSq c)) ∧
      0 < Complex.normSq c := by
  let scale : ℝ → ℝ := fun t => |t - tStar| ^ (2 * m)
  let residual : ℝ → ℝ := fun t => V t - Complex.normSq c * scale t
  have hResidual : residual =o[𝓝 tStar] scale := by
    simpa [residual, scale] using hAsymptotic
  have hRatio :
      Tendsto (fun t => residual t / scale t) (𝓝[≠] tStar) (𝓝 0) :=
    hResidual.tendsto_div_nhds_zero.mono_left inf_le_left
  have hScaleNonzero : ∀ᶠ t in 𝓝[≠] tStar, scale t ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
    exact pow_ne_zero _ (abs_ne_zero.mpr (sub_ne_zero.mpr ht))
  have hNormalized :
      Tendsto (fun t => V t / scale t) (𝓝[≠] tStar)
        (𝓝 (Complex.normSq c)) := by
    have hSum :
        Tendsto (fun t => Complex.normSq c + residual t / scale t)
          (𝓝[≠] tStar) (𝓝 (Complex.normSq c + 0)) :=
      tendsto_const_nhds.add hRatio
    rw [add_zero] at hSum
    apply hSum.congr'
    filter_upwards [hScaleNonzero] with t ht
    dsimp only [residual]
    field_simp [ht]
    ring
  refine ⟨?_, ?_⟩
  · simpa [scale] using hNormalized
  · exact Complex.normSq_pos.mpr hc

#print axioms gap_closing_exponent

end D5.S3.Zeros.GapClosingExponent
