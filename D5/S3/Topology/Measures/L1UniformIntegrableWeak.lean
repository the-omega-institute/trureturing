/- GID: D5/S3/Topology/Measures/L1UniformIntegrableWeak
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/L1UniformIntegrableWeak
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-measure uniformly integrable real L1 sequences have weak subsequences. -/

import D5.S3.Topology.Measures.L1WeakExtraction
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Finiteness

/-! Weak subsequences of uniformly integrable real L1 sequences. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter MeasureTheory Topology
open scoped ENNReal NNReal

namespace D5.S3.Topology.Measures.L1UniformIntegrableWeak

universe u
variable {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

private noncomputable def l2ToL1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 1 μ := by
  let L : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 1 μ :=
    { toFun := fun f => ⟨f.val, Lp.antitone (by norm_num) f.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let C : ℝ≥0∞ := μ univ ^ (1 / 2 : ℝ)
  have hC : C ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ univ)
  refine L.mkContinuous C.toReal (fun f => ?_)
  change (eLpNorm f 1 μ).toReal ≤ C.toReal * (eLpNorm f 2 μ).toReal
  have h : eLpNorm f 1 μ ≤ eLpNorm f 2 μ * C := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (show (1 : ℝ≥0∞) ≤ 2 by norm_num) (Lp.aestronglyMeasurable f)
    norm_num at h
    exact h
  have hfin : eLpNorm f 2 μ * C ≠ ∞ := ENNReal.mul_ne_top (Lp.memLp f).eLpNorm_lt_top.ne hC
  simpa only [ENNReal.toReal_mul, mul_comm] using ENNReal.toReal_mono hfin h

/-- Weak sequential compactness of a uniformly integrable real L1 sequence.
The weak limit tests all continuous real linear functionals. -/
theorem exists_weak_subsequence (f : ℕ → Lp ℝ 1 μ)
    (hfu : UniformIntegrable (fun n => (f n : Ω → ℝ)) 1 μ) :
    ∃ (j : ℕ → ℕ) (v : Lp ℝ 1 μ), StrictMono j ∧
      ∀ φ : Lp ℝ 1 μ →L[ℝ] ℝ,
        Tendsto (fun n => φ (f (j n))) atTop (𝓝 (φ v)) := by
  let δ (m : ℕ) : ℝ := 1 / ((m : ℝ) + 1)
  have hδpos (m : ℕ) : 0 < δ m := by dsimp [δ]; positivity
  obtain ⟨C, hC⟩ : ∃ C : ℕ → ℝ≥0, ∀ m n,
      eLpNorm ({x | C m ≤ ‖f n x‖₊}.indicator (f n)) 1 μ ≤ ENNReal.ofReal (δ m) := by
    choose C hC using fun m => hfu.spec (by norm_num) (by norm_num)
      (ENNReal.ofReal_pos.mpr (hδpos m))
    exact ⟨C, hC⟩
  let g (m n : ℕ) : Ω → ℝ := {x | ‖f n x‖₊ < C m}.indicator (f n)
  have hg (m n : ℕ) : AEStronglyMeasurable (g m n) μ :=
    (Lp.aestronglyMeasurable (f n)).indicator₀
      (nullMeasurableSet_lt (Lp.aestronglyMeasurable (f n)).nnnorm.aemeasurable aemeasurable_const)
  have hgb (m n : ℕ) : ∀ᵐ x ∂μ, ‖g m n x‖ ≤ (C m : ℝ) := by
    filter_upwards with x
    by_cases hx : ‖f n x‖₊ < C m
    · simpa [g, hx] using (show ‖f n x‖ ≤ (C m : ℝ) by exact_mod_cast hx.le)
    · simpa [g, hx] using (C m).coe_nonneg
  have hgm (m n : ℕ) : MemLp (g m n) 2 μ := MemLp.of_bound (hg m n) (C m) (hgb m n)
  let t (m n : ℕ) : Lp ℝ 2 μ := (hgm m n).toLp (g m n)
  let R (m : ℕ) : ℝ := (μ univ ^ (1 / 2 : ℝ) * (C m : ℝ≥0∞)).toReal
  have hb (m n : ℕ) : ‖t m n‖ ≤ R m := by
    rw [Lp.norm_toLp]
    apply ENNReal.toReal_mono (by finiteness)
    simpa [R] using eLpNorm_le_of_ae_bound (p := (2 : ℝ≥0∞)) (hg m n) (hgb m n)
  have herr (m n : ℕ) : ‖f n - l2ToL1 μ (t m n)‖ ≤ δ m := by
    have heq : ⇑(f n - l2ToL1 μ (t m n) : Lp ℝ 1 μ) =ᵐ[μ]
        {x | C m ≤ ‖f n x‖₊}.indicator (f n) := by
      filter_upwards [Lp.coeFn_sub (f n) (l2ToL1 μ (t m n)), (hgm m n).coeFn_toLp]
        with x hsub ht
      rw [hsub]
      change f n x - t m n x = _
      rw [ht]
      by_cases hx : ‖f n x‖₊ < C m
      · simp [g, hx, not_le.mpr hx]
      · simp [g, hx, le_of_not_gt hx]
    calc
      _ = (eLpNorm ({x | C m ≤ ‖f n x‖₊}.indicator (f n)) 1 μ).toReal := by
        rw [Lp.norm_def, eLpNorm_congr_ae heq]
      _ ≤ (ENNReal.ofReal (δ m)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hC m n)
      _ = δ m := ENNReal.toReal_ofReal (hδpos m).le
  exact L1WeakExtraction.exists_weak_subsequence_of_hilbert_approximation
    (l2ToL1 μ) f t R δ hb tendsto_one_div_add_atTop_nhds_zero_nat herr

end D5.S3.Topology.Measures.L1UniformIntegrableWeak
