/- GID: D5/S3/Arith/Lattices/Klartag/Walk/StepTruncVariance
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Walk/StepTruncVariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian matrix walk, filtration and stopped increments. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Drift.DriftVarianceBounded
import D5.S3.Arith.Lattices.Klartag.Walk.ChainSetup

set_option linter.unusedSectionVars false

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Tail
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Walk.StepTruncVariance

open MeasureTheory
open ProbabilityTheory
open Finset
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments

variable {n : ℕ}

/-- **The truncated squared step norm.** -/
noncomputable def sqTrunc (c cap : ℝ) (k : ℕ) (ω : ℕ → EuclideanSpace ℝ (UT n)) : ℝ :=
  min (‖ChainSetup.step c k ω‖ ^ 2) cap

theorem sqTrunc_mem_Icc {c cap : ℝ} (hcap : 0 ≤ cap) (k : ℕ)
    (ω : ℕ → EuclideanSpace ℝ (UT n)) : sqTrunc c cap k ω ∈ Set.Icc (0 : ℝ) cap :=
  ⟨le_min (by positivity) hcap, min_le_right _ _⟩

theorem measurable_sqTrunc (c cap : ℝ) (k : ℕ) :
    Measurable (sqTrunc (n := n) c cap k) := by
  refine Measurable.min ?_ measurable_const
  exact ((ChainSetup.measurable_step c k).norm.pow_const 2)

/-- `MemLp _ 2`, from the cap. -/
theorem memLp_sqTrunc {c cap : ℝ} (hcap : 0 ≤ cap) (k : ℕ) :
    MemLp (sqTrunc (n := n) c cap k) 2
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := by
  refine MemLp.of_bound (measurable_sqTrunc c cap k).aestronglyMeasurable cap ?_
  filter_upwards with ω
  have h := sqTrunc_mem_Icc (n := n) (c := c) hcap k ω
  rw [Real.norm_eq_abs, abs_of_nonneg h.1]
  exact h.2

/-- **Independence across steps**, carried through the truncation by `IndepFun.comp`. -/
theorem pairwise_indepFun_sqTrunc (c cap : ℝ) (K : ℕ) :
    Set.Pairwise (↑(Finset.range K)) fun i j =>
      IndepFun (sqTrunc (n := n) c cap i) (sqTrunc (n := n) c cap j)
        (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := by
  intro i _ j _ hij
  have hbase := (ChainSetup.iIndepFun_step (ι := UT n) c).indepFun hij
  have hg : Measurable (fun x : EuclideanSpace ℝ (UT n) => min (‖x‖ ^ 2) cap) :=
    Measurable.min (measurable_norm.pow_const 2) measurable_const
  exact hbase.comp hg hg

/-- **The variance of the truncated drift proxy**, `K·cap²/4`.  At the adopted parameters
`cap = η²` and this is `N·η⁴/4 = T·h·dim²·n²`, about `4·log n·n⁻⁵`. -/
theorem variance_sum_sqTrunc_le {c cap : ℝ} (hcap : 0 ≤ cap) (K : ℕ) :
    variance (fun ω => ∑ j ∈ Finset.range K, sqTrunc (n := n) c cap j ω)
        (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      ≤ (K : ℝ) * (cap / 2) ^ 2 :=
  DriftVarianceBounded.variance_sum_le
    (fun j _ => memLp_sqTrunc hcap j)
    (pairwise_indepFun_sqTrunc c cap K)
    (fun j _ => Filter.Eventually.of_forall fun ω => sqTrunc_mem_Icc (c := c) hcap j ω)

theorem sqTrunc_le {c cap : ℝ} (k : ℕ) (ω : ℕ → EuclideanSpace ℝ (UT n)) :
    sqTrunc c cap k ω ≤ ‖ChainSetup.step c k ω‖ ^ 2 := min_le_left _ _

section Integrability

/-- The truncated drift proxy is bounded, hence integrable. -/
theorem integrable_sum_sqTrunc {c cap : ℝ} (hcap : 0 ≤ cap) (K : ℕ) :
    Integrable (fun ω => ∑ j ∈ Finset.range K, sqTrunc (n := n) c cap j ω)
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := by
  refine Integrable.mono' (integrable_const ((K : ℝ) * cap))
    ((Finset.measurable_sum _ (fun j _ => measurable_sqTrunc c cap j)).aestronglyMeasurable) ?_
  filter_upwards with ω
  have hnn : (0 : ℝ) ≤ ∑ j ∈ Finset.range K, sqTrunc (n := n) c cap j ω :=
    Finset.sum_nonneg fun j _ => (sqTrunc_mem_Icc (c := c) hcap j ω).1
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  calc ∑ j ∈ Finset.range K, sqTrunc (n := n) c cap j ω
      ≤ ∑ _j ∈ Finset.range K, cap :=
        Finset.sum_le_sum fun j _ => (sqTrunc_mem_Icc (c := c) hcap j ω).2
    _ = (K : ℝ) * cap := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem integrable_neg_part {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {M : Ω → ℝ} (hM : Integrable M P) : Integrable (fun ω => max (-(M ω)) 0) P := by
  have h := GoodPathVar.integrable_pos_part (X := M) (P := P) hM 0
  refine h.congr ?_
  filter_upwards with ω using by rw [zero_sub]

end Integrability

end D5.S3.Arith.Lattices.Klartag.Walk.StepTruncVariance
