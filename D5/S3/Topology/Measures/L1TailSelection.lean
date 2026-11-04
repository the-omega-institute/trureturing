/- GID: D5/S3/Topology/Measures/L1TailSelection
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/L1TailSelection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Simultaneous tail limits admit recursive cutoffs and increasing selectors. -/

import D5.S3.Topology.Measures.L1WeakExtraction
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Lean.Elab.Tactic.Omega

/-! A countable diagonal selection for the hard-tail concentration argument. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter Topology

namespace D5.S3.Topology.Measures.L1TailSelection

/-- A bounded nonnegative tail array decreasing in its cutoff has a subsequence
with simultaneous fixed-cutoff limits and moving-cutoff limit equal to their
infimum. The cutoffs can satisfy any eventual constraint depending on the last
selected source index. This supplies the recursive small-support conditions. -/
theorem exists_selection
    (Q : ℕ → ℕ → ℝ) (B : ℝ)
    (hQ : ∀ n k, 0 ≤ Q n k ∧ Q n k ≤ B)
    (hmono : ∀ n, Antitone (Q n))
    (P : ℕ → ℕ → ℕ → Prop)
    (hP : ∀ i N, ∀ᶠ K in atTop, P i N K) :
    ∃ (j K : ℕ → ℕ) (c : ℕ → ℝ) (α : ℝ) (N : ℕ → ℕ),
      StrictMono j ∧ (∀ i, i < K i) ∧ 0 ≤ α ∧
      (∀ k, α ≤ c k) ∧ Tendsto c atTop (𝓝 α) ∧
      (∀ k, Tendsto (fun i => Q (j i) k) atTop (𝓝 (c k))) ∧
      Tendsto (fun i => Q (j i) (K i)) atTop (𝓝 α) ∧
      (∀ i, P i (N i) (K i)) ∧ (∀ h i, h < i → j h ≤ N i) := by
  classical
  obtain ⟨a, c, ha, hc⟩ := L1WeakExtraction.exists_common_weak_subsequence
    (fun k n => Q n k) (fun _ => B) (fun k n => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hQ n k).1] using (hQ n k).2)
  have hclim (k : ℕ) : Tendsto (fun n => Q (a n) k) atTop (𝓝 (c k)) :=
    hc k (ContinuousLinearMap.id ℝ ℝ)
  have hcpos (k : ℕ) : 0 ≤ c k := ge_of_tendsto' (hclim k) (fun n => (hQ (a n) k).1)
  have hcm : Antitone c := fun k l hkl =>
    le_of_tendsto_of_tendsto' (hclim l) (hclim k) (fun n => hmono (a n) hkl)
  have hcb : BddBelow (range c) := ⟨0, by rintro _ ⟨k, rfl⟩; exact hcpos k⟩
  let α : ℝ := ⨅ k, c k
  have hα : 0 ≤ α := le_ciInf hcpos
  have hαk (k : ℕ) : α ≤ c k := ciInf_le hcb k
  have hcα : Tendsto c atTop (𝓝 α) := tendsto_atTop_ciInf hcm hcb
  let ε (i : ℕ) : ℝ := 1 / ((i : ℝ) + 1)
  have hε (i : ℕ) : 0 < ε i := by dsimp [ε]; positivity
  have step (i N : ℕ) : ∃ K n, N < n ∧ i < K ∧ P i (a N) K ∧
      dist (Q (a n) K) α < ε i := by
    obtain ⟨K, hiK, hpK, hcK⟩ : ∃ K, i < K ∧ P i (a N) K ∧
        dist (c K) α < ε i / 2 := by
      have ev : ∀ᶠ K in atTop, i < K ∧ P i (a N) K ∧ dist (c K) α < ε i / 2 := by
        filter_upwards [eventually_gt_atTop i, hP i (a N),
          hcα.eventually (Metric.ball_mem_nhds α (ε := ε i / 2) (by linarith [hε i]))]
          with K hi hp hd
        exact ⟨hi, hp, hd⟩
      exact ev.exists
    have ev : ∀ᶠ n in atTop, N < n ∧ dist (Q (a n) K) (c K) < ε i / 2 := by
      filter_upwards [eventually_gt_atTop N,
        (hclim K).eventually (Metric.ball_mem_nhds (c K) (ε := ε i / 2) (by linarith [hε i]))] with n hn hd
      exact ⟨hn, hd⟩
    obtain ⟨n, hn, hd⟩ := ev.exists
    exact ⟨K, n, hn, hiK, hpK, (dist_triangle (Q (a n) K) (c K) α).trans_lt (by linarith)⟩
  choose cut next hnext hcut hp herr using step
  let b : ℕ → ℕ := Nat.rec 0 (fun i n => next i n)
  have hb (i : ℕ) : b (i + 1) = next i (b i) := rfl
  have hbm : StrictMono b := strictMono_nat_of_lt_succ (fun i => by
    rw [hb]; exact hnext i (b i))
  let j (i : ℕ) := a (b (i + 1))
  let K (i : ℕ) := cut i (b i)
  have hbi : StrictMono (fun i => b (i + 1)) :=
    fun i j hij => hbm (show i + 1 < j + 1 by omega)
  have hj : StrictMono j := ha.comp hbi
  refine ⟨j, K, c, α, fun i => a (b i), hj, fun i => hcut i (b i), hα, hαk,
    hcα, fun k => (hclim k).comp hbi.tendsto_atTop, ?_, fun i => hp i (b i), ?_⟩
  · apply tendsto_iff_dist_tendsto_zero.2
    apply squeeze_zero (fun i => dist_nonneg) (fun i => (herr i (b i)).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  · intro h i hhi
    change a (b (h + 1)) ≤ a (b i)
    exact ha.monotone (hbm.monotone (show h + 1 ≤ i by omega))

end D5.S3.Topology.Measures.L1TailSelection
