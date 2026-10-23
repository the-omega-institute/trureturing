/- GID: D5/S3/Analytic/Convexity/StrongConcavityAttainment
   generality: G
   mirror-B: D5/B/S3/Analytic/Convexity/StrongConcavityAttainment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strong concavity yields a unique quantitative maximizer on a complete convex set. -/

import Mathlib.Analysis.Convex.Strong
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic

/-!
# A strongly concave function attains its finite supremum on a complete set

The domain may be infinite dimensional and need not be compact. Midpoint strong
concavity controls distances by the two supremum deficits, so a maximizing sequence
is Cauchy. Completeness gives a point in the actual domain and upper semicontinuity
gives attainment. The same estimate proves uniqueness and a quadratic error bound.

This is a standard convex-analysis argument, using Mathlib's `StrongConcaveOn`.
The original quantum entropy application must separately prove strong concavity,
finite boundedness and upper semicontinuity in the genuine trace norm.
-/

open Filter Set Topology

namespace D5.S3.Analytic.Convexity.StrongConcavityAttainment

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An upper semicontinuous function with positive strong concavity and a finite
supremum on a nonempty complete domain has one actual maximizer, with a quadratic
deficit bound. No compactness or finite dimension is assumed. -/
theorem exists_unique_maximizer {s : Set E} {f : E → ℝ} {m : ℝ}
    (hs : s.Nonempty) (hc : IsComplete s) (hm : 0 < m)
    (hf : StrongConcaveOn s m f) (husc : UpperSemicontinuousOn f s)
    (hbdd : BddAbove (f '' s)) :
    ∃ x ∈ s, IsMaxOn f s x ∧
      (∀ y ∈ s, m / 4 * ‖y - x‖ ^ 2 ≤ f x - f y) ∧
      ∀ y ∈ s, IsMaxOn f s y → y = x := by
  classical
  let M := sSup (f '' s)
  have hupper (x : E) (hx : x ∈ s) : f x ≤ M :=
    le_csSup hbdd (mem_image_of_mem f hx)
  have hmid (x y : E) (hx : x ∈ s) (hy : y ∈ s) :
      (f x + f y) / 2 + m / 8 * ‖x - y‖ ^ 2 ≤ M := by
    have hmids : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ s := hf.1 hx hy
      (by norm_num) (by norm_num) (by norm_num)
    have h : (1 / 2 : ℝ) • f x + (1 / 2 : ℝ) • f y +
        (1 / 2 : ℝ) * (1 / 2 : ℝ) * (m / 2 * ‖x - y‖ ^ 2) ≤
        f ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) := hf.2 hx hy
      (by norm_num) (by norm_num) (by norm_num)
    dsimp [StrongConcaveOn] at h
    nlinarith [hupper _ hmids]
  obtain ⟨v, _, hvlim, hv⟩ := exists_seq_tendsto_sSup (hs.image f) hbdd
  choose u hu hfu using hv
  have huval : Tendsto (fun n => f (u n)) atTop (𝓝 M) := by
    simpa only [hfu] using hvlim
  have hucauchy : CauchySeq u := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    have hδ : 0 < m * ε ^ 2 / 16 := by positivity
    have hev : ∀ᶠ n in atTop, M - m * ε ^ 2 / 16 < f (u n) :=
      huval.eventually (lt_mem_nhds (by linarith : M - m * ε ^ 2 / 16 < M))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    refine ⟨N, fun p hp q hq => ?_⟩
    rw [dist_eq_norm]
    have hpv := hN p hp
    have hqv := hN q hq
    have hineq := hmid (u p) (u q) (hu p) (hu q)
    by_contra hdist
    have hsq : ε ^ 2 ≤ ‖u p - u q‖ ^ 2 := by
      nlinarith [norm_nonneg (u p - u q), le_of_not_gt hdist]
    have hmul := mul_le_mul_of_nonneg_left hsq (show 0 ≤ m / 8 by positivity)
    nlinarith
  obtain ⟨x, hx, hux⟩ := cauchySeq_tendsto_of_isComplete hc hu hucauchy
  have hwithin : Tendsto u atTop (𝓝[s] x) :=
    tendsto_nhdsWithin_iff.mpr ⟨hux, Eventually.of_forall hu⟩
  have hM : M ≤ f x := by
    apply le_of_forall_gt
    intro c hc
    have hcut : f x < (f x + c) / 2 := by linarith
    have hle : M ≤ (f x + c) / 2 := le_of_tendsto huval <|
      (hwithin.eventually (husc x hx _ hcut)).mono fun _ h => h.le
    linarith
  have hxmax : IsMaxOn f s x := isMaxOn_iff.mpr fun y hy =>
    (hupper y hy).trans hM
  have hdeficit (y : E) (hy : y ∈ s) : m / 4 * ‖y - x‖ ^ 2 ≤ f x - f y := by
    have h := hmid y x hy hx
    nlinarith
  refine ⟨x, hx, hxmax, hdeficit, fun y hy hymax => ?_⟩
  have h := hdeficit y hy
  have heq : f x = f y := le_antisymm (hymax hx) (hxmax hy)
  have hn : ‖y - x‖ = 0 := by
    rw [heq, sub_self] at h
    have hsq : ‖y - x‖ ^ 2 ≤ 0 := by
      by_contra hs
      have hp : 0 < m / 4 * ‖y - x‖ ^ 2 :=
        mul_pos (by positivity) (lt_of_not_ge hs)
      linarith
    nlinarith [sq_nonneg ‖y - x‖, norm_nonneg (y - x)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

end D5.S3.Analytic.Convexity.StrongConcavityAttainment
