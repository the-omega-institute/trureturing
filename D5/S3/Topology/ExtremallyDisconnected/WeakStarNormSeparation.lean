/- GID: D5/S3/Topology/ExtremallyDisconnected/WeakStarNormSeparation
   generality: G
   mirror-B: D5/B/S3/Topology/ExtremallyDisconnected/WeakStarNormSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Stonean weak-star embeddings have a uniform strong-dual norm gap. -/

import D5.S3.Topology.ExtremallyDisconnected.PointPairSeparation
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Uniform strong-dual separation of weak-star embeddings

Weak-star closed norm balls give lower semicontinuity, not norm continuity.
The compact clopen-cross argument consumes the point-pair separation theorem.
-/

open Set Filter Topology

namespace D5.S3.Topology.ExtremallyDisconnected.WeakStarNormSeparation

universe u v

private theorem uniform_positive_of_lowerSemicontinuous
    {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [ExtremallyDisconnected K] (F : K × K → ℝ) (hlsc : LowerSemicontinuous F)
    (hpos : ∀ p q, p ≠ q → 0 < F (p, q)) :
    ∃ c : ℝ, 0 < c ∧ ∀ p q, p ≠ q → c ≤ F (p, q) := by
  classical
  by_contra hgap
  have hsmall : ∀ n : ℕ, ∃ p q : K, p ≠ q ∧ F (p, q) < 1 / ((n : ℝ) + 1) := by
    intro n
    have hc : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    by_contra hn
    apply hgap
    refine ⟨1 / ((n : ℝ) + 1), hc, ?_⟩
    intro p q hpq
    by_contra hle
    exact hn ⟨p, q, hpq, lt_of_not_ge hle⟩
  choose p q hne hlt using hsmall
  have hagree : ∀ U : Set K, IsClopen U → ∀ᶠ n in atTop, (p n ∈ U ↔ q n ∈ U) := by
    intro U hU
    let D : Set (K × K) := (U ×ˢ Uᶜ) ∪ (Uᶜ ×ˢ U)
    have hDclosed : IsClosed D :=
      (hU.isClosed.prod hU.compl.isClosed).union (hU.compl.isClosed.prod hU.isClosed)
    have hDne : ∀ z ∈ D, z.1 ≠ z.2 := by
      rintro ⟨x, y⟩ (h | h) he
      · exact h.2 (he ▸ h.1)
      · exact h.1 (he.symm ▸ h.2)
    by_cases hD : D.Nonempty
    · obtain ⟨z, hz, hmin⟩ :=
        LowerSemicontinuousOn.exists_isMinOn hD hDclosed.isCompact
          (hlsc.lowerSemicontinuousOn D)
      have hzpos : 0 < F z := hpos z.1 z.2 (hDne z hz)
      have hevent : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < F z :=
        tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hzpos)
      filter_upwards [hevent] with n hn
      have hout : (p n, q n) ∉ D := by
        intro hin
        exact (not_lt_of_ge (isMinOn_iff.mp hmin _ hin)) ((hlt n).trans hn)
      constructor
      · intro hp
        by_contra hq
        exact hout (Or.inl ⟨hp, hq⟩)
      · intro hq
        by_contra hp
        exact hout (Or.inr ⟨hp, hq⟩)
    · filter_upwards [] with n
      constructor
      · intro hp
        by_contra hq
        exact hD ⟨(p n, q n), Or.inl ⟨hp, hq⟩⟩
      · intro hq
        by_contra hp
        exact hD ⟨(p n, q n), Or.inr ⟨hp, hq⟩⟩
  have heq := PointPairSeparation.eventually_eq_of_eventually_mem_isClopen_iff p q hagree
  obtain ⟨n, hn⟩ := heq.exists
  exact hne n hn

/-- A weak-star continuous injection from any compact Hausdorff extremally
 disconnected space has a uniform positive gap in the strong-dual norm.
 No completeness, nonemptiness or global norm-bound hypothesis is needed. -/
theorem exists_pos_le_norm_sub
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [ExtremallyDisconnected K] (h : K → WeakDual ℝ X)
    (hcont : Continuous h) (hinj : Function.Injective h) :
    ∃ c : ℝ, 0 < c ∧ ∀ p q : K, p ≠ q →
      c ≤ ‖WeakDual.toStrongDual (h p - h q)‖ := by
  have hdiff : Continuous (fun z : K × K => h z.1 - h z.2) :=
    (hcont.comp continuous_fst).sub (hcont.comp continuous_snd)
  have hlsc : LowerSemicontinuous
      (fun z : K × K => ‖WeakDual.toStrongDual (h z.1 - h z.2)‖) := by
    apply lowerSemicontinuous_iff_isClosed_preimage.mpr
    intro r
    simpa only [Set.preimage, Metric.mem_closedBall, dist_zero_right, Set.mem_Iic, Set.mem_setOf_eq] using
      (WeakDual.isClosed_closedBall (0 : StrongDual ℝ X) r).preimage hdiff
  apply uniform_positive_of_lowerSemicontinuous _ hlsc
  intro p q hpq
  apply norm_pos_iff.mpr
  intro hz
  have hw : h p - h q = 0 :=
    WeakDual.toStrongDual.injective (by simpa using hz)
  exact hpq (hinj (sub_eq_zero.mp hw))

end D5.S3.Topology.ExtremallyDisconnected.WeakStarNormSeparation
