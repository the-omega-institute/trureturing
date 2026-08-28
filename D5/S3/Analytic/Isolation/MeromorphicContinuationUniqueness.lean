/- GID: D5/S3/Analytic/Isolation/MeromorphicContinuationUniqueness
   generality: G
   mirror-B: D5/B/S3/Analytic/Isolation/MeromorphicContinuationUniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Normal-form meromorphic continuations agreeing on an open set agree on their domain. -/

import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Complex.Basic

/- Provenance: thin wrapper over pinned mathlib's local meromorphic identity principles,
   `MeromorphicAt.frequently_eq_iff_eventuallyEq` and
   `MeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds`. -/

open Filter Topology

namespace D5.S3.Analytic.Isolation.MeromorphicContinuationUniqueness

/-- Two normal-form meromorphic continuations agreeing on a nonempty open subset of an open
preconnected domain agree throughout that domain. -/
theorem meromorphic_continuation_unique
    {Ω D : Set ℂ} {f g : ℂ → ℂ}
    (hΩ_open : IsOpen Ω) (hΩ_preconnected : IsPreconnected Ω)
    (hD_open : IsOpen D) (hD_nonempty : D.Nonempty) (hDΩ : D ⊆ Ω)
    (hf : MeromorphicNFOn f Ω) (hg : MeromorphicNFOn g Ω)
    (hfg : Set.EqOn f g D) :
    Set.EqOn f g Ω := by
  let A : Set ℂ := {z | f =ᶠ[𝓝 z] g}
  have hA_open : IsOpen A := isOpen_setOf_eventually_nhds
  have hΩ_diff_A_open : IsOpen (Ω \ A) := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    rcases hz with ⟨hzΩ, hzA⟩
    have hzA' : ¬ f =ᶠ[𝓝 z] g := by
      simpa [A] using hzA
    have hnot_punctured : ¬ f =ᶠ[𝓝[≠] z] g := by
      intro hpunctured
      exact hzA' <|
        ((hf hzΩ).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (hg hzΩ)).1 hpunctured
    have hne_punctured : ∀ᶠ y in 𝓝[≠] z, f y ≠ g y := by
      rw [← not_frequently]
      intro hfrequent
      exact hnot_punctured <|
        ((hf hzΩ).meromorphicAt.frequently_eq_iff_eventuallyEq
          (hg hzΩ).meromorphicAt).1 hfrequent
    have hnot_A_punctured : ∀ᶠ y in 𝓝[≠] z, y ∉ A :=
      hne_punctured.mono fun y hy hyA ↦
        hy (show f y = g y from
          (show f =ᶠ[𝓝 y] g by simpa [A] using hyA).eq_of_nhds)
    have hnot_A : ∀ᶠ y in 𝓝 z, y ∉ A := by
      filter_upwards [eventually_nhdsWithin_iff.1 hnot_A_punctured] with y hy
      by_cases hyz : y = z
      · simpa [hyz] using hzA
      · exact hy (by simpa using hyz)
    filter_upwards [hΩ_open.mem_nhds hzΩ, hnot_A] with y hyΩ hyA
    exact ⟨hyΩ, hyA⟩
  have hD_A : D ⊆ A := by
    intro z hzD
    have hlocal : f =ᶠ[𝓝 z] g := by
      filter_upwards [hD_open.mem_nhds hzD] with y hyD
      exact hfg hyD
    simpa [A] using hlocal
  obtain ⟨z, hzD⟩ := hD_nonempty
  have hΩ_inter_A : (Ω ∩ A).Nonempty :=
    ⟨z, hDΩ hzD, hD_A hzD⟩
  have hΩ_A : Ω ⊆ A :=
    hΩ_preconnected.subset_left_of_subset_union hA_open hΩ_diff_A_open
      (by
        refine Set.disjoint_left.2 ?_
        intro y hyA hyΩdiff
        exact hyΩdiff.2 hyA)
      (by
        intro y hyΩ
        by_cases hyA : y ∈ A
        · exact Or.inl hyA
        · exact Or.inr ⟨hyΩ, hyA⟩)
      hΩ_inter_A
  intro y hyΩ
  exact (show f =ᶠ[𝓝 y] g by simpa [A] using hΩ_A hyΩ).eq_of_nhds

-- Reverse probe: the public conclusion recovers equality at every supplied domain point.
example
    {Ω D : Set ℂ} {f g : ℂ → ℂ}
    (hΩ_open : IsOpen Ω) (hΩ_preconnected : IsPreconnected Ω)
    (hD_open : IsOpen D) (hD_nonempty : D.Nonempty) (hDΩ : D ⊆ Ω)
    (hf : MeromorphicNFOn f Ω) (hg : MeromorphicNFOn g Ω)
    (hfg : Set.EqOn f g D) {z : ℂ} (hz : z ∈ Ω) :
    f z = g z :=
  meromorphic_continuation_unique hΩ_open hΩ_preconnected hD_open hD_nonempty hDΩ
    hf hg hfg hz

-- Trivialization probe: the open agreement set cannot be chosen empty.
example : ¬(∅ : Set ℂ).Nonempty := by simp

end D5.S3.Analytic.Isolation.MeromorphicContinuationUniqueness
