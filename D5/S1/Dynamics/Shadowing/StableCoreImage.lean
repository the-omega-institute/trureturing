/- GID: D5/S1/Dynamics/Shadowing/StableCoreImage
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/StableCoreImage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Continuous observations preserve the stable-core intersection. -/

import D5.S1.Dynamics.Shadowing.StableCoreObservation

/- Bounded library search (2026-10-12): the repository's
FactorImageStability.surjective_semiconj_iterate_ranges transports individual
iterate images on a finite source. It does not exchange an infinite image and
intersection. Pinned Mathlib's compact nested-intersection theorem supplies the
missing common predecessor in a closed observation fiber. No injectivity,
finite alphabet, source shadowing, equicontinuity or surjectivity is assumed.
The conclusion is a stable-core supplier, not a resolution of Peng Q5.1/Q5.2.
All declarations have utility kind none: no checker, finite enumeration or
numerical reduction is claimed. -/

open Set Function

namespace D5.S1.Dynamics.Shadowing

universe u v

/-- Every value realizable in every forward image has one realization in the
stable core. The target only needs closed singletons. The observation need
not be injective or onto, and its target need not be compact or finite. -/
theorem image_stableCore_eq_iInter
    {X : Type u} {Y : Type v} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [T1Space Y]
    (f : X → X) (q : X → Y) (hf : Continuous f) (hq : Continuous q) :
    q '' stableCore f = ⋂ n : ℕ, q '' Set.range (f^[n]) := by
  classical
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact Set.mem_iInter.mpr fun n => ⟨x, Set.mem_iInter.mp hx n, rfl⟩
  · intro y hy
    let K : ℕ → Set X := fun n => (q ⁻¹' {y}) ∩ Set.range (f^[n])
    have hclosed (n : ℕ) : IsClosed (K n) :=
      (isClosed_singleton.preimage hq).inter
        (isCompact_range (hf.iterate n)).isClosed
    have hnest : ∀ n : ℕ, K (n + 1) ⊆ K n := by
      intro n x hx
      refine ⟨hx.1, ?_⟩
      obtain ⟨z, hz⟩ := hx.2
      exact ⟨f z, by simpa only [iterate_succ_apply] using hz⟩
    have hne (n : ℕ) : (K n).Nonempty := by
      obtain ⟨x, hx, hqx⟩ := Set.mem_iInter.mp hy n
      exact ⟨x, hqx, hx⟩
    obtain ⟨x, hx⟩ :=
      IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
        K hnest hne (hclosed 0).isCompact hclosed
    exact ⟨x, Set.mem_iInter.mpr fun n => (Set.mem_iInter.mp hx n).2,
      (Set.mem_iInter.mp hx 0).1⟩

#print axioms image_stableCore_eq_iInter

end D5.S1.Dynamics.Shadowing
