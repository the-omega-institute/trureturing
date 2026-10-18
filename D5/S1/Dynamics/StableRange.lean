/- GID: D5/S1/Dynamics/StableRange
   generality: G
   mirror-B: D5/B/S1/Dynamics/StableRange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nested compact preimages give an onto restriction to the stable range. -/

import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Compactness.Compact
import Mathlib.Logic.Function.Iterate

/-!
# Stable ranges of compact Hausdorff endomorphisms

The onto restriction uses nested closed preimages. It selects no backward orbit
and assumes neither a nonempty source nor an onto ambient map.
-/

open Set Function Topology

namespace D5.S1.Dynamics.StableRange

universe u

variable {X : Type u}

def core (f : X → X) : Set X := ⋂ n : ℕ, range (f^[n])

private theorem range_succ_subset (f : X → X) (n : ℕ) :
    range (f^[n + 1]) ⊆ range (f^[n]) := by
  rintro _ ⟨a, rfl⟩
  exact ⟨f a, (Function.iterate_succ_apply f n a).symm⟩

/-- Forward invariance is purely set theoretic and includes time zero. -/
theorem mapsTo_core (f : X → X) : MapsTo f (core f) (core f) := by
  intro c hc
  apply mem_iInter.mpr
  intro n
  cases n with
  | zero => exact ⟨f c, rfl⟩
  | succ n =>
    obtain ⟨a, ha⟩ := mem_iInter.mp hc n
    exact ⟨a, by rw [Function.iterate_succ_apply', ha]⟩

def restriction (f : X → X) (c : core f) : core f :=
  ⟨f c.val, mapsTo_core f c.property⟩

section Topological

variable [TopologicalSpace X] [CompactSpace X] [T2Space X]

theorem is_closed_core {f : X → X} (hf : Continuous f) : IsClosed (core f) :=
  isClosed_iInter fun n => (isCompact_range (hf.iterate n)).isClosed

/-- Every stable point has a preimage in the stable range itself. -/
theorem surj_on_core {f : X → X} (hf : Continuous f) : SurjOn f (core f) (core f) := by
  intro c hc
  let F : ℕ → Set X := fun n => range (f^[n]) ∩ f ⁻¹' {c}
  have hclosed (n : ℕ) : IsClosed (F n) :=
    ((isCompact_range (hf.iterate n)).isClosed).inter (isClosed_singleton.preimage hf)
  have hmono (n : ℕ) : F (n + 1) ⊆ F n :=
    fun _ hx => ⟨range_succ_subset f n hx.1, hx.2⟩
  have hne (n : ℕ) : (F n).Nonempty := by
    obtain ⟨a, ha⟩ := mem_iInter.mp hc (n + 1)
    refine ⟨f^[n] a, ⟨a, rfl⟩, ?_⟩
    change f (f^[n] a) = c
    simpa only [Function.iterate_succ_apply'] using ha
  obtain ⟨a, ha⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      F hmono hne (hclosed 0).isCompact hclosed
  refine ⟨a, mem_iInter.mpr (fun n => (mem_iInter.mp ha n).1), ?_⟩
  exact (mem_iInter.mp ha 0).2

/-- The actual core is compact and its continuous dynamics is onto. -/
theorem compact_surjective_restriction {f : X → X} (hf : Continuous f) :
    IsCompact (core f) ∧ Continuous (restriction f) ∧ Surjective (restriction f) := by
  refine ⟨(is_closed_core hf).isCompact,
    (hf.comp continuous_subtype_val).subtype_mk _, ?_⟩
  intro c
  obtain ⟨a, ha, hac⟩ := surj_on_core hf c.property
  exact ⟨⟨a, ha⟩, Subtype.ext hac⟩

end Topological

end D5.S1.Dynamics.StableRange
