/- GID: D5/S1/Dynamics/Shadowing/DendriteObstruction/MinimalInvariant
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/DendriteObstruction/MinimalInvariant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Minimal compact invariant sets retaining a nondegenerate continuum. -/

import D5.S1.Dynamics.Shadowing.DendriteObstruction.CompactHistories
import Mathlib.Order.Zorn

open Set Function Filter
open scoped Topology
open TopologicalSpace

namespace D5.S1.Dynamics.Shadowing.DendriteObstruction

variable {X : Type*} [MetricSpace X]

/-- This class retains an actual nondegenerate continuum, without requiring
that the invariant compactum itself be connected. -/
def InvariantContinuumSet (f : X → X) (Y : Set X) : Prop :=
  IsCompact Y ∧ MapsTo f Y Y ∧
    ∃ C : Set X, IsCompact C ∧ IsConnected C ∧ C.Nontrivial ∧ C ⊆ Y

/-- Zorn minimization in the class that retains a continuum, rather than in the
class of all nonempty invariant compacta. -/
theorem exists_minimal_invariant_continuum [CompactSpace X] {f : X → X}
    (hf : Continuous f) (hfin : FinitelyPositiveExpansive f) (hull : StaticArcHull X)
    (A : EmbeddedArc X) :
    ∃ Y : Set X, Minimal (InvariantContinuumSet f) Y := by
  classical
  obtain ⟨ε, hε, N, _, hB⟩ := hfin
  let a := ε / 4
  have ha : 0 < a := by dsimp [a]; positivity
  have macroscopic : ∀ Y, InvariantContinuumSet f Y →
      ∃ K : NonemptyCompacts X,
        (IsConnected (K : Set X) ∧ a ≤ Metric.diam (K : Set X)) ∧ (K : Set X) ⊆ Y := by
    rintro Y ⟨_, hmap, C, hc, hcon, hnt, hCY⟩
    obtain ⟨n, _, hn⟩ := continuum_expands hf hε hB hull hc hcon hnt 0
    refine ⟨⟨⟨f^[n] '' C, hc.image (hf.iterate n)⟩, hcon.nonempty.image _⟩,
      ⟨hcon.image _ (hf.iterate n).continuousOn, ?_⟩,
      (image_mono hCY).trans (hmap.iterate n).image_subset⟩
    exact (by dsimp [a]; linarith : a ≤ ε).trans hn
  have hX : InvariantContinuumSet f univ :=
    ⟨isCompact_univ, mapsTo_univ f univ, A.carrier, A.compact, A.connected,
      A.infinite.nontrivial, subset_univ _⟩
  apply zorn_superset {Y | InvariantContinuumSet f Y}
  intro c hc hchain
  rcases c.eq_empty_or_nonempty with rfl | hne
  · exact ⟨univ, hX, by simp⟩
  letI : Nonempty c := hne.to_subtype
  let S : c → Set (NonemptyCompacts X) := fun Y =>
    {K | (IsConnected (K : Set X) ∧ a ≤ Metric.diam (K : Set X)) ∧ (K : Set X) ⊆ Y.1}
  have hSc (Y : c) : IsCompact (S Y) :=
    compact_continua_ge_in a (hc Y.2).1.isClosed
  have hSn (Y : c) : (S Y).Nonempty := macroscopic Y.1 (hc Y.2)
  have hdir : Directed (· ⊇ ·) S := by
    intro Y Z
    rcases hchain.total Y.2 Z.2 with hYZ | hZY
    · exact ⟨Y, Subset.rfl, fun K hK => ⟨hK.1, hK.2.trans hYZ⟩⟩
    · exact ⟨Z, (fun K hK => ⟨hK.1, hK.2.trans hZY⟩), Subset.rfl⟩
  obtain ⟨K, hK⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    S hdir hSn hSc (fun Y => (hSc Y).isClosed)
  have hKS (Y : c) : K ∈ S Y := mem_iInter.mp hK Y
  obtain ⟨Y₀, hY₀⟩ := hne
  have hbase := (hKS ⟨Y₀, hY₀⟩).1
  have hKsub : (K : Set X) ⊆ ⋂₀ c := by
    intro x hx
    exact mem_sInter.mpr (fun Y hY => (hKS ⟨Y, hY⟩).2 hx)
  refine ⟨⋂₀ c, ⟨?_, ?_, (K : Set X), K.isCompact, hbase.1,
    nontrivial_of_diam_pos (ha.trans_le hbase.2), hKsub⟩, ?_⟩
  · exact (isClosed_sInter (fun Y hY => (hc hY).1.isClosed)).isCompact
  · intro x hx
    exact mem_sInter.mpr (fun Y hY => (hc hY).2.1 (mem_sInter.mp hx Y hY))
  · exact fun Y hY => sInter_subset_of_mem hY

end D5.S1.Dynamics.Shadowing.DendriteObstruction
