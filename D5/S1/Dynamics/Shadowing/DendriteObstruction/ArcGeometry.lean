/- GID: D5/S1/Dynamics/Shadowing/DendriteObstruction/ArcGeometry
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/DendriteObstruction/ArcGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compactness of nonempty subcontinua with a diameter lower bound. -/

import Mathlib.Topology.Sets.VietorisTopology
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! Concrete hyperspace compactness used by the arc persistence argument. -/

open Set Function Filter
open scoped Topology
open TopologicalSpace

namespace D5.S1.Dynamics.Shadowing.DendriteObstruction

variable {X : Type*} [MetricSpace X]

private theorem compact_diam_le_iff (K : NonemptyCompacts X) (a : ℝ) :
    Metric.diam (K : Set X) ≤ a ↔ ∀ x ∈ (K : Set X), ∀ y ∈ (K : Set X), dist x y ≤ a :=
  ⟨fun h x hx y hy => (Metric.dist_le_diam_of_mem K.isCompact.isBounded hx hy).trans h,
    Metric.diam_le_of_forall_dist_le_of_nonempty K.nonempty⟩

private theorem compact_diam_lt_iff (K : NonemptyCompacts X) (a : ℝ) :
    Metric.diam (K : Set X) < a ↔ ∀ x ∈ (K : Set X), ∀ y ∈ (K : Set X), dist x y < a := by
  constructor
  · intro h x hx y hy
    exact (Metric.dist_le_diam_of_mem K.isCompact.isBounded hx hy).trans_lt h
  · intro h
    obtain ⟨⟨x, y⟩, hxy, hmax⟩ := (K.isCompact.prod K.isCompact).exists_isMaxOn
      (K.nonempty.prod K.nonempty) continuous_dist.continuousOn
    have hle : Metric.diam (K : Set X) ≤ dist x y :=
      Metric.diam_le_of_forall_dist_le_of_nonempty K.nonempty (fun u hu v hv => hmax (show (u, v) ∈ (K : Set X) ×ˢ (K : Set X) from ⟨hu, hv⟩))
    exact hle.trans_lt (h x hxy.1 y hxy.2)

/-- Diameter is continuous on the actual nonempty compact hyperspace. -/
theorem continuous_compact_diam : Continuous (fun K : NonemptyCompacts X => Metric.diam (K : Set X)) := by
  have hp : Continuous (fun K : NonemptyCompacts X => K ×ˢ K) :=
    NonemptyCompacts.continuous_prod.comp (continuous_id.prodMk continuous_id)
  have hclosed (a : ℝ) : IsClosed {K : NonemptyCompacts X | Metric.diam (K : Set X) ≤ a} := by
    have hc := (NonemptyCompacts.isClosed_subsets_of_isClosed
      (isClosed_le continuous_dist continuous_const : IsClosed {p : X × X | dist p.1 p.2 ≤ a})).preimage hp
    convert hc using 1
    ext K
    simp only [mem_setOf_eq, mem_preimage, NonemptyCompacts.coe_prod, compact_diam_le_iff]
    constructor
    · intro h p hp; exact h p.1 hp.1 p.2 hp.2
    · intro h x hx y hy; exact h (show (x, y) ∈ (K : Set X) ×ˢ (K : Set X) from ⟨hx, hy⟩)
  have hopen (a : ℝ) : IsOpen {K : NonemptyCompacts X | Metric.diam (K : Set X) < a} := by
    have hc := (NonemptyCompacts.isOpen_subsets_of_isOpen
      (isOpen_lt continuous_dist continuous_const : IsOpen {p : X × X | dist p.1 p.2 < a})).preimage hp
    convert hc using 1
    ext K
    simp only [mem_setOf_eq, mem_preimage, NonemptyCompacts.coe_prod, compact_diam_lt_iff]
    constructor
    · intro h p hp; exact h p.1 hp.1 p.2 hp.2
    · intro h x hx y hy; exact h (show (x, y) ∈ (K : Set X) ×ˢ (K : Set X) from ⟨hx, hy⟩)
  apply continuous_iff_continuousAt.mpr
  intro K
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [(hclosed a).isOpen_compl.mem_nhds (not_le.mpr ha)] with L hL
    exact not_le.mp hL
  · intro a ha
    exact (hopen a).mem_nhds ha

private theorem closed_connected_compacts :
    IsClosed {K : NonemptyCompacts X | IsConnected (K : Set X)} := by
  classical
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro K hK
  have hn : ¬ IsPreconnected (K : Set X) := fun h => hK ⟨K.nonempty, h⟩
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed K.isCompact.isClosed] at hn
  push_neg at hn
  obtain ⟨u, v, hu, hv, hcover, huv, hnu, hnv⟩ := hn
  obtain ⟨x, hxK, hxv⟩ := Set.not_subset.mp hnv
  obtain ⟨y, hyK, hyu⟩ := Set.not_subset.mp hnu
  have hxu : x ∈ u := (hcover hxK).resolve_right hxv
  have hyv : y ∈ v := (hcover hyK).resolve_left hyu
  obtain ⟨U, V, hU, hV, huU, hvV, hUV⟩ := normal_separation hu hv huv
  have hcov : (K : Set X) ⊆ U ∪ V := by
    intro z hz
    exact (hcover hz).elim (fun h => Or.inl (huU h)) (fun h => Or.inr (hvV h))
  have hnb := ((NonemptyCompacts.isOpen_subsets_of_isOpen (hU.union hV)).inter
    ((NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hU).inter
      (NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hV))).mem_nhds
        ⟨hcov, ⟨⟨x, hxK, huU hxu⟩, ⟨y, hyK, hvV hyv⟩⟩⟩
  apply Filter.mem_of_superset hnb
  rintro L ⟨hL, hLU, hLV⟩ hcon
  obtain ⟨z, _, hzU, hzV⟩ := hcon.isPreconnected U V hU hV hL hLU hLV
  exact Set.disjoint_left.mp hUV hzU hzV

/-- The compact family used in uniform persistence, with no dynamical fields. -/
theorem compact_continua_ge [CompactSpace X] (a : ℝ) :
    IsCompact {K : NonemptyCompacts X | IsConnected (K : Set X) ∧ a ≤ Metric.diam (K : Set X)} :=
  (closed_connected_compacts.inter
    (isClosed_le continuous_const continuous_compact_diam)).isCompact

end D5.S1.Dynamics.Shadowing.DendriteObstruction
