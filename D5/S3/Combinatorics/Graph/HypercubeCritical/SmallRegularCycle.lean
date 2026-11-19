/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SmallRegularCycle
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SmallRegularCycle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: A nonempty finite two-regular graph of girth at least eight and fewer than sixteen vertices consists of one cycle. -/

import D5.S3.Combinatorics.Graph.Brooks.General
import D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting
import Mathlib.Combinatorics.SimpleGraph.Matching
import Batteries.Tactic.OpenPrivate

/-! A small finite two-regular graph of girth at least eight has one cycle.
The cycle is obtained from actual edges, not supplied as a skeleton premise. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SmallRegularCycle

open SimpleGraph

variable {V : Type*} [Fintype V] [Nonempty V]
variable (H : SimpleGraph V) [DecidableRel H.Adj]

private theorem small_two_regular_cycle
    (hdegree : ∀ v, H.degree v = 2)
    (hg : (8 : ℕ∞) ≤ H.egirth) (hcard : Fintype.card V < 16) :
    ∃ a, ∃ p : H.Walk a a, p.IsCycle ∧ p.length = Fintype.card V ∧
      (∀ v, v ∈ p.support) ∧ Nonempty (cycleGraph p.length ≃g H) := by
  classical
  have hcycles : H.IsCycles := by
    intro v _
    rw [H.ncard_neighborSet, hdegree]
  have hneighbor (v : V) : (H.neighborSet v).Nonempty := by
    apply (H.degree_pos_iff_nonempty).mp
    rw [hdegree]
    norm_num
  let a : V := Classical.choice inferInstance
  obtain ⟨p, hp, hpc⟩ := hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := H.connectedComponentMk a) (v := a) rfl (hneighbor a)
  have hcomponent (v : V) : H.Reachable a v ↔ v ∈ p.support := by
    rw [← p.mem_verts_toSubgraph, hpc, ConnectedComponent.mem_supp_iff,
      ConnectedComponent.eq]
    exact reachable_comm
  have hp8 : 8 ≤ p.length := by
    exact_mod_cast hg.trans hp.egirth_le_length
  have hcover (v : V) : v ∈ p.support := by
    by_contra hv
    obtain ⟨q, hq, hqc⟩ := hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (c := H.connectedComponentMk v) (v := v) rfl (hneighbor v)
    have hq8 : 8 ≤ q.length := by
      exact_mod_cast hg.trans hq.egirth_le_length
    have hdis : Disjoint p.support.toFinset q.support.toFinset := by
      apply Finset.disjoint_left.mpr
      intro w hwp hwq
      have hwpr := (hcomponent w).mpr (List.mem_toFinset.mp hwp)
      have hwqr : H.Reachable v w := by
        obtain ⟨r, s, _⟩ := q.mem_support_iff_exists_append.mp (List.mem_toFinset.mp hwq)
        exact r.reachable
      exact hv ((hcomponent v).mp (hwpr.trans hwqr.symm))
    have hc : p.length + q.length ≤ Fintype.card V := by
      have hle := Finset.card_le_card
        (Finset.subset_univ (p.support.toFinset ∪ q.support.toFinset))
      rw [Finset.card_union_of_disjoint hdis,
        hp.support_toFinset_card, hq.support_toFinset_card, Finset.card_univ] at hle
      exact hle
    omega
  have hconnected : H.Connected := by
    refine ⟨?_⟩
    intro x y
    exact ((hcomponent x).mpr (hcover x)).symm.trans
      ((hcomponent y).mpr (hcover y))
  have hmax : H.maxDegree ≤ 2 := H.maxDegree_le_of_forall_degree_le 2
    (fun v => by rw [hdegree])
  have hiso := SimpleGraph.cycle_iso_of_connected_degree_le_two H hconnected hmax p hp
  have hlen : p.length = Fintype.card V := by
    have hu : p.support.toFinset = (Finset.univ : Finset V) := by
      ext v
      simp [hcover v]
    rw [← hp.support_toFinset_card, hu, Finset.card_univ]
  exact ⟨a, p, hp, hlen, hcover, hiso⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.SmallRegularCycle
