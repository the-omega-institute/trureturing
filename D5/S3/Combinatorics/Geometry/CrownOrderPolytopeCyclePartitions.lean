/- GID: D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCyclePartitions
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/CrownOrderPolytopeCyclePartitions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCCP]
   utility: none
   digest: Connected crown partitions are reconstructed exactly from their cyclic boundary cuts. -/

/- Library search (2026-09-19): pinned Mathlib supplies `cycleGraph`, reachability
   setoids, and connected components, but no equivalence between cyclic edge cuts and
   connected vertex partitions.  The construction below uses those graph primitives. -/

import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Tactic
import D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration

open D5.S3.Combinatorics.Geometry.CrownOrderPolytope

private def cycleCutRank {N : ℕ} (c v : Fin N) : ℕ :=
  if v.val ≤ c.val then v.val + (N - 1 - c.val) else v.val - c.val - 1

private theorem cycleCutRank_lt {N : ℕ} (c v : Fin N) (hv : v ≠ c) :
    cycleCutRank c v < N - 1 := by
  unfold cycleCutRank
  by_cases hvc : v.val ≤ c.val
  · simp only [if_pos hvc]
    have hne : v.val ≠ c.val := fun h => hv (Fin.ext h)
    omega
  · simp only [if_neg hvc]
    omega

private theorem cycleCutRank_injective {N : ℕ} (c : Fin N) :
    Function.Injective (cycleCutRank c) := by
  intro u v h
  unfold cycleCutRank at h
  by_cases huc : u.val ≤ c.val <;> by_cases hvc : v.val ≤ c.val
  · simp only [if_pos huc, if_pos hvc] at h
    exact Fin.ext (by omega)
  · simp only [if_pos huc, if_neg hvc] at h
    exfalso
    omega
  · simp only [if_neg huc, if_pos hvc] at h
    exfalso
    omega
  · simp only [if_neg huc, if_neg hvc] at h
    exact Fin.ext (by omega)

private theorem cycleGraph_adj_cycleCutRank {N : ℕ} (hN : 4 ≤ N)
    (c u v : Fin N) (hu : u ≠ c) (hv : v ≠ c)
    (hadj : (SimpleGraph.cycleGraph N).Adj u v) :
    cycleCutRank c u + 1 = cycleCutRank c v ∨
      cycleCutRank c v + 1 = cycleCutRank c u := by
  have hedges :
      u.val = v.val + 1 ∨ v.val = u.val + 1 ∨
        (u.val = 0 ∧ v.val = N - 1) ∨ (v.val = 0 ∧ u.val = N - 1) := by
    rw [SimpleGraph.cycleGraph_adj'] at hadj
    rcases hadj with huv | hvu
    · by_cases hvleu : v ≤ u
      · left
        have hdiff : u.val - v.val = 1 := by
          simpa [Fin.sub_val_of_le hvleu] using huv
        omega
      · right
        right
        left
        have hcast : ((u - v).val : ℤ) = 1 := congrArg Int.ofNat huv
        rw [Fin.intCast_val_sub_eq_sub_add_ite] at hcast
        simp [show ¬v ≤ u from hvleu] at hcast
        constructor <;> omega
    · by_cases hulev : u ≤ v
      · right
        left
        have hdiff : v.val - u.val = 1 := by
          simpa [Fin.sub_val_of_le hulev] using hvu
        omega
      · right
        right
        right
        have hcast : ((v - u).val : ℤ) = 1 := congrArg Int.ofNat hvu
        rw [Fin.intCast_val_sub_eq_sub_add_ite] at hcast
        simp [show ¬u ≤ v from hulev] at hcast
        constructor <;> omega
  have huc : u.val ≠ c.val := fun h => hu (Fin.ext h)
  have hvc : v.val ≠ c.val := fun h => hv (Fin.ext h)
  unfold cycleCutRank
  rcases hedges with h | h | h | h <;>
    by_cases hule : u.val ≤ c.val <;> by_cases hvle : v.val ≤ c.val <;>
      simp only [hule, hvle, if_true, if_false] <;> omega

/- Cutting at any vertex outside an endpoint-free actual block turns that block into one
   nonempty integer interval.  This is the source's cyclic-consecutive-block classification,
   now for the real CCP relation rather than an abstract connected subset. -/
private theorem crownPartition_originalBlock_cycleCutInterval {n : ℕ} (hn : 2 ≤ n)
    (P : CrownConnectedCompatiblePartition n) (i c : Fin (2 * n))
    (hbottom : ¬ P.toSetoid.r (.vertex i) .bottom)
    (htop : ¬ P.toSetoid.r (.vertex i) .top)
    (hc : ¬ P.toSetoid.r (.vertex i) (.vertex c)) :
    ∃ a b : ℕ, a ≤ b ∧ b < 2 * n - 1 ∧
      ∀ v : Fin (2 * n),
        P.toSetoid.r (.vertex i) (.vertex v) ↔
          a ≤ cycleCutRank c v ∧ cycleCutRank c v ≤ b := by
  classical
  let block : Finset (Fin (2 * n)) :=
    Finset.univ.filter fun v => P.toSetoid.r (.vertex i) (.vertex v)
  let ranks : Finset ℕ := block.image (cycleCutRank c)
  have hi_block : i ∈ block := by simp [block]
  have hranks : ranks.Nonempty :=
    ⟨cycleCutRank c i, Finset.mem_image.mpr ⟨i, hi_block, rfl⟩⟩
  let a := ranks.min' hranks
  let b := ranks.max' hranks
  have ha_mem : a ∈ ranks := Finset.min'_mem ranks hranks
  have hb_mem : b ∈ ranks := Finset.max'_mem ranks hranks
  obtain ⟨amin, hamin_block, hamin_rank⟩ := Finset.mem_image.mp ha_mem
  obtain ⟨bmax, hbmax_block, hbmax_rank⟩ := Finset.mem_image.mp hb_mem
  have hamin : P.toSetoid.r (.vertex i) (.vertex amin) := by
    simpa [block] using hamin_block
  have hbmax : P.toSetoid.r (.vertex i) (.vertex bmax) := by
    simpa [block] using hbmax_block
  have hamin_ne : amin ≠ c := fun h => hc (h ▸ hamin)
  have hbmax_ne : bmax ≠ c := fun h => hc (h ▸ hbmax)
  have hab : a ≤ b := Finset.min'_le_max' ranks hranks
  have hb_lt : b < 2 * n - 1 := by
    rw [← hbmax_rank]
    exact cycleCutRank_lt c bmax hbmax_ne
  refine ⟨a, b, hab, hb_lt, fun v => ?_⟩
  constructor
  · intro hv
    have hv_block : v ∈ block := by simp [block, hv]
    have hv_rank : cycleCutRank c v ∈ ranks :=
      Finset.mem_image.mpr ⟨v, hv_block, rfl⟩
    exact ⟨Finset.min'_le ranks _ hv_rank, Finset.le_max' ranks _ hv_rank⟩
  · rintro ⟨hav, hvb⟩
    have hv_rank : cycleCutRank c v ∈ ranks := by
      by_cases hva : cycleCutRank c v = a
      · simpa [hva] using ha_mem
      · have hav_strict : a < cycleCutRank c v := lt_of_le_of_ne hav (Ne.symm hva)
        let u : {j // P.toSetoid.r (.vertex i) (.vertex j)} := ⟨amin, hamin⟩
        let w : {j // P.toSetoid.r (.vertex i) (.vertex j)} := ⟨bmax, hbmax⟩
        obtain ⟨p⟩ := (crownPartition_originalBlock_cycleGraph_connected hn P i hbottom htop)
          u w
        let lower : Set {j // P.toSetoid.r (.vertex i) (.vertex j)} :=
          {x | cycleCutRank c x.1 < cycleCutRank c v}
        have hu_lower : u ∈ lower := by
          change cycleCutRank c amin < cycleCutRank c v
          rw [hamin_rank]
          exact hav_strict
        have hw_lower : w ∉ lower := by
          change ¬cycleCutRank c bmax < cycleCutRank c v
          rw [hbmax_rank]
          omega
        obtain ⟨d, _, hd_lower, hd_upper⟩ :=
          p.exists_boundary_dart lower hu_lower hw_lower
        have hdfst_ne : d.fst.1 ≠ c := fun h => hc (h ▸ d.fst.2)
        have hdsnd_ne : d.snd.1 ≠ c := fun h => hc (h ▸ d.snd.2)
        have hstep := cycleGraph_adj_cycleCutRank (N := 2 * n) (by omega)
          c d.fst.1 d.snd.1 hdfst_ne hdsnd_ne d.adj
        have hfst : cycleCutRank c d.fst.1 < cycleCutRank c v := hd_lower
        have hsnd : cycleCutRank c v ≤ cycleCutRank c d.snd.1 := Nat.le_of_not_gt hd_upper
        have hsnd_eq : cycleCutRank c d.snd.1 = cycleCutRank c v := by
          rcases hstep with hstep | hstep <;> omega
        have hdsnd_block : d.snd.1 ∈ block := by
          simp only [block, Finset.mem_filter, Finset.mem_univ, true_and]
          exact d.snd.2
        exact Finset.mem_image.mpr ⟨d.snd.1, hdsnd_block, hsnd_eq⟩
    obtain ⟨witness, hwitness_block, hwitness_rank⟩ := Finset.mem_image.mp hv_rank
    have hvw : v = witness := cycleCutRank_injective c hwitness_rank.symm
    simpa [block, hvw] using hwitness_block

/-- The cycle edges internal to the blocks of a vertex partition. -/
private def cyclePartitionGraph {N : ℕ} (s : Setoid (Fin N)) : SimpleGraph (Fin N) where
  Adj u v := s.r u v ∧ (SimpleGraph.cycleGraph N).Adj u v
  symm.symm _ _ h := ⟨s.symm h.1, h.2.symm⟩
  loopless.irrefl _ h := h.2.ne rfl

/-- A partition whose blocks induce connected subgraphs of the cycle. -/
private structure ConnectedCyclePartition (N : ℕ) where
  toSetoid : Setoid (Fin N)
  connected : ∀ {u v}, toSetoid.r u v → (cyclePartitionGraph toSetoid).Reachable u v

private theorem cyclePartitionGraph_reachable_iff {N : ℕ} (P : ConnectedCyclePartition N)
    (u v : Fin N) :
    (cyclePartitionGraph P.toSetoid).Reachable u v ↔ P.toSetoid.r u v := by
  refine ⟨?_, P.connected⟩
  rintro ⟨p⟩
  induction p with
  | nil => exact P.toSetoid.refl _
  | @cons a b c hab _ ih => exact P.toSetoid.trans hab.1 ih

/-- The cyclic edges crossing between distinct blocks, indexed by their first endpoint. -/
private noncomputable def cycleBoundaryCuts {N : ℕ} [NeZero N]
    (P : ConnectedCyclePartition N) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter fun u => ¬ P.toSetoid.r u (u + 1)

/-- Delete the cyclic edges indexed by a cut set. -/
private def cycleGraphWithCuts {N : ℕ} [NeZero N]
    (cuts : Finset (Fin N)) : SimpleGraph (Fin N) where
  Adj u v := (SimpleGraph.cycleGraph N).Adj u v ∧
    ¬ ((u ∈ cuts ∧ v = u + 1) ∨ (v ∈ cuts ∧ u = v + 1))
  symm.symm _ _ h := ⟨h.1.symm, by simpa [or_comm] using h.2⟩
  loopless.irrefl u h := h.1.ne rfl

/-- The connected-component partition obtained after making the prescribed cyclic cuts. -/
private def connectedCyclePartitionOfCuts {N : ℕ} [NeZero N] (cuts : Finset (Fin N)) :
    ConnectedCyclePartition N where
  toSetoid := (cycleGraphWithCuts cuts).reachableSetoid
  connected h := h.mono fun _ _ hadj => ⟨hadj.reachable, hadj.1⟩

private theorem cycleGraphWith_boundaryCuts {N : ℕ} [NeZero N] (hN : 3 ≤ N)
    (P : ConnectedCyclePartition N) :
    cycleGraphWithCuts (cycleBoundaryCuts P) = cyclePartitionGraph P.toSetoid := by
  ext u v
  constructor
  · rintro ⟨huv, hcut⟩
    refine ⟨?_, huv⟩
    rw [SimpleGraph.cycleGraph_adj'] at huv
    rcases huv with huv | huv
    · have hpred : u = v + 1 := by
        apply (sub_eq_iff_eq_add').mp
        apply Fin.ext
        change (u - v).val = 1 % N
        rw [Nat.mod_eq_of_lt (by omega)]
        exact huv
      by_contra hs
      apply hcut
      right
      refine ⟨?_, hpred⟩
      simp only [cycleBoundaryCuts, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hpred]
      exact fun hvu => hs (P.toSetoid.symm hvu)
    · have hsucc : v = u + 1 := by
        apply (sub_eq_iff_eq_add').mp
        apply Fin.ext
        change (v - u).val = 1 % N
        rw [Nat.mod_eq_of_lt (by omega)]
        exact huv
      by_contra hs
      apply hcut
      left
      refine ⟨?_, hsucc⟩
      simpa [cycleBoundaryCuts, hsucc] using hs
  · rintro ⟨hs, huv⟩
    refine ⟨huv, ?_⟩
    rintro (⟨hcut, rfl⟩ | ⟨hcut, rfl⟩)
    · simp only [cycleBoundaryCuts, Finset.mem_filter, Finset.mem_univ, true_and] at hcut
      exact hcut hs
    · simp only [cycleBoundaryCuts, Finset.mem_filter, Finset.mem_univ, true_and] at hcut
      exact hcut (P.toSetoid.symm hs)

/- Taking all actual cyclic block boundaries and then taking the connected components
   of the cut graph recovers the original partition exactly. -/
private theorem connectedCyclePartitionOfCuts_boundaryCuts {N : ℕ} [NeZero N] (hN : 3 ≤ N)
    (P : ConnectedCyclePartition N) :
    (connectedCyclePartitionOfCuts (cycleBoundaryCuts P)).toSetoid = P.toSetoid := by
  apply Setoid.ext
  intro u v
  change (cycleGraphWithCuts (cycleBoundaryCuts P)).Reachable u v ↔ P.toSetoid.r u v
  rw [cycleGraphWith_boundaryCuts hN P]
  exact cyclePartitionGraph_reachable_iff P u v

/- The no-cut case is exactly the exceptional partition with one block. -/
private theorem cycleBoundaryCuts_eq_empty_iff {N : ℕ} [NeZero N] (hN : 3 ≤ N)
    (P : ConnectedCyclePartition N) :
    cycleBoundaryCuts P = ∅ ↔ ∀ u v, P.toSetoid.r u v := by
  constructor
  · intro hcuts u v
    have hgraph : cycleGraphWithCuts (cycleBoundaryCuts P) = SimpleGraph.cycleGraph N := by
      rw [hcuts]
      ext a b
      simp [cycleGraphWithCuts]
    have hreach : (cycleGraphWithCuts (cycleBoundaryCuts P)).Reachable u v := by
      rw [hgraph]
      exact SimpleGraph.cycleGraph_preconnected u v
    rw [cycleGraphWith_boundaryCuts hN P] at hreach
    exact (cyclePartitionGraph_reachable_iff P u v).mp hreach
  · intro hall
    ext u
    simp [cycleBoundaryCuts, hall]

/-- The directed quotient relation induced by the actual crown order on a connected
    cyclic partition. -/
private def crownCycleBlockRel {n : ℕ} (P : ConnectedCyclePartition (2 * n))
    (C D : Quotient P.toSetoid) : Prop :=
  ∃ i j : Fin (2 * n),
    Quotient.mk'' i = C ∧ Quotient.mk'' j = D ∧ crownRelation n i j

/- Between distinct quotient blocks, every directed crown relation crosses an actual
   cyclic boundary cut, and every such directed boundary witnesses the quotient relation. -/
private theorem crownCycleBlockRel_iff_boundaryCut {n : ℕ} [NeZero (2 * n)] (hn : 2 ≤ n)
    (P : ConnectedCyclePartition (2 * n)) (C D : Quotient P.toSetoid) (hne : C ≠ D) :
    crownCycleBlockRel P C D ↔
      ∃ i j : Fin (2 * n),
        Quotient.mk'' i = C ∧ Quotient.mk'' j = D ∧ crownRelation n i j ∧
          ((i ∈ cycleBoundaryCuts P ∧ j = i + 1) ∨
            (j ∈ cycleBoundaryCuts P ∧ i = j + 1)) := by
  constructor
  · rintro ⟨i, j, hi, hj, hij⟩
    have hnrel : ¬ P.toSetoid.r i j := by
      intro hrel
      apply hne
      rw [← hi, ← hj]
      exact Quotient.sound hrel
    refine ⟨i, j, hi, hj, hij, ?_⟩
    rcases hij.2 with hnext | hprev
    · left
      have hsucc : j = i + 1 := by
        apply Fin.ext
        simpa [Fin.add_def] using hnext
      refine ⟨?_, hsucc⟩
      simpa [cycleBoundaryCuts, hsucc] using hnrel
    · right
      have hpred : i = j + 1 := by
        apply Fin.ext
        simp only [Fin.add_def, Fin.val_one',
          Nat.mod_eq_of_lt (show 1 < 2 * n by omega)]
        by_cases hi0 : i.val = 0
        · rw [hi0, zero_add, Nat.mod_eq_of_lt (by omega)] at hprev
          rw [hprev, show 2 * n - 1 + 1 = 2 * n by omega, Nat.mod_self]
          exact hi0
        · have hipos : 0 < i.val := Nat.pos_of_ne_zero hi0
          have hform : i.val + 2 * n - 1 = (i.val - 1) + 2 * n := by omega
          have himod : ((i.val - 1) + 2 * n) % (2 * n) = i.val - 1 := by
            rw [Nat.add_mod_right]
            exact Nat.mod_eq_of_lt (by omega)
          rw [hform, himod] at hprev
          rw [hprev, show i.val - 1 + 1 = i.val by omega, Nat.mod_eq_of_lt i.isLt]
      refine ⟨?_, hpred⟩
      simp only [cycleBoundaryCuts, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hpred]
      exact fun hji => hnrel (P.toSetoid.symm hji)
  · rintro ⟨i, j, hi, hj, hij, _⟩
    exact ⟨i, j, hi, hj, hij⟩

end D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration
