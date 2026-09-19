/- GID: D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCycleIntervals
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/CrownOrderPolytopeCycleIntervals
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCCP]
   utility: none
   digest: Proper original-vertex crown blocks are cyclic intervals after cutting outside them. -/

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

/- Removing a vertex outside a proper actual block turns that block into one interval. -/
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

end D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration
