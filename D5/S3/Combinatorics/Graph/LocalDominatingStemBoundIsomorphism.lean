/- GID: D5/S3/Combinatorics/Graph/LocalDominatingStemBoundIsomorphism
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LocalDominatingStemBoundIsomorphism
   mirror-E: none(waiver:finite-combinatorial-identities)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finite]
   utility: none
   digest: One-copy hub replication is isomorphic to the original one-stem graph. -/

import D5.S3.Combinatorics.Graph.LocalDominatingStemBoundResidual

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.LocalDominatingStemBoundIsomorphism

open Finset DominatingSetAverage LocalDominatingStemBoundStructure
  LocalDominatingStemBoundReplication LocalDominatingStemBoundResidual

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The sole copy keeps its labels, and the hub and its pendant restore the removed vertices. -/
def oneCopyMap (G : SimpleGraph V) (v w : V) :
    RepVertex 1 {x // x ∈ remaining G v} → V
  | Sum.inl (_, x) => x.val
  | Sum.inr k => if k = 0 then v else w

private theorem remaining_ne_leaf (G : SimpleGraph V) (v w : V)
    (hL : leafNeighbors G v = {w}) (x : {x // x ∈ remaining G v}) : x.val ≠ w := by
  intro hx
  have hw : w ∈ leafNeighbors G v := by rw [hL]; simp
  have hnot := (mem_remaining.mp x.property).2
  exact hnot (hx ▸ mem_leafNeighbors.mp hw)

private theorem oneCopyMap_bijective (G : SimpleGraph V) (v w : V)
    (hL : leafNeighbors G v = {w}) : Function.Bijective (oneCopyMap G v w) := by
  classical
  have hw : w ∈ leafNeighbors G v := by rw [hL]; simp
  have hne : v ≠ w := (mem_leafNeighbors.mp hw).1.ne
  constructor
  · intro x y heq
    cases x with
    | inl x => cases y with
      | inl y =>
        apply congrArg Sum.inl
        apply Prod.ext
        · exact Subsingleton.elim _ _
        · exact Subtype.ext heq
      | inr y =>
        fin_cases y
        · exact False.elim ((mem_remaining.mp x.2.property).1 heq)
        · exact False.elim (remaining_ne_leaf G v w hL x.2 heq)
    | inr x => cases y with
      | inl y =>
        fin_cases x
        · exact False.elim ((mem_remaining.mp y.2.property).1 heq.symm)
        · exact False.elim (remaining_ne_leaf G v w hL y.2 heq.symm)
      | inr y =>
        fin_cases x <;> fin_cases y
        · rfl
        · exact False.elim (hne heq)
        · exact False.elim (hne heq.symm)
        · rfl
  · intro x
    by_cases hxv : x = v
    · exact ⟨Sum.inr 0, by simpa [oneCopyMap] using hxv.symm⟩
    by_cases hxw : x = w
    · exact ⟨Sum.inr 1, by simpa [oneCopyMap] using hxw.symm⟩
    have hx : x ∈ remaining G v := by
      simp only [remaining, mem_sdiff, mem_univ, true_and, mem_insert, hL,
        mem_singleton, not_or]
      exact ⟨hxv,hxw⟩
    exact ⟨Sum.inl (0, ⟨x,hx⟩), rfl⟩

/-- The restored vertex labels give a graph isomorphism for a stem with exactly one leaf. -/
noncomputable def oneCopyIso (G : SimpleGraph V) (v w : V)
    (hL : leafNeighbors G v = {w}) :
    replicated (residualGraph G v) (residualNeighbors G v) 1 ≃g G := by
  classical
  have hw : w ∈ leafNeighbors G v := by rw [hL]; simp
  have hadj : G.Adj v w := (mem_leafNeighbors.mp hw).1
  have hleaf : Leaf G w := (mem_leafNeighbors.mp hw).2
  refine { Equiv.ofBijective (oneCopyMap G v w) (oneCopyMap_bijective G v w hL) with
    map_rel_iff' := ?_ }
  intro x y
  change G.Adj (oneCopyMap G v w x) (oneCopyMap G v w y) ↔
    (replicated (residualGraph G v) (residualNeighbors G v) 1).Adj x y
  cases x with
  | inl x => cases y with
    | inl y =>
      have heq : x.1 = y.1 := Subsingleton.elim _ _
      simp only [oneCopyMap, replicated, heq, true_and]
      rfl
    | inr y =>
      fin_cases y
      · simpa [oneCopyMap, replicated] using (G.adj_comm x.2.val v)
      · have hn : ¬ G.Adj x.2.val w := by
          intro hh
          exact (mem_remaining.mp x.2.property).1 (leaf_adj_unique hleaf hadj.symm hh.symm)
        simp [oneCopyMap, replicated, hn]
  | inr x => cases y with
    | inl y =>
      fin_cases x
      · simp [oneCopyMap, replicated]
      · have hn : ¬ G.Adj w y.2.val := by
          intro hh
          exact (mem_remaining.mp y.2.property).1 (leaf_adj_unique hleaf hadj.symm hh)
        simp [oneCopyMap, replicated, hn]
    | inr y =>
      fin_cases x <;> fin_cases y <;> simp [oneCopyMap, replicated, hadj, hadj.symm]

/-- The one-copy average is the global average of the original graph. -/
theorem one_copy_avd (G : SimpleGraph V) (v w : V)
    (hL : leafNeighbors G v = {w}) :
    avd (replicated (residualGraph G v) (residualNeighbors G v) 1) = avd G :=
  avd_iso (oneCopyIso G v w hL)

/-- The extremal residual mean transfers through the one-copy graph isomorphism. -/
theorem global_equality_from_replication {G : SimpleGraph V} (v : V)
    (hl : leafCount G v = 1)
    (hfamilies : partialDomSets G v = residualDomSets G v)
    (hmean : familyAverage (residualDomSets G v) = 2 * (remaining G v).card / 3) :
    avd G = 2 * (Fintype.card V : ℚ) / 3 := by
  classical
  obtain ⟨w,hw⟩ := card_eq_one.mp (show (leafNeighbors G v).card = 1 from hl)
  rw [← one_copy_avd G v w hw, replicated_average]
  have hc : (partialSets (residualGraph G v) (residualNeighbors G v)).card =
      (domSets (residualGraph G v)).card := by
    rw [residualPartial_card, hfamilies, residualDomSets_card]
  have hα : familyAverage (partialSets (residualGraph G v) (residualNeighbors G v)) =
      2 * (remaining G v).card / 3 := by
    rw [residualPartial_average, hfamilies, hmean]
  have hβ : avd (residualGraph G v) = 2 * (remaining G v).card / 3 := by
    rw [← residualDomSets_average, hmean]
  have hb : ((domSets (residualGraph G v)).card : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (domSets_card_pos (residualGraph G v)))
  have hn : ((remaining G v).card : ℚ) + 2 = Fintype.card V := by
    have hh := remaining_card (G := G) v
    rw [hl] at hh
    exact_mod_cast (by omega : (remaining G v).card + 2 = Fintype.card V)
  rw [hc,hα,hβ]
  norm_num
  apply (div_eq_iff (by positivity :
    (2 * (domSets (residualGraph G v)).card + (domSets (residualGraph G v)).card : ℚ) ≠ 0)).mpr
  nlinarith

end D5.S3.Combinatorics.Graph.LocalDominatingStemBoundIsomorphism
