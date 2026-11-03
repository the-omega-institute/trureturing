/- GID: D5/S3/Combinatorics/Graph/HereditaryFlip/Metric
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HereditaryFlip/Metric
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Metric, mathlib/module/Mathlib.Data.Finset.SymmDiff]
   utility: none
   digest: Hereditary finite-support flip graphs have native Hamming geodesics and coordinate intervals. -/

import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Order.UpperLower.Basic

/-! Native geodesics and distance intervals for hereditary finite-support families. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HereditaryFlip.Metric

open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- Vertices are members of a family; an edge changes exactly one coordinate. -/
def flipGraph (F : Set (Finset V)) : SimpleGraph {A : Finset V // A ∈ F} where
  Adj A B := (A.val ∆ B.val).card = 1
  symm := ⟨fun A B h => by simpa [symmDiff_comm] using h⟩
  loopless := ⟨fun A => by simp⟩

private theorem card_triangle (A B C : Finset V) :
    (A ∆ C).card ≤ (A ∆ B).card + (B ∆ C).card :=
  (Finset.card_le_card (symmDiff_triangle A B C)).trans (Finset.card_union_le _ _)

/-- Every native walk must change all coordinates on which its endpoints differ. -/
theorem walk_lower_bound {F : Set (Finset V)} {A B : {s : Finset V // s ∈ F}}
    (p : (flipGraph F).Walk A B) : (A.val ∆ B.val).card ≤ p.length := by
  induction p with
  | nil => simp
  | @cons A C B h p ih =>
      have hc := card_triangle A.val C.val B.val
      have hh : (A.val ∆ C.val).card = 1 := h
      simp only [SimpleGraph.Walk.length_cons]
      omega

private theorem downward_walk {F : Set (Finset V)} (hF : IsLowerSet F)
    (T : Finset V) (hT : T ∈ F) (S : Finset V) (hST : S ⊆ T) :
    ∃ p : (flipGraph F).Walk ⟨T, hT⟩ ⟨S, hF hST hT⟩,
      p.length + S.card = T.card := by
  induction T using Finset.strongInductionOn generalizing S with
  | _ T ih =>
      by_cases heq : T = S
      · subst T
        exact ⟨.nil, by simp⟩
      · obtain ⟨x, hxT, hxS⟩ := Finset.not_subset.mp (fun hTS => heq (Finset.Subset.antisymm hTS hST))
        have hsub : S ⊆ T.erase x := by
          intro y hy
          exact Finset.mem_erase.mpr ⟨fun hyx => hxS (hyx ▸ hy), hST hy⟩
        have hE : T.erase x ∈ F := hF (Finset.erase_subset x T) hT
        obtain ⟨p, hp⟩ := ih (T.erase x) (Finset.erase_ssubset hxT) hE S hsub
        have hedge : (flipGraph F).Adj ⟨T, hT⟩ ⟨T.erase x, hE⟩ := by
          change (T ∆ T.erase x).card = 1
          have hs : T ∆ T.erase x = {x} := by
            ext y
            by_cases hyx : y = x <;> simp_all [Finset.mem_symmDiff]
          simp [hs]
        refine ⟨p.cons hedge, ?_⟩
        simp only [SimpleGraph.Walk.length_cons]
        have hcard := Finset.card_erase_add_one hxT
        omega

/-- Delete to the intersection and reverse a second deletion walk to insert to the target. -/
theorem exists_shortest_walk {F : Set (Finset V)} (hF : IsLowerSet F)
    (A B : {s : Finset V // s ∈ F}) :
    ∃ p : (flipGraph F).Walk A B, p.length = (A.val ∆ B.val).card := by
  obtain ⟨p, hp⟩ := downward_walk hF A.val A.property (A.val ∩ B.val) Finset.inter_subset_left
  obtain ⟨q, hq⟩ := downward_walk hF B.val B.property (A.val ∩ B.val) Finset.inter_subset_right
  refine ⟨p.append q.reverse, ?_⟩
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
  have h1 := Finset.card_sdiff_add_card_inter A.val B.val
  have h2 := Finset.card_sdiff_add_card_inter B.val A.val
  have hd : Disjoint (A.val \ B.val) (B.val \ A.val) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hd]
  rw [Finset.inter_comm B.val A.val] at h2
  omega

/-- An inhabited hereditary family has connected flip graph, even in an infinite ambient type. -/
theorem connected {F : Set (Finset V)} (hF : IsLowerSet F) (h0 : ∅ ∈ F) :
    (flipGraph F).Connected where
  preconnected A B := by
    obtain ⟨p, _⟩ := exists_shortest_walk hF A B
    exact ⟨p⟩
  nonempty := ⟨⟨∅, h0⟩⟩

/-- Native graph distance is symmetric-difference cardinality; reachability is proved. -/
theorem dist_eq {F : Set (Finset V)} (hF : IsLowerSet F)
    (A B : {s : Finset V // s ∈ F}) :
    (flipGraph F).dist A B = (A.val ∆ B.val).card := by
  obtain ⟨p, hp⟩ := exists_shortest_walk hF A B
  apply le_antisymm (hp ▸ SimpleGraph.dist_le p)
  have hc := connected hF (hF (Finset.empty_subset A.val) A.property)
  obtain ⟨q, hq⟩ := hc.exists_walk_length_eq_dist A B
  exact hq ▸ walk_lower_bound q

private theorem card_symmDiff_eq (S T : Finset V) :
    (S ∆ T).card + 2 * (S ∩ T).card = S.card + T.card := by
  have h1 := Finset.card_sdiff_add_card_inter S T
  have h2 := Finset.card_sdiff_add_card_inter T S
  have hd : Disjoint (S \ T) (T \ S) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hd]
  rw [Finset.inter_comm T S] at h2
  omega

/-- An intermediate vertex is on a geodesic exactly when it keeps common coordinates
and introduces no coordinate absent from both endpoints. -/
theorem interval_iff {F : Set (Finset V)} (hF : IsLowerSet F)
    (A B M : {s : Finset V // s ∈ F}) :
    (flipGraph F).dist A M + (flipGraph F).dist M B = (flipGraph F).dist A B ↔
      A.val ∩ B.val ⊆ M.val ∧ M.val ⊆ A.val ∪ B.val := by
  rw [dist_eq hF, dist_eq hF, dist_eq hF]
  have h := card_symmDiff_eq (A.val ∆ M.val) (M.val ∆ B.val)
  have hc : (A.val ∆ M.val) ∆ (M.val ∆ B.val) = A.val ∆ B.val := by
    simp [symmDiff_assoc]
  rw [hc] at h
  have heq : (A.val ∆ M.val).card + (M.val ∆ B.val).card = (A.val ∆ B.val).card ↔
      (A.val ∆ M.val) ∩ (M.val ∆ B.val) = ∅ := by
    rw [← Finset.card_eq_zero]
    omega
  rw [heq, Finset.eq_empty_iff_forall_notMem]
  simp only [Finset.mem_inter, Finset.mem_symmDiff, Finset.subset_iff, Finset.mem_union]
  constructor
  · intro hnot
    constructor
    · intro x hx
      by_contra hxm
      exact hnot x ⟨Or.inl ⟨hx.1, hxm⟩, Or.inr ⟨hx.2, hxm⟩⟩
    · intro x hxm
      by_contra hx
      push Not at hx
      exact hnot x ⟨Or.inr ⟨hxm, hx.1⟩, Or.inl ⟨hxm, hx.2⟩⟩
  · rintro ⟨hlo, hup⟩ x ⟨hAM, hMB⟩
    rcases hAM with hAM | hAM <;> rcases hMB with hMB | hMB
    · exact hAM.2 hMB.1
    · exact hAM.2 (hlo ⟨hAM.1, hMB.1⟩)
    · exact (hup hAM.1).elim hAM.2 hMB.2
    · exact hMB.2 hAM.1

end D5.S3.Combinatorics.Graph.HereditaryFlip.Metric
