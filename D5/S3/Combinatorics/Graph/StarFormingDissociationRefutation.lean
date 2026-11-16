/- GID: D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarFormingDissociationRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex, mathlib/module/Mathlib.Data.Finset.Powerset, mathlib/module/Mathlib.Data.Finset.Max]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.claim; result=D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.result; claim=D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.claim
   digest: A ten-vertex bipartite graph refutes equality of 2-independence and upper 2-star formation. -/

import D5.S3.Combinatorics.Graph.StarForming.Foundations.Invariants
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FinCases

namespace D5.S3.Combinatorics.Graph.StarFormingDissociationRefutation

/-- Conjecture 4.2, with finite vertex types represented by Fin n. -/
def claim : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
  G.Colorable 2 → beta G 2 = SF G 2

/-- The original sixteen-edge H₀ certificate, reused by port compositions. -/
def edges : Finset (Fin 10 × Fin 10) :=
  {(0,5), (0,6), (0,9), (1,5), (1,6), (1,8), (2,8), (2,9),
   (3,6), (3,7), (3,8), (3,9), (4,5), (4,7), (4,8), (4,9)}

/-- The original ten-vertex bipartite counterexample H₀. -/
def counterGraph : SimpleGraph (Fin 10) where
  Adj i j := (i, j) ∈ edges ∨ (j, i) ∈ edges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by intro i h; fin_cases i <;> simp [edges] at h⟩

instance : DecidableRel counterGraph.Adj :=
  inferInstanceAs (DecidableRel (fun i j => (i, j) ∈ edges ∨ (j, i) ∈ edges))

/-- The original minimal six-set, with selected attachment ports 0 and 5. -/
def selected : Finset (Fin 10) := {0, 1, 2, 5, 6, 7}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Expand and independently verify all 1024 subset implications.
/-- The original H₀ certificates, exposed for exact composition consumers.
No graph, selection, or finite checking argument is replaced. -/
theorem h0_properties : counterGraph.Colorable 2 ∧
    IsMinimalStarForming counterGraph 2 selected ∧ beta counterGraph 2 ≤ 5 := by
  have coloring : counterGraph.Colorable 2 := by
    refine ⟨SimpleGraph.Coloring.mk (fun v => if v.val < 5 then 0 else 1) ?_⟩
    change ∀ i j : Fin 10, counterGraph.Adj i j →
      (if i.val < 5 then (0 : Fin 2) else 1) ≠ (if j.val < 5 then 0 else 1)
    intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  have hlocal : LocalTwo counterGraph selected := by
    intro v
    fin_cases v <;> decide +kernel
  have proper : ∀ T ∈ selected.powerset, T ≠ selected → ¬ LocalTwo counterGraph T := by
    simp only [selected, ← Finset.insert_empty, Finset.powerset_insert,
      Finset.powerset_empty, Finset.forall_mem_union, Finset.forall_mem_image,
      Finset.forall_mem_insert, Finset.forall_mem_empty_iff, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  have minimal : IsMinimalStarForming counterGraph 2 selected := by
    refine ⟨(starForming_two_iff counterGraph selected).mpr hlocal, ?_⟩
    intro T hT hstar
    exact proper T (Finset.mem_powerset.mpr hT.subset) hT.ne
      ((starForming_two_iff counterGraph T).mp hstar)
  have huniv : (Finset.univ : Finset (Fin 10)) = {0,1,2,3,4,5,6,7,8,9} := by
    decide +kernel
  have subsets : ∀ T ∈ ({0,1,2,3,4,5,6,7,8,9} : Finset (Fin 10)).powerset,
      T.card = 6 → ¬ IsKIndependent counterGraph 2 T := by
    simp only [← Finset.insert_empty, Finset.powerset_insert,
      Finset.powerset_empty, Finset.forall_mem_union, Finset.forall_mem_image,
      Finset.forall_mem_insert, Finset.forall_mem_empty_iff, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  have six : ∀ T ∈ (Finset.univ : Finset (Fin 10)).powersetCard 6,
      ¬ IsKIndependent counterGraph 2 T := by
    intro T hT
    apply subsets T
    · rw [← huniv]
      exact Finset.mem_powerset.mpr (Finset.subset_univ T)
    · exact (Finset.mem_powersetCard.mp hT).2
  have upper : beta counterGraph 2 ≤ 5 := by
    apply Finset.sup_le
    intro I hI
    have hi := (Finset.mem_filter.mp hI).2
    by_contra hcard
    obtain ⟨T, hTI, hTcard⟩ := Finset.exists_subset_card_eq (by omega : 6 ≤ I.card)
    apply six T (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ T, hTcard⟩)
    intro v hv
    exact lt_of_le_of_lt
      (Finset.card_le_card (Finset.filter_subset_filter (counterGraph.Adj v) hTI))
      (hi v (hTI hv))
  exact ⟨coloring, minimal, upper⟩

/-- The bipartite equality fails at the original ten-vertex certificate. -/
theorem result : ¬ claim := by
  obtain ⟨coloring, minimal, upper⟩ := h0_properties
  have lower : 6 ≤ SF counterGraph 2 := by
    classical
    have hmem : selected ∈ Finset.univ.powerset.filter
        (IsMinimalStarForming counterGraph 2) :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), minimal⟩
    have hcard : selected.card = 6 := by decide +kernel
    exact hcard ▸ Finset.le_sup (f := Finset.card) hmem
  intro hclaim
  have heq := hclaim 10 counterGraph coloring
  omega

end D5.S3.Combinatorics.Graph.StarFormingDissociationRefutation
