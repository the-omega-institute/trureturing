/- GID: D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.claim; result=D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.result; claim=D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.claim
   digest: C4-free pair ownership, finite Pappus/Heawood proofs and canonical dissociation obstruction. -/

import D5.S3.Combinatorics.Graph.SubQuorum.C4RepresentativeBounds
import D5.S3.Combinatorics.Graph.StarForming.HeawoodParameters
import D5.S3.Combinatorics.Graph.StarForming.HeawoodCertificates

/-! Actual finite Pappus and Heawood certificates from the exact received Sahbi
source revision 48728b42d39ab3de5de251c61da5a404ec418a69, Apache-2.0.
The actual Pappus dissociation ten-set refutes the cubic C4-free half-order
claim. General representative proofs are imported without weakening hypotheses.
Finite positive consequences retain their own separate utility-review duty. -/

namespace D5.S3.Combinatorics.Graph.SubQuorum.C4FreeRepresentatives
open StarFormingDissociationRefutation
open StarForming
open scoped BigOperators
open DoubleStarGrafting

def pappusNeighbors (vertex : Fin 18) : List Nat :=
  match vertex.val with
  | 0 => [1, 5, 17]
  | 1 => [0, 2, 8]
  | 2 => [1, 3, 13]
  | 3 => [2, 4, 10]
  | 4 => [3, 5, 15]
  | 5 => [0, 4, 6]
  | 6 => [5, 7, 11]
  | 7 => [6, 8, 14]
  | 8 => [1, 7, 9]
  | 9 => [8, 10, 16]
  | 10 => [3, 9, 11]
  | 11 => [6, 10, 12]
  | 12 => [11, 13, 17]
  | 13 => [2, 12, 14]
  | 14 => [7, 13, 15]
  | 15 => [4, 14, 16]
  | 16 => [9, 15, 17]
  | 17 => [0, 12, 16]
  | _ => []

def pappusSelected : List Nat := [0, 1, 4, 6, 7, 9, 10, 12, 13, 15]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem pappus_regular_bipartite_certificate :
    (∀ vertex : Fin 18, (pappusNeighbors vertex).length = 3 ∧
      (pappusNeighbors vertex).Nodup ∧
      ∀ neighbor, neighbor ∈ pappusNeighbors vertex →
        neighbor < 18 ∧ neighbor % 2 ≠ vertex.val % 2) ∧
    (∀ first second : Fin 18,
      second.val ∈ pappusNeighbors first ↔ first.val ∈ pappusNeighbors second) := by
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem pappus_no_four_cycle_certificate :
    ∀ first second : Fin 18, first ≠ second →
      ((pappusNeighbors first).filter (fun vertex =>
        (pappusNeighbors second).contains vertex)).length ≤ 1 := by
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem pappus_dissociation_certificate :
    pappusSelected.length = 10 ∧ pappusSelected.Nodup ∧
    (∀ vertex, vertex ∈ pappusSelected → vertex < 18) ∧
    (∀ vertex : Fin 18, vertex.val ∈ pappusSelected →
      ((pappusNeighbors vertex).filter (fun neighbor =>
        pappusSelected.contains neighbor)).length ≤ 1) := by
  decide


def pappusGraph : SimpleGraph (Fin 18) where
  Adj v w := w.val ∈ pappusNeighbors v
  symm := ⟨fun v w h => (pappus_regular_bipartite_certificate.2 v w).mp h⟩
  loopless := ⟨by decide +kernel⟩
instance : DecidableRel pappusGraph.Adj := fun v w => inferInstanceAs
  (Decidable (w.val ∈ pappusNeighbors v))

def pappusSet : Finset (Fin 18) := Finset.univ.filter (fun v => v.val ∈ pappusSelected)

private theorem pappus_degree_bridge : ∀ v : Fin 18,
    DegreeCapacity.degree pappusGraph v = (pappusNeighbors v).length := by decide +kernel

private theorem pappus_common_bridge : ∀ a b : Fin 18,
    (Finset.univ.filter (fun v => pappusGraph.Adj a v ∧ pappusGraph.Adj b v)).card =
      ((pappusNeighbors a).filter (fun v => (pappusNeighbors b).contains v)).length := by
  decide +kernel

private theorem pappus_selection_bridge : ∀ v : Fin 18,
    (pappusSet.filter (pappusGraph.Adj v)).card =
      ((pappusNeighbors v).filter (fun w => pappusSelected.contains w)).length := by
  decide +kernel

/-- The exact supplier table gives actual cubic bipartiteness and no four-cycle. -/
theorem pappus_class : pappusGraph.Colorable 2 ∧
    (∀ v, DegreeCapacity.degree pappusGraph v = 3) ∧ NoFourCycle pappusGraph.Adj := by
  refine ⟨?_,?_,?_⟩
  · refine ⟨SimpleGraph.Coloring.mk
      (fun v => (⟨v.val % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2)) ?_⟩
    intro a b hab he
    have h := (pappus_regular_bipartite_certificate.1 a).2.2 b.val hab
    exact h.2 (congrArg Fin.val he).symm
  · intro v
    rw [pappus_degree_bridge]
    exact (pappus_regular_bipartite_certificate.1 v).1
  · intro a b x y hab hxy hax hay hbx hby h1 h2 h3 h4
    have hc := pappus_no_four_cycle_certificate a b hab
    rw [← pappus_common_bridge] at hc
    have hi := Finset.card_le_one.mp hc
    exact hxy (hi x (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h1,h3⟩)
      y (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h2,h4⟩))

/-- The source ten-set is transported to the actual canonical finite selection. -/
theorem pappus_selection : IsKIndependent pappusGraph 2 pappusSet ∧ pappusSet.card = 10 := by
  constructor
  · intro v hv
    have hh := pappus_dissociation_certificate.2.2.2 v (Finset.mem_filter.mp hv).2
    rw [pappus_selection_bridge]
    omega
  · decide +kernel

/-- The canonical maximum is exactly10, without enumerating all graph subsets. -/
theorem beta_pappus : beta pappusGraph 2 = 10 := by
  have hlo : pappusSet.card ≤ beta pappusGraph 2 :=
    Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,pappus_selection.1⟩)
  rw [pappus_selection.2] at hlo
  have hm := beta_le_sf pappusGraph
  have hu := DegreeCapacity.sf_regular_bound pappusGraph 3 (by decide) pappus_class.2.1
  norm_num at hu
  omega

/-- The cubic C4-free half-order identification cannot extend to order18. -/
def claim : Prop := ∀ (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj],
  G.Colorable 2 → (∀ v, DegreeCapacity.degree G v = 3) → NoFourCycle G.Adj →
    2 * beta G 2 ≤ 18

set_option maxRecDepth 8192 in
theorem result : ¬ claim := by
  intro h
  have hh := h pappusGraph pappus_class.1 pappus_class.2.1 pappus_class.2.2
  rw [beta_pappus] at hh
  omega

section RepresentativeConsequences
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem noFour_of_common_cap {W : Type} [Fintype W] [DecidableEq W]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (h : ∀ a b, a ≠ b → (Finset.univ.filter (fun v => F.Adj a v ∧ F.Adj b v)).card ≤ 1) :
    NoFourCycle F.Adj := by
  intro a b x y hab hxy _ _ _ _ hax hay hbx hby
  exact hxy (Finset.card_le_one.mp (h a b hab) x
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hax,hbx⟩) y
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hay,hby⟩))

private def heawoodColor (v : Fin 14) : Bool := decide (v.val < 7)
private theorem heawoodColor_valid : ∀ v w, HeawoodParameters.graph.Adj v w →
    heawoodColor v ≠ heawoodColor w := by decide +kernel
private theorem heawoodColor_sides : ∀ c,
    (Finset.univ.filter (fun v => heawoodColor v = c)).card = 7 := by decide +kernel
private theorem heawood_free : NoFourCycle HeawoodParameters.graph.Adj := by
  apply noFour_of_common_cap
  decide +kernel

/-- In the actual cyclic-label Heawood graph, the coloring/representative
parameters equal seven while the distinct star-forming parameter equals eight. -/
theorem heawood_parameters : beta HeawoodParameters.graph 2 = 7 ∧
    psiSq HeawoodParameters.graph = 7 ∧ Omega HeawoodParameters.graph = 7 ∧
    SF HeawoodParameters.graph 2 = 8 := by
  have hp := threshold_parameters HeawoodParameters.graph heawoodColor heawoodColor_valid
    heawood_free 3 7 (by decide) HeawoodParameters.graph_class.2 heawoodColor_sides (by decide)
  exact ⟨hp.1,hp.2.1,hp.2.2,HeawoodParameters.sf_graph⟩

/-- Binary-label Heawood graph used by the written mixed-support example.
Point and line copies of the same nonzero binary label are distinct. -/
def binaryHeawood : SimpleGraph (Fin 14) where
  Adj v w := (v.val < 7) ≠ (w.val < 7) ∧
    HeawoodCertificates.dot (v.val%7+1) (w.val%7+1) = 0
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩

instance : DecidableRel binaryHeawood.Adj := fun v w => inferInstanceAs (Decidable
  ((v.val < 7) ≠ (w.val < 7) ∧ HeawoodCertificates.dot (v.val%7+1) (w.val%7+1) = 0))

private theorem binaryColor_valid : ∀ v w, binaryHeawood.Adj v w →
    heawoodColor v ≠ heawoodColor w := by decide +kernel
private theorem binary_regular : ∀ v, DegreeCapacity.degree binaryHeawood v = 3 := by
  decide +kernel
private theorem binary_free : NoFourCycle binaryHeawood.Adj := by
  apply noFour_of_common_cap
  decide +kernel

def mixedSingletons : Finset (Fin 14) := {1,2,3,11,12,13}
def mixedMatching : Finset (Fin 14 × Fin 14) := {(0,8)}

/-- The q=2 exception is an actual optimum with three singletons on each
side and one matching edge, in the source's exact binary labeling. -/
theorem mixed_support_optimum : Feasible binaryHeawood mixedSingletons mixedMatching ∧
    mixedSingletons.card + mixedMatching.card = Omega binaryHeawood ∧
    (mixedSingletons.filter (fun v => heawoodColor v = false)).card = 3 ∧
    (mixedSingletons.filter (fun v => heawoodColor v = true)).card = 3 := by
  have hp := threshold_parameters binaryHeawood heawoodColor binaryColor_valid
    binary_free 3 7 (by decide) binary_regular heawoodColor_sides (by decide)
  refine ⟨?_,?_,by decide +kernel,by decide +kernel⟩
  · constructor
    · decide +kernel
    · intro e he f hf hne
      simp [mixedMatching] at he hf
      exact (hne (he.trans hf.symm)).elim
    · decide +kernel
    · decide +kernel
  · rw [hp.2.2]
    decide +kernel

private def pappusColor (v : Fin 18) : Bool := decide (v.val % 2 = 1)
private theorem pappusColor_valid : ∀ v w, pappusGraph.Adj v w → pappusColor v ≠ pappusColor w := by
  decide +kernel
private theorem pappusColor_sides : ∀ c, (Finset.univ.filter (fun v => pappusColor v = c)).card = 9 := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- The Pappus representative upper bound is a general pair-packing consequence,
not an enumeration of representative pairs. -/
theorem omega_pappus : Omega pappusGraph = 10 := by
  classical
  have hu : Omega pappusGraph ≤ 10 := by
    apply omega_upper_of_objective_bound
    intro T M hf
    by_cases he : T.card + M.card ≤ 9
    · omega
    · have hh := positive_excess_budget pappusGraph pappusColor pappusColor_valid
        pappus_class.2.2 3 9 (by decide) pappus_class.2.1 pappusColor_sides T M hf (by omega)
      norm_num at hh
      omega
  have hh := parameter_comparison pappusGraph
  rw [beta_pappus] at hh
  omega

/-- Pappus attains ten in all three distinct parameters. -/
theorem pappus_parameters : beta pappusGraph 2 = 10 ∧
    psiSq pappusGraph = 10 ∧ Omega pappusGraph = 10 := by
  have hh := parameter_comparison pappusGraph
  rw [beta_pappus,omega_pappus] at hh
  exact ⟨beta_pappus,by omega,omega_pappus⟩

/-- Every Pappus optimum has no matching representative, preserving the full
support-rigidity assertion beyond the numerical value ten. -/
theorem pappus_optimal_matching_empty (T : Finset (Fin 18)) (M : Finset (Fin 18 × Fin 18))
    (hf : Feasible pappusGraph T M) (hc : T.card + M.card = 10) : M = ∅ := by
  have hh := positive_excess_budget pappusGraph pappusColor pappusColor_valid
    pappus_class.2.2 3 9 (by decide) pappus_class.2.1 pappusColor_sides T M hf (by omega)
  norm_num at hh
  apply Finset.card_eq_zero.mp
  omega

/-- Every ten-color Pappus coloring has an actual ten-vertex dissociation support
and is injective on that support; this is a statement about every optimum. -/
theorem pappus_coloring_rigidity (c : Fin 18 → Option ℕ)
    (hc : IsSubQuorum pappusGraph c) (hp : (palette c Finset.univ).card = 10) :
    IsKIndependent pappusGraph 2 (coloredSupport c Finset.univ) ∧
    (coloredSupport c Finset.univ).card = 10 ∧
    Set.InjOn c (coloredSupport c Finset.univ) := by
  classical
  obtain ⟨T,M,hf,he,hclasses⟩ := coloring_representatives pappusGraph c hc
  have hm := pappus_optimal_matching_empty T M hf (he.trans hp)
  have hclass := hclasses hm
  have hi : IsKIndependent pappusGraph 2 (coloredSupport c Finset.univ) := by
    intro v hv
    have hvc := (Finset.mem_filter.mp hv).2
    have hsame : ((Finset.univ.filter (pappusGraph.Adj v)).filter
        (fun w => c w = c v)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro w hw he
      exact hclass v w hvc he (Finset.mem_filter.mp hw).2
    have hh := hc v hvc
    have hneigh : @Finset.filter (Fin 18) (pappusGraph.Adj v)
        (fun _ => Classical.propDecidable _) Finset.univ =
        Finset.univ.filter (pappusGraph.Adj v) := by ext w; simp
    have hs : ((Finset.univ.filter (pappusGraph.Adj v)).filter (fun w => c w ≠ none)) =
        (coloredSupport c Finset.univ).filter (pappusGraph.Adj v) := by
      ext w
      simp [coloredSupport,and_comm]
    rw [hneigh,hsame,hs] at hh
    simp only [Finset.card_empty] at hh
    omega
  have hu : (coloredSupport c Finset.univ).card ≤ beta pappusGraph 2 :=
    Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,hi⟩)
  have hl : (palette c Finset.univ).card ≤ (coloredSupport c Finset.univ).card :=
    Finset.card_image_le
  rw [beta_pappus] at hu
  have hcard : (coloredSupport c Finset.univ).card = 10 := by omega
  refine ⟨hi,hcard,?_⟩
  apply Finset.card_image_iff.mp
  exact hp.trans hcard.symm

end RepresentativeConsequences

end D5.S3.Combinatorics.Graph.SubQuorum.C4FreeRepresentatives
