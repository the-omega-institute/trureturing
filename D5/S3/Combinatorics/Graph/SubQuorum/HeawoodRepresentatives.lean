/- GID: D5/S3/Combinatorics/Graph/SubQuorum/HeawoodRepresentatives
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/SubQuorum/HeawoodRepresentatives
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: kind=certified-instance
   digest: Cyclic and binary Heawood representative certificates. -/

import D5.S3.Combinatorics.Graph.SubQuorum.C4RepresentativeBounds
import D5.S3.Combinatorics.Graph.StarForming.HeawoodParameters
import D5.S3.Combinatorics.Graph.StarForming.HeawoodIncidence

/-! Finite Heawood certificates from the exact received Sahbi source revision
48728b42d39ab3de5de251c61da5a404ec418a69, Apache-2.0.
These fixed positive certificates have no qualifying refutation basis under
CLAUDE.md §3.3. Their utility header records the classification and has no basis. -/

namespace D5.S3.Combinatorics.Graph.SubQuorum.C4FreeRepresentatives
open StarFormingDissociationRefutation
open StarForming
open scoped BigOperators
open DoubleStarGrafting

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
  have regular : ∀ v, HeawoodParameters.graph.degree v = 3 := by
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter] using
      HeawoodParameters.graph_class.2
  have hp := threshold_parameters HeawoodParameters.graph heawoodColor heawoodColor_valid
    heawood_free 3 7 (by decide) regular heawoodColor_sides (by decide)
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
private theorem binary_regular : ∀ v, binaryHeawood.degree v = 3 := by
  simp only [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
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

end D5.S3.Combinatorics.Graph.SubQuorum.C4FreeRepresentatives
