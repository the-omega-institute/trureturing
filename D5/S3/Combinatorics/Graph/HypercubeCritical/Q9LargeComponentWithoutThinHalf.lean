import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ThinPairedCertificate
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9TwoGrayComponents

/-! The surviving large component in a hypothetical 258-vertex candidate
has no twenty-vertex coordinate half when its order is 72. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open BalancedCubeLowerBound (coordinateSlice)
open TwoBalancedComponents (componentFinset)
open private componentFinset_subset componentFinset_neighbor_closed from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwoBalancedComponents
open private selected_neighbor_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenSaturation
open private reindex reindex_adj reindex_regular reindex_balanced reindex_slice from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction
attribute [local instance] Classical.propDecidable

private theorem no_twenty_half {U C : Finset (Q 9)} (hU : U.card = 258) (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (hsub : C ⊆ U) (hclosed : ∀ x ∈ C, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ C)
    (hdeg : ∀ x ∈ U, (U.filter ((hypercube 9).Adj x)).card ≤ 3)
    (j : Fin 9) (b : Bool) (hs : (C.filter (fun x => x j = b)).card = 20) : False := by
  classical
  let p := Equiv.swap j (0 : Fin 9)
  let g := reindex p
  have hU' : (U.image g).card = 258 := by rw [Finset.card_image_of_injective _ g.injective, hU]
  have hC' : (C.image g).card = 72 := by rw [Finset.card_image_of_injective _ g.injective, hC]
  have hs' : (coordinateSlice (C.image g) b).card = 20 := by
    change (coordinateSlice (C.image (reindex (Equiv.swap j 0))) b).card = 20
    rw [reindex_slice, Finset.card_image_of_injective _ g.injective, hs]
  apply Q9ThinPairedCertificate.no_thin_component_of_extension hU' hC'
    (reindex_regular hr p) (reindex_balanced hb p) b hs' (Finset.image_subset_image hsub)
  · intro x hx y hy hadj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image_of_mem g (hclosed a ha c hc ((reindex_adj p a c).mp hadj))
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    have hf : (U.image g).filter ((hypercube 9).Adj (g a)) =
        (U.filter ((hypercube 9).Adj a)).image g := by
      rw [Finset.filter_image]
      congr 1
      ext y
      simp only [Finset.mem_filter, g, reindex_adj]
    rw [hf, Finset.card_image_of_injective _ g.injective]
    exact hdeg a ha

/-- A 258-vertex induced subcubic set has a Huang-balanced cubic component
of order at least 72. If that component has order 72, none of its coordinate
halves contains exactly twenty vertices. -/
theorem exists_large_component_without_thin_half (U : Finset (Q 9)) (hU : U.card = 258)
    (hdeg : ∀ v : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree v ≤ 3) :
    ∃ K : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent,
      let C := componentFinset U K
      ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3 ∧
        IsBalanced C ∧ 72 ≤ C.card ∧
          (C.card = 72 → ∀ (j : Fin 9) (b : Bool), (C.filter (fun x => x j = b)).card ≠ 20) := by
  classical
  obtain ⟨K, hr, hb, hc⟩ := Q9TwoGrayComponents.exists_large_balanced_component U hU hdeg
  refine ⟨K, hr, hb, hc, fun heq j b hhalf => ?_⟩
  have hdegree (x : Q 9) (hx : x ∈ U) : (U.filter ((hypercube 9).Adj x)).card ≤ 3 := by
    have he : U.filter ((hypercube 9).Adj x) = (hypercube 9).neighborFinset x ∩ U := by
      ext y
      simp [SimpleGraph.mem_neighborFinset, and_comm]
    rw [he, selected_neighbor_card hx]
    exact hdeg ⟨x, hx⟩
  exact no_twenty_half hU heq hr hb (componentFinset_subset U K)
    (componentFinset_neighbor_closed U K) hdegree j b hhalf

#print axioms exists_large_component_without_thin_half

end D5.S3.Combinatorics.Graph.HypercubeCritical
