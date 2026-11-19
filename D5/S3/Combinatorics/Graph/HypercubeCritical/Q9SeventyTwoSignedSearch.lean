import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoEmbeddingSearch
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixSignedModelProbe
import Batteries.Tactic.OpenPrivate

/-! The actual normalized embedding carries integer switching values. Their
restriction to the chosen half determines all values across the cut. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoSignedSearch

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q IsBalanced)
open BalancedCubeLowerBound (coordinateSlice)
open Q9EightCubicGraphCertificate (modelAdj)
open private cube_action_regular_balanced from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixNormalizeProbe

attribute [local instance] Classical.propDecidable
local notation "flip" => BalancedCriticalSpectrum.flip

/-- A geometric candidate obtained from an actual support admits signed
integer values for its highs and selected middles, together with all of
the ambient row constraints. -/
theorem exists_signed_candidate {C : Finset (Q 9)} (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card = 20) :
    ∃ (g : Q 9 ≃ Q 9) (σ : Fin 9 ≃ Fin 9) (wagner : Bool) (pattern : Fin 5)
      (p : Fin 8 ↪ Q 9) (z : Q 9 → ℤ),
      (∀ x i, g (flip x i) = flip (g x) (σ i)) ∧
      (∀ x, g x 0 = false ↔ x 0 = b) ∧
      (fun i => (cubeBitVec 9).symm (p i)) ∈ Q9SeventyTwoEmbeddingSearch.candidates wagner pattern ∧
      (∀ k, p k ∈ (coordinateSlice C b).image g) ∧
      (∀ i j, modelAdj wagner i j = true →
        ∃ m ∈ (coordinateSlice C b).image g,
          ∀ k, (hypercube 9).Adj m (p k) ↔ k = i ∨ k = j) ∧
      (∀ x ∈ C.image g, z x = 1 ∨ z x = -1) ∧ (∀ x ∉ C.image g, z x = 0) ∧
      (∀ x ∈ C.image g, ∀ i : Fin 9, flip x i ∈ C.image g →
        truePrefixSign x i = z x * z (flip x i)) ∧
      ∀ y, z (flip y 0) =
        3 * z y - ∑ i ∈ Finset.univ.erase (0 : Fin 9), truePrefixSign y i * z (flip y i) := by
  obtain ⟨g, σ, wagner, pattern, p, hg, hcut, hhigh, hmem, hmid⟩ :=
    Q9SeventyTwoEmbeddingSearch.exists_member hC hr hb b hs
  obtain ⟨hrg, hbg⟩ := cube_action_regular_balanced g σ hg hr hb
  obtain ⟨z, hunit, hzero, hsign, hrow⟩ := q9_integral_true_prefix_switching hrg hbg
  refine ⟨g, σ, wagner, pattern, p, z, hg, hcut, hmem, hhigh, ?_, hunit, hzero, hsign, ?_⟩
  · intro i j hij
    obtain ⟨m, hm, _, hAdj⟩ := hmid i j hij
    exact ⟨m, hm, hAdj⟩
  · intro y
    have h := hrow y
    have hz : truePrefixSign y (0 : Fin 9) = 1 := by
      simp [truePrefixSign]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin 9)), hz, one_mul] at h
    rw [← h, add_sub_cancel_left]

#print axioms exists_signed_candidate

end D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoSignedSearch
