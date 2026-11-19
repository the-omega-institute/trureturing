import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ThinOrbitCertificate

/-! Any 258-vertex extension containing a thin 72-vertex component must use the
compressed cube with three disjoint root-axis pairs. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ThinExtensionReduction

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced flip_adj)
open BalancedCubeLowerBound (coordinateSlice)
open Q9SeventyTwoSignedCompletion (exists_surviving_signs signMasks signsFromMask support)
open Q9SeventyTwoEmbeddingSearch (Placement candidates)
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private exists_mask from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoSignedCompletion
open private verified from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ThinEdgeCertificates

attribute [local instance] Classical.propDecidable
local notation "flip" => BalancedCriticalSpectrum.flip

private theorem image_adj_iff (g : Q 9 ≃ Q 9) (σ : Fin 9 ≃ Fin 9)
    (hg : ∀ x i, g (flip x i) = flip (g x) (σ i)) (x y : Q 9) :
    (hypercube 9).Adj (g x) (g y) ↔ (hypercube 9).Adj x y := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := adjacent_exists_flip h
    have hy : g (flip x (σ.symm i)) = g y := by
      rw [hg, σ.apply_symm_apply, hi]
    exact (g.injective hy) ▸ flip_adj x (σ.symm i)
  · intro h
    obtain ⟨i, hi⟩ := adjacent_exists_flip h
    rw [hi, hg]
    exact flip_adj _ _

private theorem card_le_of_map_representative (U C : Finset (Q 9)) (k : Fin 7)
    (e : Q 9 ≃ BitVec 9)
    (he : ∀ x y, Q9GrayCrossedPlacement.cube.Adj (e x) (e y) ↔ (hypercube 9).Adj x y)
    (hC : C.card = 72) (hrep : Q9ThinEdgeCertificates.support k ⊆ C.map e.toEmbedding)
    (hsub : C ⊆ U) (hclosed : ∀ x ∈ C, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ C)
    (hdeg : ∀ x ∈ U, (U.filter ((hypercube 9).Adj x)).card ≤ 3) : U.card ≤ 257 := by
  have hmodel := Finset.eq_of_subset_of_card_le hrep (by
    rw [Finset.card_map, hC, (verified k).1])
  have h := Q9ThinEdgeCertificates.card_le_of_representative k (U.map e.toEmbedding)
    (hmodel ▸ Finset.map_subset_map.mpr hsub) (by
      intro a ha b hb hab
      rw [hmodel] at ha ⊢
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hb
      exact Finset.mem_map.mpr ⟨y, hclosed x hx y hy ((he x y).mp hab), rfl⟩) (by
      intro a ha
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ha
      rw [Finset.filter_map, Finset.card_map]
      have hp : U.filter (Q9GrayCrossedPlacement.cube.Adj (e.toEmbedding x) ∘ e.toEmbedding) =
          U.filter ((hypercube 9).Adj x) := by
        ext y
        simp only [Finset.mem_filter, Function.comp_apply, Equiv.toEmbedding_apply, he]
      rw [hp]
      exact hdeg x hx)
  simpa only [Finset.card_map] using h

/-- A thin 72-vertex closed component in a 258-vertex subcubic set must
normalize to the cube root pattern with three disjoint axis pairs. -/
theorem exists_paired_cube_of_extension {U C : Finset (Q 9)} (hU : U.card = 258)
    (hC : C.card = 72) (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card = 20)
    (hsub : C ⊆ U) (hclosed : ∀ x ∈ C, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ C)
    (hdeg : ∀ x ∈ U, (U.filter ((hypercube 9).Adj x)).card ≤ 3) :
    ∃ (g : Q 9 ≃ Q 9) (σ : Fin 9 ≃ Fin 9) (highs : Placement) (signs : Fin 128),
      (∀ x i, g (flip x i) = flip (g x) (σ i)) ∧ highs ∈ candidates false 4 ∧
      signs ∈ signMasks false (cubeBitVec 9 ∘ highs) ∧
      C.image g = support false (cubeBitVec 9 ∘ highs) (signsFromMask signs) := by
  classical
  obtain ⟨g, σ, wagner, pattern, p, bits, hg, hh, hroot, hsigns, hzero, hCeq⟩ :=
    exists_surviving_signs hC hr hb b hs
  let highs : Placement := fun i => (cubeBitVec 9).symm (p i)
  have hp : cubeBitVec 9 ∘ highs = p := funext fun i => (cubeBitVec 9).apply_symm_apply (p i)
  obtain ⟨signs, rfl⟩ := exists_mask bits hroot
  rw [← hp] at hsigns hCeq
  have hmask := (Q9SeventyTwoSignedCompletion.mem_signMasks wagner _ signs).mpr hsigns
  by_cases hpaired : wagner = false ∧ pattern = 4
  · obtain ⟨rfl, rfl⟩ := hpaired
    exact ⟨g, σ, highs, signs, hg, hh, hmask, hCeq⟩
  · have hsmall (hw : wagner = false) : pattern ≠ 0 ∧ pattern ≠ 4 :=
      ⟨hzero hw, fun h4 => hpaired ⟨hw, h4⟩⟩
    obtain ⟨k, e, he, hrep⟩ := Q9ThinOrbitCertificate.smaller_pattern_representative hsmall hh hmask
    have hm : Q9ThinEdgeCertificates.support k ⊆ C.map (g.trans e).toEmbedding := by
      rw [← hCeq] at hrep
      change _ ⊆ (C.image g.toEmbedding).map e.toEmbedding at hrep
      rw [← Finset.map_eq_image g.toEmbedding C, Finset.map_map] at hrep
      exact hrep
    have h := card_le_of_map_representative U C k (g.trans e)
      (fun x y => (he (g x) (g y)).trans (image_adj_iff g σ hg x y)) hC hm hsub hclosed hdeg
    omega

#print axioms exists_paired_cube_of_extension

end D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ThinExtensionReduction
