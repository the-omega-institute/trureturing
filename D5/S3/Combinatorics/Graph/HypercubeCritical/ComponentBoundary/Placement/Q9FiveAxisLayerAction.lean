/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisLayerAction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisLayerAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Exchanging coordinates 3 and 4 and exchanging the roots realize the two pattern permutations by actual cube isometries. Both preserve the even slice and the mask family. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisOrbitGeometry
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9RootStabilizer

/-! The generators that exchange representatives are realized on the actual supports. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisLayerAction

open Finset
open BalancedCriticalSpectrum (Q)
open D5.S3.Combinatorics.Graph.HypercubeCritical (cubeBitVec)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization
  (normalize origin)
open Q9FiveAxisOrbitCover (Pattern Word orbit evenWords swapAxes swapRoots)
open Q9RootStabilizer (cubeBitVec_swap34 cubeBitVec_translate03)
open private swap34 swapWord from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9RootStabilizer
open Q9TightDistanceTwoCNF (support)
open Q9IsotropicHuang (parity)
open Q9FiveAxisOrbitGeometry (family)


def LayerMatches (C D : Finset (Q 9)) (p : Pattern) : Prop :=
  ∀ (s : Bool) (w : Word), w ∈ evenWords →
    (cubeBitVec 9 w ∈ support C D s ↔ w ∈ p.on s)

private def swapFrame : Q 9 ≃ Q 9 := normalize swap34 origin

private def rootFrame : Q 9 ≃ Q 9 := normalize (Equiv.refl _) (cubeBitVec 9 (3 : Word))

private theorem swapWord_mem {w : Word} (h : w ∈ evenWords) : swapWord w ∈ evenWords := by
  revert w
  decide +kernel

private theorem rootWord_mem {w : Word} (h : w ∈ evenWords) : w ^^^ 3 ∈ evenWords := by
  revert w
  decide +kernel

private theorem swapWord_involutive : Function.Involutive swapWord := by
  intro w
  revert w
  decide +kernel

private theorem rootWord_involutive (w : Word) : (w ^^^ 3) ^^^ 3 = w := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

private theorem image_mem_involutive {f : Word → Word} (hf : Function.Involutive f)
    {X : Finset Word} {w : Word} : w ∈ X.image f ↔ f w ∈ X := by
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := mem_image.mp h
    rw [hf x]
    exact hx
  · intro h
    exact mem_image.mpr ⟨f w, h, hf w⟩

private theorem cube_swapFrame (w : Word) :
    swapFrame.symm (cubeBitVec 9 w) = cubeBitVec 9 (swapWord w) := by
  apply swapFrame.injective
  rw [Equiv.apply_symm_apply]
  change _ = normalize swap34 origin (cubeBitVec 9 (swapWord w))
  rw [cubeBitVec_swap34, swapWord_involutive]

private theorem cube_rootFrame (w : Word) :
    rootFrame.symm (cubeBitVec 9 w) = cubeBitVec 9 (w ^^^ 3) := by
  apply rootFrame.injective
  rw [Equiv.apply_symm_apply]
  change _ = normalize (Equiv.refl _) (cubeBitVec 9 (3 : Word)) (cubeBitVec 9 (w ^^^ 3))
  rw [cubeBitVec_translate03, rootWord_involutive]

private theorem layer_swap {C D : Finset (Q 9)} {p : Pattern}
    (h : LayerMatches C D p) :
    LayerMatches (C.map swapFrame.toEmbedding) (D.map swapFrame.toEmbedding) (swapAxes p) := by
  intro s w hw
  cases s
  · change cubeBitVec 9 w ∈ C.map swapFrame.toEmbedding ↔ w ∈ p.1.image swapWord
    rw [mem_map_equiv, cube_swapFrame, image_mem_involutive swapWord_involutive]
    exact h false (swapWord w) (swapWord_mem hw)
  · change cubeBitVec 9 w ∈ D.map swapFrame.toEmbedding ↔ w ∈ p.2.image swapWord
    rw [mem_map_equiv, cube_swapFrame, image_mem_involutive swapWord_involutive]
    exact h true (swapWord w) (swapWord_mem hw)

private theorem layer_root {C D : Finset (Q 9)} {p : Pattern}
    (h : LayerMatches C D p) :
    LayerMatches (D.map rootFrame.toEmbedding) (C.map rootFrame.toEmbedding) (swapRoots p) := by
  intro s w hw
  have hInv : Function.Involutive (fun x : Word => x ^^^ (3 : Word)) := rootWord_involutive
  cases s
  · change cubeBitVec 9 w ∈ D.map rootFrame.toEmbedding ↔ w ∈ p.2.image (· ^^^ 3)
    rw [mem_map_equiv, cube_rootFrame, image_mem_involutive hInv]
    exact h true (w ^^^ 3) (rootWord_mem hw)
  · change cubeBitVec 9 w ∈ C.map rootFrame.toEmbedding ↔ w ∈ p.1.image (· ^^^ 3)
    rw [mem_map_equiv, cube_rootFrame, image_mem_involutive hInv]
    exact h false (w ^^^ 3) (rootWord_mem hw)

private theorem image_twice {f : Word → Word} (hf : Function.Involutive f) (X : Finset Word) :
    (X.image f).image f = X := by
  ext x
  rw [image_mem_involutive hf, image_mem_involutive hf, hf x]

private theorem swapAxes_involutive (p : Pattern) : swapAxes (swapAxes p) = p := by
  rcases p with ⟨L, R⟩
  change ((L.image swapWord).image swapWord, (R.image swapWord).image swapWord) = (L, R)
  rw [image_twice swapWord_involutive, image_twice swapWord_involutive]

private theorem swapRoots_involutive (p : Pattern) : swapRoots (swapRoots p) = p := by
  rcases p with ⟨L, R⟩
  let f : Word → Word := (· ^^^ 3)
  change ((L.image f).image f, (R.image f).image f) = (L, R)
  have hInv : Function.Involutive f := rootWord_involutive
  rw [image_twice hInv, image_twice hInv]

private theorem swap_preserves_family :
    family.map (Finset.mapEmbedding swap34.symm.toEmbedding).toEmbedding = family := by
  decide +kernel

/-- Every orbit representative is realized by a coordinate normalization of
the given supports, with a possible exchange of the two shores. -/
theorem reaches_representative {C D : Finset (Q 9)} {p r : Pattern}
    (hp : p ∈ orbit r) (h : LayerMatches C D p) :
    ∃ (σ : Equiv.Perm (Fin 9)) (o : Q 9) (b : Bool),
      parity o = false ∧
      family.map (Finset.mapEmbedding σ.symm.toEmbedding).toEmbedding = family ∧
      LayerMatches ((support C D b).map (normalize σ o).toEmbedding)
        ((support C D (!b)).map (normalize σ o).toEmbedding) r := by
  simp only [orbit, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · refine ⟨Equiv.refl _, origin, false, by decide +kernel, by decide +kernel, ?_⟩
    have he : normalize (Equiv.refl _) origin = Equiv.refl _ := by
      ext x i
      change (x i != false) = x i
      simp
    simpa only [he, support, Bool.not_false, Bool.false_eq_true, ite_false, ite_true,
      Equiv.refl_toEmbedding, Finset.map_refl] using h
  · refine ⟨swap34, origin, false, by decide +kernel, swap_preserves_family, ?_⟩
    change LayerMatches (C.map swapFrame.toEmbedding) (D.map swapFrame.toEmbedding) r
    simpa only [swapAxes_involutive] using layer_swap h
  · refine ⟨Equiv.refl _, cubeBitVec 9 (3 : Word), true, by decide +kernel, by decide +kernel, ?_⟩
    change LayerMatches (D.map rootFrame.toEmbedding) (C.map rootFrame.toEmbedding) r
    simpa only [swapRoots_involutive] using layer_root h
  · have ht := layer_root (layer_swap h)
    rw [swapAxes_involutive, swapRoots_involutive] at ht
    have he : swapFrame.trans rootFrame =
        normalize ((Equiv.refl (Fin 9)).trans swap34) (swapFrame.symm (cubeBitVec 9 (3 : Word))) :=
      Q9RootStabilizer.normalize_comp swap34 (Equiv.refl _) origin (cubeBitVec 9 (3 : Word))
    refine ⟨(Equiv.refl (Fin 9)).trans swap34, swapFrame.symm (cubeBitVec 9 (3 : Word)),
      true, by decide +kernel, by decide +kernel, ?_⟩
    simpa only [support, Bool.not_true, Bool.false_eq_true, ite_false, ite_true,
      Finset.map_map, ← Equiv.trans_toEmbedding, he] using ht

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisLayerAction
