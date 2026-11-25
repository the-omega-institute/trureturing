/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeKernelSupport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeKernelSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Combinatorics.Graph.Hypercube.BinaryKernelMinimum, lake/module/D5.S3.Combinatorics.Graph.Hypercube.BinaryAdjacencyWeight]
   utility: none
   digest: Minimum binary kernel support and weight divisibility in Boolean coordinates. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.BinaryCubeHalfKernel
import D5.S3.Combinatorics.Graph.Hypercube.BinaryAdjacencyWeight
import D5.S3.Combinatorics.Graph.Hypercube.BinaryKernelMinimum

/-! Transport the binary adjacency and weight theorems from symmetric differences
of coordinate sets to the Boolean-coordinate cube used by the Q9 fold. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BinaryCubeKernelSupport

open scoped BigOperators symmDiff
open Finset
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q)
local notation "flip" => BalancedCriticalSpectrum.flip
open D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.BinaryCubeHalfKernel (adjacency)

/-- The support of a binary word on a finite type. -/
def binarySites {α : Type*} [Fintype α] (f : α → ZMod 2) : Finset α :=
  Finset.univ.filter fun x => f x ≠ 0

/-- Adding two binary words loses precisely twice the number of shared
support sites. For opposite cube sections this is the equality test for
whether their sum is as large as the two sections counted together. -/
theorem add_sites_card_add_twice_inter {α : Type*} [Fintype α] [DecidableEq α]
    (f g : α → ZMod 2) :
    (binarySites (f + g)).card + 2 * (binarySites f ∩ binarySites g).card =
      (binarySites f).card + (binarySites g).card := by
  have hone : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  have hd :
      binarySites (f + g) = (binarySites f ∪ binarySites g) \ (binarySites f ∩ binarySites g) := by
    ext x
    simp only [binarySites, Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply,
      Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
    by_cases hf : f x = 0 <;> by_cases hg : g x = 0
    · simp [hf, hg]
    · simp [hf, hg]
    · simp [hf, hg]
    · simp [hone _ hf, hone _ hg, ZModModule.add_self]
  have hi := Finset.card_union_add_card_inter (binarySites f) (binarySites g)
  have hs :=
    Finset.card_sdiff_add_card_eq_card
      (Finset.inter_subset_union (s := binarySites f) (t := binarySites g))
  rw [← hd] at hs
  omega

private def cubeFinsetEquiv (n : ℕ) : Q n ≃ Finset (Fin n) where
  toFun x := univ.filter fun i => x i = true
  invFun s i := decide (i ∈ s)
  left_inv x := by
    funext i
    change decide (i ∈ univ.filter (fun j => x j = true)) = x i
    cases h : x i <;> simp [h]
  right_inv s := by
    ext i
    change i ∈ univ.filter (fun j => decide (j ∈ s) = true) ↔ i ∈ s
    simp

private theorem cubeFinsetEquiv_flip {n : ℕ} (x : Q n) (i : Fin n) :
    cubeFinsetEquiv n (flip x i) = cubeFinsetEquiv n x ∆ {i} := by
  ext j
  change j ∈ univ.filter (fun k => flip x i k = true) ↔
    j ∈ (univ.filter (fun k => x k = true)) ∆ {i}
  by_cases h : j = i
  · subst j
    cases hxi : x i <;> simp [mem_symmDiff, hxi]
  · simp only [mem_filter, mem_univ, true_and]
    simp [mem_symmDiff, BalancedCriticalSpectrum.flip, h]

private theorem adjacency_to_finsets {n : ℕ} (f : Q n → ZMod 2) :
    BinaryKernelCoordinateMoment.adjacency (f ∘ (cubeFinsetEquiv n).symm) =
      adjacency f ∘ (cubeFinsetEquiv n).symm := by
  funext s
  obtain ⟨x, rfl⟩ := (cubeFinsetEquiv n).surjective s
  simp only [BinaryKernelCoordinateMoment.adjacency, adjacency, Function.comp_apply,
    ← cubeFinsetEquiv_flip, Equiv.symm_apply_apply]

private theorem weight_to_finsets {n : ℕ} (f : Q n → ZMod 2) :
    BinaryAdjacencyWeight.weight (f ∘ (cubeFinsetEquiv n).symm) = (binarySites f).card := by
  unfold BinaryAdjacencyWeight.weight
  calc
    _ = ∑ x : Q n, (f x).val :=
      Fintype.sum_equiv (cubeFinsetEquiv n).symm _ _ (fun _ => rfl)
    _ = ∑ x : Q n, if f x ≠ 0 then (1 : ℕ) else 0 := by
      have hval : ∀ a : ZMod 2, a.val = if a ≠ 0 then 1 else 0 := by decide
      exact sum_congr rfl fun x _ => hval (f x)
    _ = _ := by rw [← sum_filter, ← card_eq_sum_ones]; rfl

private theorem even_rows_of_kernel {n : ℕ} {f : Q n → ZMod 2}
    (hf : adjacency f = 0) (x : Finset (Fin n)) :
    Even (BinaryKernelCrossing.neighborDirections
      ((binarySites f).map (cubeFinsetEquiv n).toEmbedding) x).card := by
  apply ZMod.natCast_eq_zero_iff_even.mp
  let e := cubeFinsetEquiv n
  let g := f ∘ e.symm
  have hg : BinaryKernelCoordinateMoment.adjacency g = 0 := by
    change BinaryKernelCoordinateMoment.adjacency (f ∘ e.symm) = 0
    rw [adjacency_to_finsets, hf]
    rfl
  have hsum : (∑ i : Fin n, g (x ∆ {i})) = 0 := congrFun hg x
  have hbinary : ∀ z : ZMod 2, (if z ≠ 0 then 1 else 0) = z := by decide
  unfold BinaryKernelCrossing.neighborDirections
  calc
    _ = ∑ i ∈ univ.filter (fun i : Fin n => x ∆ {i} ∈
        (binarySites f).map e.toEmbedding), (1 : ZMod 2) := by simp [e]
    _ = ∑ i : Fin n, (if g (x ∆ {i}) ≠ 0 then 1 else 0) := by
      rw [sum_filter]
      apply sum_congr rfl
      intro i _
      simp [mem_map_equiv, binarySites, g, e]
    _ = _ := by simpa only [hbinary] using hsum

/-- Equality in the binary kernel minimum transported to Boolean coordinates.
In even dimensions at least six, a nonzero kernel word of weight at most
the dimension is a single flip neighbourhood. -/
theorem minimum_kernel_support {n : ℕ} (hn : 6 ≤ n) (he : Even n)
    (f : Q n → ZMod 2) (hf : adjacency f = 0) (hne : f ≠ 0)
    (hw : (binarySites f).card ≤ n) :
    ∃ p : Q n, (binarySites f).card = n ∧ binarySites f = univ.image (flip p) := by
  classical
  let e := cubeFinsetEquiv n
  let S := (binarySites f).map e.toEmbedding
  have hpos : (binarySites f).Nonempty := by
    by_contra h
    apply hne
    funext x
    by_contra hx
    exact h ⟨x, by simpa [binarySites] using hx⟩
  have hSpos : S.Nonempty := hpos.map
  have hrows : ∀ x, Even (BinaryKernelCrossing.neighborDirections S x).card :=
    even_rows_of_kernel hf
  have hcardS : S.card = (binarySites f).card := card_map _
  have hsmin := BinaryKernelCrossing.card_ge_dimension S hSpos hrows
  have hweight : (binarySites f).card = n := by omega
  obtain ⟨s, hs⟩ := (BinaryKernelMinimum.minimum_support_iff hn he S).mp
    ⟨hcardS.trans hweight, hrows⟩
  refine ⟨e.symm s, hweight, ?_⟩
  apply Finset.map_injective e.toEmbedding
  change S = (univ.image (flip (e.symm s))).map e.toEmbedding
  rw [hs, map_eq_image, image_image]
  congr 1
  funext i
  change s ∆ {i} = e (flip (e.symm s) i)
  rw [cubeFinsetEquiv_flip, Equiv.apply_symm_apply]

/-- Every binary adjacency kernel word on a positive 4m-dimensional cube
has support size divisible by four. -/
theorem four_dvd_binarySites_card {m : ℕ} (hm : 0 < m) {f : Q (4 * m) → ZMod 2}
    (hf : adjacency f = 0) : 4 ∣ (binarySites f).card := by
  have hkernel : BinaryKernelCoordinateMoment.adjacency
      (f ∘ (cubeFinsetEquiv (4 * m)).symm) = 0 := by
    rw [adjacency_to_finsets, hf]
    rfl
  rw [← weight_to_finsets f]
  exact BinaryAdjacencyWeight.four_dvd_weight_of_adjacency_eq_zero ⟨m, rfl⟩
    ⟨0, by omega⟩ _ hkernel

#print axioms four_dvd_binarySites_card
#print axioms minimum_kernel_support

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BinaryCubeKernelSupport
