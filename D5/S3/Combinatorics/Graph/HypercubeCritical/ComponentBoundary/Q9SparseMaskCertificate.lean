/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseMaskCertificate
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseMaskCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.BitVec]
   utility: none
   digest: A bit-vector contact count certifies the absence of a universally sharp boundary. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SparseOccupiedGram
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeBitMoves

/-! The sparse Gram obstruction can be checked by finite local counts on
bit-vector supports. Each check scans only the directions of the mask. -/

set_option autoImplicit false
noncomputable section
open scoped Matrix

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SparseMaskCertificate

open Finset
open BalancedCriticalSpectrum (Q flip flip_flip IsSwitching)
open CoordinateHalves.CubeBitMoves (toggle)
open CoordinateHalves.Q9DominantAxisBoundary (PairedRows boundary)
open Q9PositivePairedKernel (pairedVertex)
open Q9SparseOccupiedGram (maskContact not_universal_boundary_of_sparse_mask)
open private vertex_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9PositivePairedKernel

private abbrev Word := BitVec 9
private def words : List Word := (List.finRange 512).map BitVec.ofFin

private theorem mem_words (v : Word) : v ∈ words :=
  List.mem_map.mpr ⟨v.toFin, List.mem_finRange _, rfl⟩

private def inSupport (m : ℕ) (v : Word) : Bool := m.testBit v.toNat

/-- Interpret a 512-bit integer characteristic function as a cube support. -/
def support (m : ℕ) : Finset (Q 9) :=
  (words.toFinset.filter fun v => inSupport m v = true).map (cubeBitVec 9).toEmbedding

private theorem support_mem_iff (m : ℕ) (v : Word) :
    cubeBitVec 9 v ∈ support m ↔ inSupport m v = true := by
  constructor
  · intro h
    obtain ⟨u, hu, he⟩ := mem_map.mp h
    have huv : u = v := (cubeBitVec 9).injective he
    subst u
    exact (mem_filter.mp hu).2
  · intro h
    exact mem_map.mpr ⟨v, mem_filter.mpr ⟨List.mem_toFinset.mpr (mem_words v), h⟩, rfl⟩

private theorem toggle_vertex (v : Word) (a : Fin 9) :
    cubeBitVec 9 (toggle v a) = flip (cubeBitVec 9 v) a := by
  rw [toggle, cubeBitVec_xor_single]
  rfl

private def occupiedWord (m : ℕ) (i : Fin 9) (v : Word) : Bool :=
  inSupport m v || inSupport m (toggle v i)

private def pairedWord (m : ℕ) (i : Fin 9) (v : Word) : Bool :=
  inSupport m v && inSupport m (toggle v i)

private theorem occupied_iff (m : ℕ) (i : Fin 9) (v : Word) :
    occupiedWord m i v = true ↔
      cubeBitVec 9 v ∈ support m ∨ flip (cubeBitVec 9 v) i ∈ support m := by
  rw [← toggle_vertex, support_mem_iff, support_mem_iff]
  simp [occupiedWord]

private theorem paired_iff (m : ℕ) (i : Fin 9) (v : Word) :
    pairedWord m i v = true ↔
      cubeBitVec 9 v ∈ support m ∧ flip (cubeBitVec 9 v) i ∈ support m := by
  rw [← toggle_vertex, support_mem_iff, support_mem_iff]
  simp [pairedWord]

private def pairedDirs (m : ℕ) (i : Fin 9) (T : Finset (Fin 9)) (v : Word) :
    Finset (Fin 9) := T.filter fun a => pairedWord m i (toggle v a) = true

private def occupiedDirs (m : ℕ) (i : Fin 9) (T : Finset (Fin 9)) (v : Word) :
    Finset (Fin 9) := T.filter fun a => occupiedWord m i (toggle v a) = true

private def checkWord (m : ℕ) (i : Fin 9) (T : Finset (Fin 9)) (v : Word) : Bool :=
  (if occupiedWord m i v then decide ((pairedDirs m i T v).card ≤ 1) else true) &&
  (if pairedWord m i v then decide ((occupiedDirs m i T v).card < T.card) else true)

/-- Finite test of the sparse occupied row and strict column contact bounds. -/
def sparseMaskCheck (m : ℕ) (i : Fin 9) (T : Finset (Fin 9)) : Bool :=
  decide (i ∉ T) && words.all (checkWord m i T)

private theorem row_checked {m : ℕ} {i : Fin 9} {T : Finset (Fin 9)}
    (h : sparseMaskCheck m i T = true) (v : Word) (hv : occupiedWord m i v = true) :
    (pairedDirs m i T v).card ≤ 1 := by
  have hAll := (Bool.and_eq_true_iff.mp h).2
  have ht := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hAll v (mem_words v))).1
  simpa [checkWord, hv] using ht

private theorem col_checked {m : ℕ} {i : Fin 9} {T : Finset (Fin 9)}
    (h : sparseMaskCheck m i T = true) (v : Word) (hv : pairedWord m i v = true) :
    (occupiedDirs m i T v).card < T.card := by
  have hAll := (Bool.and_eq_true_iff.mp h).2
  have ht := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hAll v (mem_words v))).2
  simpa [checkWord, hv] using ht

/-- A successful contact count excludes universal weighted boundary kernels
for the encoded support, for every switching and retained parity. -/
theorem not_universal_of_sparseMaskCheck {m : ℕ} {i : Fin 9} {T : Finset (Fin 9)}
    (h : sparseMaskCheck m i T = true) {σ : Q 9 → ℝ} (hs : IsSwitching (support m) σ)
    (b : Bool) : ¬ (∀ w : Fin 9 → ℝ, ∃ f ≠ 0, boundary (support m) b w *ᵥ f = 0) := by
  classical
  have hi : i ∉ T := of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
  apply not_universal_boundary_of_sparse_mask (i := i) hs T hi
  · intro r x y hx hy
    obtain ⟨hr, a, ha, hax⟩ := hx
    obtain ⟨_, d, hd, hdy⟩ := hy
    let v := (cubeBitVec 9).symm r
    have hv : cubeBitVec 9 v = r := (cubeBitVec 9).apply_symm_apply r
    have hr' : occupiedWord m i v = true := (occupied_iff m i v).2 (by rw [hv]; exact hr)
    have hp (u : PairedRows (support m) b i) (j : Fin 9) (hj : j ∈ T)
        (he : flip r j = pairedVertex u) : j ∈ pairedDirs m i T v := by
      apply mem_filter.mpr
      refine ⟨hj, (paired_iff m i _).2 ?_⟩
      rw [toggle_vertex, hv, he]
      exact ⟨u.1.1.property, u.property⟩
    have had := (Finset.card_le_one.mp (row_checked h v hr')) a (hp x a ha hax) d (hp y d hd hdy)
    apply vertex_injective
    rw [← hax, ← hdy, had]
  · intro x
    let v := (cubeBitVec 9).symm (pairedVertex x)
    have hv : cubeBitVec 9 v = pairedVertex x := (cubeBitVec 9).apply_symm_apply _
    have hp : pairedWord m i v = true := (paired_iff m i v).2 (by
      rw [hv]
      exact ⟨x.1.1.property, x.property⟩)
    let D := occupiedDirs m i T v
    have hsub : (univ.filter fun r => maskContact (support m) b i T r x) ⊆
        D.image (flip (pairedVertex x)) := by
      intro r hr
      obtain ⟨ho, a, ha, he⟩ := (mem_filter.mp hr).2
      have hflip : flip (pairedVertex x) a = r := by rw [← he, BalancedCriticalSpectrum.flip_flip]
      refine mem_image.mpr ⟨a, mem_filter.mpr ⟨ha, (occupied_iff m i _).2 ?_⟩, hflip⟩
      rw [toggle_vertex, hv, hflip]
      exact ho
    exact (card_le_card hsub).trans_lt (card_image_le.trans_lt (col_checked h v hp))

#print axioms not_universal_of_sparseMaskCheck

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SparseMaskCertificate
