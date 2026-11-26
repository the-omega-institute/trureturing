/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33NormalizedRectangle
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33NormalizedRectangle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Translating the missing labels fixes both rectangles and their contact axes. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9K33AlignedLayer
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoNormalized

/-! Translate the missing row and column to zero in a contacting rectangle. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9K33NormalizedRectangle

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open D5.S3.Combinatorics.Graph.HypercubeCritical (cubeBitVec)
open BalancedCriticalSpectrum (Q IsBalanced flip)
open Q9IsotropicHuang (parity)
open Q9WeightedSaturation (defect signedBiadjacency)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9SquareMaskGraph (activeAxes)
open Q9K33AlignedLayer (nine_masks_on_six_axes_force_contact_rectangles)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization (normalize)
open Q9TightDistanceTwoNormalized (normalize_differingAxes parity_normalize)
open private normalize_hammingDist from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactNormalized
open private differingAxes differingAxes_foldl_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private orientedVertex orientedRow orientedCol row_col_ne blockParity anti leftLayer alignedLayer
  row_parity col_parity flip_row flip_col from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9K33AlignedLayer

private def shuffle : Equiv.Perm (Fin 9) where
  toFun := ![0, 3, 1, 4, 2, 5, 6, 7, 8]
  invFun := ![0, 2, 4, 1, 3, 5, 6, 7, 8]
  left_inv := by decide
  right_inv := by decide

private def blockDiff (u v : Q 3) : Q 3 := fun i => u i != v i

private theorem blockDiff_cancel :
    ∀ u v : Q 3, blockDiff (blockDiff u v) v = u := by decide

private theorem blockDiff_anti :
    ∀ u v : Q 3, blockDiff (anti (blockDiff (anti u) v)) v = u := by decide

private theorem blockDiff_parity :
    ∀ u v : Q 3, blockParity (blockDiff u v) = blockParity u + blockParity v := by decide

private theorem anti_blockParity :
    ∀ u : Q 3, blockParity (anti u) = !blockParity u := by decide

private theorem blockDiff_eq_right :
    ∀ u v : Q 3, blockDiff u v = v ↔ u = fun _ => false := by decide

private theorem parity_class_card (b : Bool) :
    ({x : Q 3 | blockParity x = b} : Set (Q 3)).ncard = 4 := by
  have hcard : (univ.filter (fun x : Q 3 => blockParity x = b)).card = 4 := by
    cases b <;> decide
  have hf : ({x : Q 3 | blockParity x = b} : Set (Q 3)).Finite := Set.toFinite _
  have he : hf.toFinset =
      univ.filter (fun x : Q 3 => blockParity x = b) := by
    ext x
    simp
  rw [Set.ncard_eq_toFinset_card _ hf, he]
  exact hcard

private theorem omit_one {P : Set (Q 3)} {b : Bool} (hcard : P.ncard = 3)
    (hP : ∀ x ∈ P, blockParity x = b) :
    ∃ m, blockParity m = b ∧ ∀ x, x ∈ P ↔ blockParity x = b ∧ x ≠ m := by
  let B : Set (Q 3) := {x | blockParity x = b}
  have hb : B.ncard = 4 := parity_class_card b
  have hsub : P ⊆ B := fun x hx => hP x hx
  have hd : (B \ P).ncard = 1 := by
    rw [Set.ncard_sdiff' hsub, hb, hcard]
  obtain ⟨m, hmB, hmP⟩ := (Set.ncard_pos (s := B \ P)).mp (by omega)
  have hsub' : P ⊆ B \ {m} := fun x hx =>
    ⟨hP x hx, fun he => hmP ((Set.mem_singleton_iff.mp he) ▸ hx)⟩
  have hB' : (B \ {m}).ncard = 3 := by
    rw [Set.ncard_sdiff_singleton_of_mem hmB, hb]
  have he : P = B \ {m} := Set.eq_of_subset_of_ncard_le hsub' (by rw [hB', hcard])
  exact ⟨m, hmB, fun x => by rw [he]; rfl⟩

private def evenGrid : Finset (BitVec 9) := {15, 27, 30, 39, 45, 51, 54, 57, 60}
private def oddGrid : Finset (BitVec 9) := {3, 6, 9, 12, 18, 24, 33, 36, 48}

private def wordRow (w : BitVec 9) : Q 3 := fun i => w.getLsbD (2 * i.val)
private def wordCol (w : BitVec 9) : Q 3 := fun i => w.getLsbD (2 * i.val + 1)

private theorem even_grid_facts :
    ∀ w ∈ evenGrid, blockParity (wordRow w) = false ∧ blockParity (wordCol w) = false ∧
      wordRow w ≠ (fun _ => false) ∧ wordCol w ≠ (fun _ => false) := by decide

private theorem odd_grid_facts :
    ∀ w ∈ oddGrid, blockParity (wordRow w) = true ∧ blockParity (wordCol w) = true ∧
      anti (wordRow w) ≠ (fun _ => false) ∧ anti (wordCol w) ≠ (fun _ => false) := by decide

private theorem encode_blocks (σ : Equiv.Perm (Fin 9)) (m n a c z : Q 3)
    (w : BitVec 9) (ha : blockDiff a m = wordRow w) (hc : blockDiff c n = wordCol w)
    (hz : ∀ i : Fin 3, w.getLsbD (6 + i.val) = false) :
    normalize (shuffle.trans σ) (orientedVertex σ m n z) (orientedVertex σ a c z) =
      cubeBitVec 9 w := by
  funext i
  change ((orientedVertex σ a c z (σ (shuffle i))) !=
    (orientedVertex σ m n z (σ (shuffle i)))) = w.getLsbD i.val
  simp only [orientedVertex, Equiv.symm_apply_apply]
  have hdiff (k : Fin 9) :
      (SixAxisGridSignedCompression.vertex a c z k != SixAxisGridSignedCompression.vertex m n z k) =
        SixAxisGridSignedCompression.vertex (blockDiff a m) (blockDiff c n) (blockDiff z z) k := by
    unfold SixAxisGridSignedCompression.vertex
    refine Fin.addCases (m := 3) (n := 6) (fun j => ?_) (fun j => ?_) k
    · simp only [Fin.append_left, blockDiff]
    · simp only [Fin.append_right]
      refine Fin.addCases (m := 3) (n := 3) (fun j => ?_) (fun j => ?_) j
      · simp only [Fin.append_left, blockDiff]
      · simp only [Fin.append_right, blockDiff]
  rw [hdiff, ha, hc]
  have hzero : blockDiff z z = fun _ => false := by
    funext t
    simp [blockDiff]
  rw [hzero]
  fin_cases i <;>
    first | rfl | exact (hz 0).symm | exact (hz 1).symm | exact (hz 2).symm

private theorem grid_exterior :
    ∀ w ∈ evenGrid ∪ oddGrid, ∀ i : Fin 3, w.getLsbD (6 + i.val) = false := by decide

private theorem exists_center_of_rectangle
    {σ : Equiv.Perm (Fin 9)} {C D : Finset (Q 9)} {a c z : Q 3} {b : Bool}
    {R S : Set (Q 3)} (hr : R.ncard = 3) (hs : S.ncard = 3)
    (hpar : parity (orientedVertex σ a c z) = b)
    (hC : leftLayer σ C z (blockParity a) (blockParity c) = R ×ˢ S)
    (hD : alignedLayer σ D z (blockParity a) (blockParity c) = R ×ˢ S) :
    ∃ o : Q 9, parity o = b ∧
      (∀ w ∈ evenGrid, cubeBitVec 9 w ∈ C.map (normalize (shuffle.trans σ) o).toEmbedding) ∧
      (∀ w ∈ oddGrid, cubeBitVec 9 w ∈ D.map (normalize (shuffle.trans σ) o).toEmbedding) := by
  obtain ⟨r, hr'⟩ := (Set.ncard_pos (s := R)).mp (by omega)
  obtain ⟨s, hs'⟩ := (Set.ncard_pos (s := S)).mp (by omega)
  obtain ⟨m, hm, hR⟩ := omit_one hr fun x hx =>
    (show (x,s) ∈ leftLayer σ C z (blockParity a) (blockParity c) from
      hC.symm ▸ Set.mem_prod.mpr ⟨hx, hs'⟩).1
  obtain ⟨n, hn, hS⟩ := omit_one hs fun x hx =>
    (show (r,x) ∈ leftLayer σ C z (blockParity a) (blockParity c) from
      hC.symm ▸ Set.mem_prod.mpr ⟨hr', hx⟩).2.1
  let o := orientedVertex σ m n z
  have hp : parity o = b := by
    dsimp only [o]
    rw [row_parity m a n z hm, col_parity a n c z hn, hpar]
  have hmem {t : Q 3} {P : Set (Q 3)} {m : Q 3}
      (hP : ∀ x, x ∈ P ↔ blockParity x = blockParity m ∧ x ≠ m)
      (ht : blockParity t = false) (hn : t ≠ (fun _ => false)) :
      blockDiff t m ∈ P := by
    exact (hP _).mpr ⟨by rw [blockDiff_parity, ht]; cases blockParity m <;> decide,
      fun h => hn ((blockDiff_eq_right _ _).mp h)⟩
  have hRow : ∀ x, x ∈ R ↔ blockParity x = blockParity m ∧ x ≠ m := by
    simpa only [hm] using hR
  have hCol : ∀ x, x ∈ S ↔ blockParity x = blockParity n ∧ x ≠ n := by
    simpa only [hn] using hS
  refine ⟨o, hp, ?_, ?_⟩
  · intro w hw
    obtain ⟨hr, hc, hrn, hcn⟩ := even_grid_facts w hw
    have h := show (blockDiff (wordRow w) m, blockDiff (wordCol w) n) ∈
        leftLayer σ C z (blockParity a) (blockParity c) from
      hC.symm ▸ Set.mem_prod.mpr ⟨hmem hRow hr hrn, hmem hCol hc hcn⟩
    exact mem_map.mpr ⟨_, h.2.2, encode_blocks σ m n _ _ z w
      (blockDiff_cancel _ _) (blockDiff_cancel _ _) (grid_exterior w (mem_union_left _ hw))⟩
  · intro w hw
    obtain ⟨hr, hc, hrn, hcn⟩ := odd_grid_facts w hw
    have hr' : blockParity (anti (wordRow w)) = false := by rw [anti_blockParity, hr]; decide
    have hc' : blockParity (anti (wordCol w)) = false := by rw [anti_blockParity, hc]; decide
    have h := show (blockDiff (anti (wordRow w)) m, blockDiff (anti (wordCol w)) n) ∈
        alignedLayer σ D z (blockParity a) (blockParity c) from
      hD.symm ▸ Set.mem_prod.mpr ⟨hmem hRow hr' hrn, hmem hCol hc' hcn⟩
    exact mem_map.mpr ⟨_, h.2.2, encode_blocks σ m n _ _ z w
      (blockDiff_anti _ _) (blockDiff_anti _ _) (grid_exterior w (mem_union_right _ hw))⟩

private def rowMaskAxis (i : Fin 3) : Fin 9 := ⟨2 * i.val, by omega⟩
private def colMaskAxis (j : Fin 3) : Fin 9 := ⟨2 * j.val + 1, by omega⟩

private theorem shuffle_row :
    ∀ i : Fin 3, shuffle (rowMaskAxis i) = i.castAdd 6 := by decide

private theorem shuffle_col :
    ∀ j : Fin 3, shuffle (colMaskAxis j) = Fin.natAdd 3 (j.castAdd 3) := by decide

open private mem_minimumDisplacements from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator

open Classical in
/-- One translation and axis permutation produce the two canonical rectangles.
Every even contact in those coordinates uses one axis from each triple. -/
theorem normalization_of_nine_masks_on_six_axes
    {C D : Finset (Q 9)} {b : Bool}
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcC : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetC : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w C false)).det = 0)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0)
    (haxes : (activeAxes (minimumDisplacements C D b 2)).card = 6)
    (hmask : (minimumDisplacements C D b 2).card = 9) :
    ∃ (π : Equiv.Perm (Fin 9)) (o : Q 9),
      let C' := C.map (normalize π o).toEmbedding
      let D' := D.map (normalize π o).toEmbedding
      (∀ w ∈ evenGrid, cubeBitVec 9 w ∈ C') ∧
      (∀ w ∈ oddGrid, cubeBitVec 9 w ∈ D') ∧
      (∀ x ∈ C', ∀ y ∈ D', parity x = false → hammingDist x y = 2 →
        ∃ i j : Fin 3, differingAxes x y = {rowMaskAxis i, colMaskAxis j}) := by
  obtain ⟨σ, hσ⟩ := nine_masks_on_six_axes_force_contact_rectangles
    hsep hrC hrD hcC hcD hbC hbD hdetC hdetD haxes hmask
  obtain ⟨mask, hm⟩ := card_pos.mp (by omega : 0 < (minimumDisplacements C D b 2).card)
  obtain ⟨x, hx, y, hy, hp, hd, _⟩ := mem_minimumDisplacements.mp hm
  obtain ⟨a, c, z, _, _, R, S, hax, _, hR, hS, hC, hD⟩ := hσ x hx y hy hp hd
  obtain ⟨o, ho, hL, hR'⟩ := exists_center_of_rectangle hR hS (hax ▸ hp) hC hD
  let π := shuffle.trans σ
  refine ⟨π, o, hL, hR', ?_⟩
  intro u hu v hv hpu huv
  obtain ⟨u, hu', rfl⟩ := mem_map.mp hu
  obtain ⟨v, hv', rfl⟩ := mem_map.mp hv
  change parity (normalize π o u) = false at hpu
  change hammingDist (normalize π o u) (normalize π o v) = 2 at huv
  have hpu' : parity u = b := by
    rw [parity_normalize, ho] at hpu
    have hzero : ∀ p q : Bool, p + q = false → p = q := by decide
    exact hzero _ _ hpu
  rw [normalize_hammingDist] at huv
  obtain ⟨a', c', z', i, j, _, _, hu'', hv'', _⟩ := hσ u hu' v hv' hpu' huv
  have hrow : π (rowMaskAxis i) = orientedRow σ i := by
    simp [π, orientedRow, shuffle_row]
  have hcol : π (colMaskAxis j) = orientedCol σ j := by
    simp [π, orientedCol, shuffle_col]
  have hflip : v = flip (flip u (orientedRow σ i)) (orientedCol σ j) := by
    rw [hu'', flip_row, flip_col]
    exact hv''
  have hdiff : differingAxes u v = {orientedRow σ i, orientedCol σ j} := by
    rw [hflip]
    simpa only [List.foldl_cons, List.foldl_nil, List.toFinset_cons, List.toFinset_nil,
      insert_empty] using differingAxes_foldl_flip [orientedRow σ i, orientedCol σ j]
        (by simp [row_col_ne]) u
  refine ⟨i, j, ?_⟩
  change differingAxes (normalize π o u) (normalize π o v) = _
  rw [normalize_differingAxes, hdiff, ← hrow, ← hcol]
  simp

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9K33NormalizedRectangle
