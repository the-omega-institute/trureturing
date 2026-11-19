import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9GrayPlacementNormalForm
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9OrbitCertificateProbe

/-! A small set of points in the second support detects every forbidden
relative center of two normalized Gray placements. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Q9GrayRelativeCenters

open Q9GrayPlacementNormalForm
open Q9TriplePartitionOrbits (standardLabels secondLabels)
open D5.S3.Combinatorics.Graph.Hypercube

/-- Centers that survive the distance-one test for each of the five pairs. -/
def centers : Fin 5 → List (BitVec 9) :=
  ![[63, 127, 191, 255, 319, 383, 447, 455, 463, 471, 479, 487, 495, 503,
     504, 505, 506, 507, 508, 509, 510, 511],
    [255, 383, 447, 479, 495, 503, 504, 505, 506, 507, 508, 509, 510, 511],
    [255, 383, 447, 479, 495, 503, 507, 509, 510, 511],
    [255, 383, 447, 479, 495, 503, 507, 509, 510, 511],
    [255, 383, 447, 479, 495, 503, 507, 509, 510, 511]]

private def witnesses : Fin 5 → List (BitVec 9) :=
  ![[9, 66, 144, 292, 73, 146, 20, 72, 129, 34, 68],
    [9, 66, 144, 388, 42, 97, 265, 145, 96, 17],
    [3, 28, 352, 146, 69, 160, 266, 80, 9, 84],
    [3, 28, 352, 146, 265, 69, 160, 320, 9],
    [3, 28, 448, 98, 273, 168, 133, 140, 10, 12, 20]]

-- Bit x is set only if x lies in the closed neighborhood of the standard support.
private def nearMask : Nat :=
  (0x0000000000000000000000170017171600000017001717160017177f177f7f7f <<< 256) |||
    0x00000017001717160017177f177f7f7f0017177f177f7f7f0016167f167f7f16

private def neighbor (v : BitVec 9) (i : Fin 10) : BitVec 9 :=
  if i.val < 9 then v ^^^ BitVec.ofNat 9 (2 ^ i.val) else v

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
-- Verify the closed-neighborhood mask by testing each point and its nine neighbors.
private theorem near_sound : ∀ v : BitVec 9, nearMask.testBit v.toNat = true →
    ∃ i : Fin 10, Fits standardLabels origin (cubeBitVec 9 (neighbor v i)) ∧
      hammingDist (cubeBitVec 9 (neighbor v i)) (cubeBitVec 9 v) ≤ 1 := by
  decide +kernel

private theorem witnesses_fit : ∀ k : Fin 5, ∀ v ∈ witnesses k,
    Fits (secondLabels k) origin (cubeBitVec 9 v) := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
-- The finite check uses a single bit lookup per tested witness and relative center.
private theorem centers_or_collision : ∀ (k : Fin 5) (t : BitVec 9),
    t ∈ centers k ∨ (witnesses k).any (fun v => nearMask.testBit (v ^^^ t).toNat) = true := by
  decide +kernel

theorem fits_xor_center (block : Fin 9 → Fin 3) (v t : BitVec 9)
    (h : Fits block origin (cubeBitVec 9 v)) :
    Fits block (cubeBitVec 9 t) (cubeBitVec 9 (v ^^^ t)) := by
  have hx (i : Fin 9) :
      cubeBitVec 9 (v ^^^ t) i ≠ cubeBitVec 9 t i ↔ cubeBitVec 9 v i ≠ origin i := by
    change (v ^^^ t).getLsbD i.val ≠ t.getLsbD i.val ↔ v.getLsbD i.val ≠ false
    rw [BitVec.getLsbD_xor]
    cases v.getLsbD i.val <;> cases t.getLsbD i.val <;> decide
  simpa only [Fits, hammingDist, hx] using h

/-- Separation of the two components leaves only the listed relative centers.
Each rejected center has an actual support point at distance zero or one
from the first placement. -/
theorem center_mem_of_separated (k : Fin 5) (t : BitVec 9)
    (hsep : ∀ x ∈ placement standardLabels origin,
      ∀ y ∈ placement (secondLabels k) (cubeBitVec 9 t), 1 < hammingDist x y) :
    t ∈ centers k := by
  rcases centers_or_collision k t with h | h
  · exact h
  obtain ⟨v, hv, hnear⟩ := List.any_eq_true.mp h
  obtain ⟨i, hfit, hdist⟩ := near_sound (v ^^^ t) hnear
  exact (Nat.not_lt_of_ge hdist (hsep _ (mem_placement.mpr hfit)
    _ (mem_placement.mpr (fits_xor_center _ v t (witnesses_fit k v hv))))).elim

#print axioms center_mem_of_separated

/-- Representatives of the relative centers under coordinate permutations
preserving both partitions, with relabeling of their blocks allowed. -/
def representativeCenters : Fin 5 → List (BitVec 9) :=
  ![[63, 127, 255, 511], [255, 383, 504, 505, 507, 511],
    [255, 383, 479, 495, 511], [255, 383, 511], [255, 511]]

private abbrev Color := Fin 3 × Fin 3 × Bool

private def color (k : Fin 5) (t : BitVec 9) (i : Fin 9) : Color :=
  (standardLabels i, secondLabels k i, cubeBitVec 9 t i)

private def relabeledColor (k : Fin 5) (t : BitVec 9)
    (p q : Equiv.Perm (Fin 3)) (i : Fin 9) : Color :=
  (p.symm (standardLabels i), q.symm (secondLabels k i), cubeBitVec 9 t i)

private def colorCount (col : Fin 9 → Color) (c : Color) : ℕ :=
  (Finset.univ.filter (fun i => col i = c)).card

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
-- Check joint block-and-bit counts after independently relabeling the two partitions.
private theorem representative_counts : ∀ (k : Fin 5) (t : BitVec 9), t ∈ centers k →
    ∃ r ∈ representativeCenters k, ∃ p q : Equiv.Perm (Fin 3), ∀ c,
      colorCount (color k r) c = colorCount (relabeledColor k t p q) c := by
  decide +kernel

/-- Every separated normalized placement is equivalent to one of the twenty
representatives. The same coordinate permutation acts on both components. -/
theorem representative_of_separated (k : Fin 5) (t : BitVec 9)
    (hsep : ∀ x ∈ placement standardLabels origin,
      ∀ y ∈ placement (secondLabels k) (cubeBitVec 9 t), 1 < hammingDist x y) :
    ∃ r ∈ representativeCenters k, ∃ σ : Equiv.Perm (Fin 9),
      (placement standardLabels origin).map (normalize σ origin).toEmbedding =
        placement standardLabels origin ∧
      (placement (secondLabels k) (cubeBitVec 9 t)).map (normalize σ origin).toEmbedding =
        placement (secondLabels k) (cubeBitVec 9 r) := by
  obtain ⟨r, hr, p, q, hc⟩ := representative_counts k t (center_mem_of_separated k t hsep)
  obtain ⟨σ, hσ⟩ := exists_perm_of_coordinate_color_counts
    (color k r) (relabeledColor k t p q) hc
  have hb (i : Fin 9) : standardLabels (σ i) = p (standardLabels i) ∧
      secondLabels k (σ i) = q (secondLabels k i) ∧
      cubeBitVec 9 t (σ i) = cubeBitVec 9 r i := by
    simpa [color, relabeledColor, Prod.mk.injEq, Equiv.symm_apply_eq] using hσ i
  have hn (x : Vertex) : normalize σ origin x = fun i => x (σ i) := by
    funext i
    change (x (σ i) != false) = x (σ i)
    cases x (σ i) <;> rfl
  refine ⟨r, hr, σ, ?_, ?_⟩
  · have ho : normalize σ origin origin = origin := by
      rw [hn]
      rfl
    simpa only [ho] using
      normalize_placement σ p standardLabels standardLabels (fun i => (hb i).1) origin origin
  · have ht : normalize σ origin (cubeBitVec 9 t) = cubeBitVec 9 r := by
      rw [hn]
      exact funext (fun i => (hb i).2.2)
    simpa only [ht] using
      normalize_placement σ q (secondLabels k) (secondLabels k)
        (fun i => (hb i).2.1) origin (cubeBitVec 9 t)

#print axioms representative_of_separated

/-- A separated pair of Gray placements lies in one of the listed cases
after a common isometry of the whole nine-cube. -/
theorem separated_pair_normal_form
    (first second : Fin 9 → Fin 3) (c d : Vertex)
    (hfirst : ∀ b, (Finset.univ.filter (fun i => first i = b)).card = 3)
    (hsecond : ∀ b, (Finset.univ.filter (fun i => second i = b)).card = 3)
    (hsep : ∀ x ∈ placement first c,
      ∀ y ∈ placement second d, 1 < hammingDist x y) :
    ∃ (e : Vertex ≃ Vertex) (k : Fin 5), ∃ r ∈ representativeCenters k,
      (∀ x y, hammingDist (e x) (e y) = hammingDist x y) ∧
      (placement first c).map e.toEmbedding = placement standardLabels origin ∧
      (placement second d).map e.toEmbedding = placement (secondLabels k) (cubeBitVec 9 r) := by
  obtain ⟨e, k, t, hd, hA, hB⟩ := normalize_pair first second c d hfirst hsecond
  let b := (cubeBitVec 9).symm t
  have ht : cubeBitVec 9 b = t := Equiv.apply_symm_apply _ _
  have hsep' : ∀ x ∈ placement standardLabels origin,
      ∀ y ∈ placement (secondLabels k) (cubeBitVec 9 b), 1 < hammingDist x y := by
    intro x hx y hy
    rw [← hA] at hx
    rw [ht, ← hB] at hy
    obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_map.mp hy
    change 1 < hammingDist (e x') (e y')
    rw [hd]
    exact hsep x' hx' y' hy'
  obtain ⟨r, hr, σ, hA', hB'⟩ := representative_of_separated k b hsep'
  let f := normalize σ origin
  refine ⟨e.toEquiv.trans f, k, r, hr, ?_, ?_, ?_⟩
  · intro x y
    change hammingDist (f (e x)) (f (e y)) = hammingDist x y
    rw [normalize_hammingDist, hd]
  · change (placement first c).map (e.toEquiv.toEmbedding.trans f.toEmbedding) = _
    rw [← Finset.map_map, hA]
    exact hA'
  · change (placement second d).map (e.toEquiv.toEmbedding.trans f.toEmbedding) = _
    rw [← Finset.map_map, hB, ← ht]
    exact hB'

#print axioms separated_pair_normal_form

end D5.S3.Combinatorics.Graph.HypercubeCritical.Q9GrayRelativeCenters
