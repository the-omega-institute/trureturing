import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoSignedCompletion
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ThinEdgeCertificates
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9GrayPlacementNormalForm

/-! Transport normalized signed thin slices to the supports used by the edge certificates. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ThinOrbitCertificate

open BalancedCriticalSpectrum (Q)
open Q9GrayPlacementNormalForm (normalize normalize_hammingDist)
open Q9SeventyTwoEmbeddingSearch (Placement candidates)
open Q9SeventyTwoSignedCompletion (complete signsFromMask signMasks)
open Q9ThinEdgeCertificates (supportMask)
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open private signedRecords valueIn unitSign from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoSignedCompletion

private structure Witness where
  highs : Placement
  signs : Fin 128
  representative : Fin 7
  axes : Fin 9 → Fin 9
  origin : BitVec 9
  image : BitVec 9

private def preimage (row : Witness) (v : Q 9) : Q 9 := fun i =>
  (v (row.axes i) != cubeBitVec 9 row.image (row.axes i)) != cubeBitVec 9 row.origin i

private def completedValue (entries : List (Q 9 × ℤ)) (x : Q 9) : ℤ :=
  if x 0 = false then valueIn entries x
  else
    let y := BalancedCriticalSpectrum.flip x 0
    3 * valueIn entries y - ∑ i ∈ Finset.univ.erase (0 : Fin 9),
      truePrefixSign y i * valueIn entries (BalancedCriticalSpectrum.flip y i)

private def rowChecked (wagner : Bool) (row : Witness) : Bool :=
  decide (∀ i j : Fin 9, row.axes i = row.axes j → i = j) &&
  let entries := signedRecords wagner (cubeBitVec 9 ∘ row.highs)
    (unitSign ∘ signsFromMask row.signs)
  (List.finRange 512).all fun v =>
    if (supportMask row.representative).testBit v.val then
      decide (completedValue entries (preimage row (cubeBitVec 9 (BitVec.ofFin v))) ≠ 0)
    else true

private theorem row_preimages (wagner : Bool) (row : Witness) (hrow : rowChecked wagner row = true) :
    ∃ e : Q 9 ≃ BitVec 9,
      (∀ x y, Q9GrayCrossedPlacement.cube.Adj (e x) (e y) ↔ (hypercube 9).Adj x y) ∧
      Q9ThinEdgeCertificates.support row.representative ⊆
        (Q9SeventyTwoSignedCompletion.support wagner (cubeBitVec 9 ∘ row.highs)
          (signsFromMask row.signs)).map e.toEmbedding := by
  obtain ⟨haxes, hpoints⟩ := Bool.and_eq_true_iff.mp hrow
  have hinj : Function.Injective row.axes := fun {i j} =>
    (of_decide_eq_true (p := ∀ i j : Fin 9, row.axes i = row.axes j → i = j) haxes) i j
  let p := Equiv.ofBijective row.axes ⟨hinj, Finite.surjective_of_injective hinj⟩
  let shift := normalize (Equiv.refl (Fin 9)) (cubeBitVec 9 row.image)
  let e := ((normalize p.symm (cubeBitVec 9 row.origin)).trans shift).trans (cubeBitVec 9).symm
  have hinverse (x : BitVec 9) : e.symm x = preimage row (cubeBitVec 9 x) := rfl
  refine ⟨e, ?_, ?_⟩
  · intro x y
    change (hypercube 9).Adj (cubeBitVec 9 (e x)) (cubeBitVec 9 (e y)) ↔ _
    simp only [e, Equiv.trans_apply, Equiv.apply_symm_apply]
    change (hammingDist (shift (normalize p.symm (cubeBitVec 9 row.origin) x))
      (shift (normalize p.symm (cubeBitVec 9 row.origin) y)) = 1) ↔ hammingDist x y = 1
    rw [normalize_hammingDist, normalize_hammingDist]
  · intro x hx
    have hbit : (supportMask row.representative).testBit x.toNat = true := by
      exact (Finset.mem_filter.mp hx).2
    have hpoint := List.all_eq_true.mp hpoints x.toFin (List.mem_finRange x.toFin)
    change (if (supportMask row.representative).testBit x.toNat then
      decide (completedValue _ (preimage row (cubeBitVec 9 x)) ≠ 0) else true) = true at hpoint
    simp only [hbit, ↓reduceIte] at hpoint
    refine Finset.mem_map.mpr ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    simp only [Q9SeventyTwoSignedCompletion.support, Finset.mem_filter, Finset.mem_univ,
      true_and, hinverse]
    exact of_decide_eq_true hpoint

private def covered (wagner : Bool) (rows : List Witness) (highs : Placement)
    (signs : Fin 128) : Bool :=
  rows.any fun row => (decide (row.signs = signs) &&
    (List.finRange 8).all (fun i => decide (row.highs i = highs i))) && rowChecked wagner row

private theorem covered_spec {wagner : Bool} {rows : List Witness} {highs : Placement}
    {signs : Fin 128} (h : covered wagner rows highs signs = true) :
    ∃ (k : Fin 7) (e : Q 9 ≃ BitVec 9),
      (∀ x y, Q9GrayCrossedPlacement.cube.Adj (e x) (e y) ↔ (hypercube 9).Adj x y) ∧
      Q9ThinEdgeCertificates.support k ⊆
        (Q9SeventyTwoSignedCompletion.support wagner (cubeBitVec 9 ∘ highs)
          (signsFromMask signs)).map e.toEmbedding := by
  obtain ⟨row, _, hr⟩ := List.any_eq_true.mp h
  obtain ⟨hm, hc⟩ := Bool.and_eq_true_iff.mp hr
  obtain ⟨hs, hh⟩ := Bool.and_eq_true_iff.mp hm
  have hs' : row.signs = signs := of_decide_eq_true hs
  have hh' : row.highs = highs := funext fun i =>
    of_decide_eq_true (List.all_eq_true.mp hh i (List.mem_finRange i))
  obtain ⟨e, ha, he⟩ := row_preimages wagner row hc
  exact ⟨row.representative, e, ha, by simpa only [hs', hh'] using he⟩

private def allCovered (wagner : Bool) (pattern : Fin 5) (rows : List Witness) : Bool :=
  (candidates wagner pattern).all fun highs =>
    (signMasks wagner (cubeBitVec 9 ∘ highs)).all (covered wagner rows highs)

private def cubePatternOne : List Witness := [
  ⟨![0, 18, 20, 80, 40, 58, 60, 120], 7, 0, ![0, 1, 2, 5, 4, 3, 8, 6, 7], 0, 0⟩,
  ⟨![0, 18, 20, 80, 40, 58, 60, 120], 127, 0, ![0, 1, 2, 3, 4, 5, 8, 6, 7], 0, 0⟩,
  ⟨![0, 18, 20, 144, 40, 58, 60, 184], 7, 0, ![0, 1, 2, 5, 4, 3, 6, 8, 7], 0, 0⟩,
  ⟨![0, 18, 20, 144, 40, 58, 60, 184], 127, 0, ![0, 1, 2, 3, 4, 5, 6, 8, 7], 0, 0⟩,
  ⟨![0, 18, 20, 272, 40, 58, 60, 312], 7, 0, ![0, 1, 2, 5, 4, 3, 6, 7, 8], 0, 0⟩,
  ⟨![0, 18, 20, 272, 40, 58, 60, 312], 127, 0, ![0, 1, 2, 3, 4, 5, 6, 7, 8], 0, 0⟩,
]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- Check the finite candidate list and its transported component vertices.
private theorem cube_pattern_one_checked : allCovered false 1 cubePatternOne = true := by
  decide +kernel

/-- Every signing surviving midpoint checks in the second cube root pattern
contains a transported edge-certificate support. -/
theorem cube_pattern_one_representative {highs : Placement} {signs : Fin 128}
    (hh : highs ∈ candidates false 1) (hs : signs ∈ signMasks false (cubeBitVec 9 ∘ highs)) :
    ∃ (k : Fin 7) (e : Q 9 ≃ BitVec 9),
      (∀ x y, Q9GrayCrossedPlacement.cube.Adj (e x) (e y) ↔ (hypercube 9).Adj x y) ∧
      Q9ThinEdgeCertificates.support k ⊆
        (Q9SeventyTwoSignedCompletion.support false (cubeBitVec 9 ∘ highs)
          (signsFromMask signs)).map e.toEmbedding := by
  have h := List.all_eq_true.mp cube_pattern_one_checked highs hh
  exact covered_spec (List.all_eq_true.mp h signs hs)

#print axioms cube_pattern_one_representative

end D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ThinOrbitCertificate
