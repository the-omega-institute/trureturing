import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoSignedCompletion
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ThinEdgeCertificates
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9GrayPlacementNormalForm
import Mathlib.Data.ZMod.Basic

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

private def encodeEntries (entries : List (Q 9 × ℤ)) : List (BitVec 9 × ℤ) :=
  entries.map fun entry => ((cubeBitVec 9).symm entry.1, entry.2)

private def valueAt (entries : List (BitVec 9 × ℤ)) (x : BitVec 9) : ℤ :=
  ((entries.find? fun e => decide (e.1 = x)).map Prod.snd).getD 0

private theorem valueAt_encode (entries : List (Q 9 × ℤ)) (x : BitVec 9) :
    valueAt (encodeEntries entries) x = valueIn entries (cubeBitVec 9 x) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    have heq : (cubeBitVec 9).symm entry.1 = x ↔ entry.1 = cubeBitVec 9 x :=
      (cubeBitVec 9).symm_apply_eq
    by_cases h : entry.1 = cubeBitVec 9 x
    · simp [valueAt, encodeEntries, valueIn, h]
    · simpa [valueAt, encodeEntries, valueIn, List.find?_cons, mt heq.mp h, h] using ih

private def flipBit (x : BitVec 9) (i : Fin 9) : BitVec 9 :=
  x ^^^ BitVec.ofNat 9 (2 ^ i.val)

private theorem decode_flip (x : BitVec 9) (i : Fin 9) :
    cubeBitVec 9 (flipBit x i) = BalancedCriticalSpectrum.flip (cubeBitVec 9 x) i :=
  cubeBitVec_xor_single x i

private def completedValue (entries : List (BitVec 9 × ℤ)) (x : BitVec 9) : ℤ :=
  if x.getLsbD 0 = false then valueAt entries x
  else
    let y := flipBit x 0
    3 * valueAt entries y - ∑ i ∈ Finset.univ.erase (0 : Fin 9),
      truePrefixSign (cubeBitVec 9 y) i * valueAt entries (flipBit y i)

private theorem completedValue_encode (wagner : Bool) (highs : Placement)
    (signs : Fin 128) (x : BitVec 9) :
    completedValue (encodeEntries (signedRecords wagner (cubeBitVec 9 ∘ highs)
      (unitSign ∘ signsFromMask signs))) x =
      complete wagner (cubeBitVec 9 ∘ highs) (unitSign ∘ signsFromMask signs) (cubeBitVec 9 x) := by
  simp only [completedValue, complete, valueAt_encode, decode_flip]
  rfl

-- Modulo two, a signed cut row only counts the occupied vertices in the first half.
private def completedParity (entries : List (BitVec 9 × ℤ)) (x : BitVec 9) : ZMod 2 :=
  if x.getLsbD 0 = false then (valueAt entries x : ZMod 2)
  else
    let y := flipBit x 0
    (valueAt entries y : ZMod 2) + ∑ i ∈ Finset.univ.erase (0 : Fin 9),
      (valueAt entries (flipBit y i) : ZMod 2)

private theorem completedParity_eq (entries : List (BitVec 9 × ℤ)) (x : BitVec 9) :
    completedParity entries x = (completedValue entries x : ZMod 2) := by
  have hneg : (-1 : ZMod 2) = 1 := by decide
  have hthree : (3 : ZMod 2) = 1 := by decide
  have hsub (a b : ZMod 2) : a - b = a + b := by
    revert a b
    decide
  simp only [completedParity, completedValue]
  split
  · rfl
  · simp [truePrefixSign, hneg, hthree, hsub]

private def rowChecked (wagner : Bool) (row : Witness) : Bool :=
  decide (∀ i j : Fin 9, row.axes i = row.axes j → i = j) &&
  let entries := encodeEntries (signedRecords wagner (cubeBitVec 9 ∘ row.highs)
    (unitSign ∘ signsFromMask row.signs))
  (List.finRange 512).all fun v =>
    if (supportMask row.representative).testBit v.val then
      decide (completedParity entries
        ((cubeBitVec 9).symm (preimage row (cubeBitVec 9 (BitVec.ofFin v)))) ≠ 0)
    else true

private theorem row_preimages (wagner : Bool) (row : Witness)
    (hrow : rowChecked wagner row = true) :
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
      decide (completedParity _ ((cubeBitVec 9).symm (preimage row (cubeBitVec 9 x))) ≠ 0)
      else true) = true at hpoint
    simp only [hbit, ↓reduceIte] at hpoint
    refine Finset.mem_map.mpr ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    simp only [Q9SeventyTwoSignedCompletion.support, Finset.mem_filter, Finset.mem_univ,
      true_and, hinverse]
    have hn : completedParity _ ((cubeBitVec 9).symm (preimage row (cubeBitVec 9 x))) ≠ 0 :=
      of_decide_eq_true hpoint
    rw [completedParity_eq, completedValue_encode, Equiv.apply_symm_apply] at hn
    intro hz
    exact hn (by rw [hz, Int.cast_zero])

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

private def smallerPatternWitnesses (wagner : Bool) (pattern : Fin 5) : List Witness :=
  match wagner, pattern.val with
  | false, 1 => cubePatternOne
  | false, 2 => [
      ⟨![0, 18, 36, 54, 24, 80, 60, 116], 57, 0, ![0, 1, 5, 2, 4, 3, 8, 6, 7], 0, 0⟩,
      ⟨![0, 18, 36, 54, 24, 80, 60, 116], 95, 0, ![0, 1, 3, 2, 4, 5, 8, 6, 7], 0, 0⟩,
      ⟨![0, 18, 36, 54, 24, 144, 60, 180], 57, 0, ![0, 1, 5, 2, 4, 3, 6, 8, 7], 0, 0⟩,
      ⟨![0, 18, 36, 54, 24, 144, 60, 180], 95, 0, ![0, 1, 3, 2, 4, 5, 6, 8, 7], 0, 0⟩,
      ⟨![0, 18, 36, 54, 24, 272, 60, 308], 57, 0, ![0, 1, 5, 2, 4, 3, 6, 7, 8], 0, 0⟩,
      ⟨![0, 18, 36, 54, 24, 272, 60, 308], 95, 0, ![0, 1, 3, 2, 4, 5, 6, 7, 8], 0, 0⟩,
    ]
  | false, 3 => [
      ⟨![0, 18, 36, 54, 40, 58, 96, 114], 63, 0, ![0, 3, 1, 2, 5, 4, 8, 6, 7], 0, 0⟩,
      ⟨![0, 18, 36, 54, 40, 58, 96, 114], 106, 0, ![0, 5, 1, 2, 3, 4, 8, 6, 7], 0, 0⟩,
      ⟨![0, 18, 36, 54, 40, 58, 160, 178], 63, 0, ![0, 3, 1, 2, 5, 4, 6, 8, 7], 0, 0⟩,
      ⟨![0, 18, 36, 54, 40, 58, 160, 178], 106, 0, ![0, 5, 1, 2, 3, 4, 6, 8, 7], 0, 0⟩,
      ⟨![0, 18, 36, 54, 40, 58, 288, 306], 63, 0, ![0, 3, 1, 2, 5, 4, 6, 7, 8], 0, 0⟩,
      ⟨![0, 18, 36, 54, 40, 58, 288, 306], 106, 0, ![0, 5, 1, 2, 3, 4, 6, 7, 8], 0, 0⟩,
    ]
  | true, 1 => [
      ⟨![0, 18, 58, 60, 20, 80, 120, 40], 59, 1, ![0, 1, 2, 5, 4, 3, 8, 6, 7], 0, 0⟩,
      ⟨![0, 18, 58, 60, 20, 80, 120, 40], 93, 1, ![0, 1, 2, 3, 4, 5, 8, 6, 7], 0, 0⟩,
      ⟨![0, 18, 58, 60, 20, 144, 184, 40], 59, 1, ![0, 1, 2, 5, 4, 3, 6, 8, 7], 0, 0⟩,
      ⟨![0, 18, 58, 60, 20, 144, 184, 40], 93, 1, ![0, 1, 2, 3, 4, 5, 6, 8, 7], 0, 0⟩,
      ⟨![0, 18, 58, 60, 20, 272, 312, 40], 59, 1, ![0, 1, 2, 5, 4, 3, 6, 7, 8], 0, 0⟩,
      ⟨![0, 18, 58, 60, 20, 272, 312, 40], 93, 1, ![0, 1, 2, 3, 4, 5, 6, 7, 8], 0, 0⟩,
    ]
  | true, 3 => [
      ⟨![0, 18, 114, 96, 36, 54, 58, 40], 95, 1, ![0, 3, 2, 1, 5, 4, 8, 6, 7], 0, 0⟩,
      ⟨![0, 18, 114, 96, 36, 54, 58, 40], 108, 1, ![0, 5, 2, 1, 3, 4, 8, 6, 7], 0, 0⟩,
      ⟨![0, 18, 178, 160, 36, 54, 58, 40], 95, 1, ![0, 3, 2, 1, 5, 4, 6, 8, 7], 0, 0⟩,
      ⟨![0, 18, 178, 160, 36, 54, 58, 40], 108, 1, ![0, 5, 2, 1, 3, 4, 6, 8, 7], 0, 0⟩,
      ⟨![0, 18, 306, 288, 36, 54, 58, 40], 95, 1, ![0, 3, 2, 1, 5, 4, 6, 7, 8], 0, 0⟩,
      ⟨![0, 18, 306, 288, 36, 54, 58, 40], 108, 1, ![0, 5, 2, 1, 3, 4, 6, 7, 8], 0, 0⟩,
    ]
  | _, _ => []

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- Verify the placements and signings for this root pattern.
private theorem checked_false_2 :
    allCovered false 2 (smallerPatternWitnesses false 2) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- Verify the placements and signings for this root pattern.
private theorem checked_false_3 :
    allCovered false 3 (smallerPatternWitnesses false 3) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- Verify the placements and signings for this root pattern.
private theorem checked_true_0 :
    allCovered true 0 (smallerPatternWitnesses true 0) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- Verify the placements and signings for this root pattern.
private theorem checked_true_1 :
    allCovered true 1 (smallerPatternWitnesses true 1) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- Verify the placements and signings for this root pattern.
private theorem checked_true_2 :
    allCovered true 2 (smallerPatternWitnesses true 2) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- Verify the placements and signings for this root pattern.
private theorem checked_true_3 :
    allCovered true 3 (smallerPatternWitnesses true 3) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- Verify the placements and signings for this root pattern.
private theorem checked_true_4 :
    allCovered true 4 (smallerPatternWitnesses true 4) = true := by
  decide +kernel

private theorem smaller_patterns_checked (wagner : Bool) (pattern : Fin 5)
    (h : wagner = false → pattern ≠ 0 ∧ pattern ≠ 4) :
    allCovered wagner pattern (smallerPatternWitnesses wagner pattern) = true := by
  have hpattern : pattern = 0 ∨ pattern = 1 ∨ pattern = 2 ∨ pattern = 3 ∨ pattern = 4 := by
    omega
  cases wagner with
  | false =>
    rcases hpattern with rfl | rfl | rfl | rfl | rfl
    · exact ((h rfl).1 rfl).elim
    · exact cube_pattern_one_checked
    · exact checked_false_2
    · exact checked_false_3
    · exact ((h rfl).2 rfl).elim
  | true =>
    rcases hpattern with rfl | rfl | rfl | rfl | rfl
    · exact checked_true_0
    · exact checked_true_1
    · exact checked_true_2
    · exact checked_true_3
    · exact checked_true_4

/-- Outside the cube pattern with three disjoint root-axis pairs, every
surviving actual signing contains the image of an edge-certificate support. -/
theorem smaller_pattern_representative {wagner : Bool} {pattern : Fin 5}
    {highs : Placement} {signs : Fin 128}
    (h : wagner = false → pattern ≠ 0 ∧ pattern ≠ 4)
    (hh : highs ∈ candidates wagner pattern)
    (hs : signs ∈ signMasks wagner (cubeBitVec 9 ∘ highs)) :
    ∃ (k : Fin 7) (e : Q 9 ≃ BitVec 9),
      (∀ x y, Q9GrayCrossedPlacement.cube.Adj (e x) (e y) ↔ (hypercube 9).Adj x y) ∧
      Q9ThinEdgeCertificates.support k ⊆
        (Q9SeventyTwoSignedCompletion.support wagner (cubeBitVec 9 ∘ highs)
          (signsFromMask signs)).map e.toEmbedding := by
  have hc := List.all_eq_true.mp (smaller_patterns_checked wagner pattern h) highs hh
  exact covered_spec (List.all_eq_true.mp hc signs hs)

#print axioms smaller_pattern_representative

end D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ThinOrbitCertificate
