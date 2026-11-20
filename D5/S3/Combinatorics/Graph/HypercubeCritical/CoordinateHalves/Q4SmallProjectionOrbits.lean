/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q4SmallProjectionOrbits
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q4SmallProjectionOrbits
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: XOR and coordinate-permutation orbits of small four-cube projections. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9FourProjection
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.Dedup

/-! The eight- and nine-point four-cube envelopes used in Hong–Wu–Xia,
§7 Problem 2. Bit indices are little-endian. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q4SmallProjectionOrbits

open Q9FourProjection (flipBit)

/-- Directions of the occupied neighbors of `x`. -/
def neighborDirections (P : Finset (BitVec 4)) (x : BitVec 4) : Finset (Fin 4) :=
  Finset.univ.filter fun i => flipBit x i ∈ P

/-- The eight-point representative for `false` and the nine-point representative for `true`. -/
def representative (nine : Bool) : Finset (BitVec 4) :=
  if nine then {0, 1, 2, 3, 4, 11, 12, 13, 15} else {0, 1, 2, 5, 10, 13, 14, 15}

/-- The bit at output coordinate `i` is the input bit at coordinate `σ i`. -/
def permute (σ : Equiv.Perm (Fin 4)) (x : BitVec 4) : BitVec 4 :=
  (cubeBitVec 4).symm fun i => x.getLsbD (σ i).val

private def vertices : List (BitVec 4) :=
  (List.finRange 16).map (BitVec.ofFin (w := 4))

private theorem mem_vertices (x : BitVec 4) : x ∈ vertices :=
  List.mem_map.mpr ⟨x.toFin, List.mem_finRange _, BitVec.ofFin_toFin x⟩

private def occupied (mask : Nat) (x : BitVec 4) : Bool :=
  mask.testBit x.toNat

private def envelope (mask : Nat) : Finset (BitVec 4) :=
  (vertices.filter (occupied mask)).toFinset

private def size (mask : Nat) : Nat :=
  (vertices.filter (occupied mask)).length

private theorem mem_envelope (mask : Nat) (x : BitVec 4) :
    x ∈ envelope mask ↔ occupied mask x = true := by
  rw [envelope, List.mem_toFinset, List.mem_filter]
  exact ⟨And.right, fun h => ⟨mem_vertices x, h⟩⟩

private theorem envelope_card (mask : Nat) : (envelope mask).card = size mask :=
  List.toFinset_card_of_nodup ((show vertices.Nodup by decide +kernel).filter _)

private def encode (P : Finset (BitVec 4)) : Nat :=
  ((cubeBitVec 16).symm fun i => decide (BitVec.ofFin (w := 4) i ∈ P)).toNat

private theorem envelope_encode (P : Finset (BitVec 4)) : envelope (encode P) = P := by
  ext x
  rw [mem_envelope]
  have hx := congrFun ((cubeBitVec 16).apply_symm_apply
    (fun i : Fin 16 => decide (BitVec.ofFin (w := 4) i ∈ P))) x.toFin
  change occupied (encode P) x = decide (x ∈ P) at hx
  rw [hx, decide_eq_true_eq]

private def missingStart (mask : Nat) (i : Fin 4) (x : BitVec 4) : Bool :=
  !x.getLsbD i.val && (!occupied mask x && !occupied mask (flipBit x i))

private theorem missingStart_spec (mask : Nat) (i : Fin 4) (x : BitVec 4) :
    missingStart mask i x = true ↔
      x.getLsbD i.val = false ∧ x ∉ envelope mask ∧ flipBit x i ∉ envelope mask := by
  simp [missingStart, mem_envelope, Bool.and_eq_true_iff]

-- Once the first missing edge in a direction is found, there is at most one
-- other permitted start, the false endpoint of its antipodal edge.
private def antipodesOK (mask : Nat) (i : Fin 4) : Bool :=
  match vertices.find? (missingStart mask i) with
  | none => true
  | some x => vertices.all fun y =>
      if missingStart mask i y = true then decide (y = x ∨ y = flipBit (x ^^^ 15) i)
      else true

private theorem antipodesOK_of (mask : Nat)
    (h : ∀ (i : Fin 4) (x y : BitVec 4),
      x.getLsbD i.val = false → y.getLsbD i.val = false →
      x ∉ envelope mask → flipBit x i ∉ envelope mask →
      y ∉ envelope mask → flipBit y i ∉ envelope mask →
      x ≠ y → y = flipBit (x ^^^ 15) i) :
    (List.finRange 4).all (antipodesOK mask) = true := by
  apply List.all_eq_true.mpr
  intro i _
  cases hx : vertices.find? (missingStart mask i) with
  | none => simp only [antipodesOK, hx]
  | some x =>
    simp only [antipodesOK, hx]
    obtain ⟨hxi, hxP, hxf⟩ := (missingStart_spec mask i x).mp (List.find?_some hx)
    apply List.all_eq_true.mpr
    intro y _
    by_cases hy : missingStart mask i y = true
    · rw [if_pos hy]
      apply decide_eq_true
      by_cases hxy : x = y
      · exact Or.inl hxy.symm
      · obtain ⟨hyi, hyP, hyf⟩ := (missingStart_spec mask i y).mp hy
        exact Or.inr (h i x y hxi hyi hxP hxf hyP hyf hxy)
    · rw [if_neg hy]

private def degree (mask : Nat) (x : BitVec 4) : Nat :=
  ((List.finRange 4).filter fun i => occupied mask (flipBit x i)).length

private theorem degree_eq (mask : Nat) (x : BitVec 4) :
    degree mask x = (neighborDirections (envelope mask) x).card := by
  let dirs := (List.finRange 4).filter fun i => occupied mask (flipBit x i)
  have hnodup : dirs.Nodup := (List.nodup_finRange 4).filter _
  have hdirs : dirs.toFinset = neighborDirections (envelope mask) x := by
    ext i
    simp [dirs, neighborDirections, mem_envelope]
  calc
    degree mask x = dirs.toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
    _ = (neighborDirections (envelope mask) x).card := congrArg Finset.card hdirs

private def degreesOK (mask : Nat) : Bool :=
  vertices.all fun x =>
    if occupied mask x = true then
      decide (0 < degree mask x) &&
        (if degree mask x = 1 then
          (List.finRange 4).all fun i =>
            if occupied mask (flipBit x i) = true then
              decide (degree mask (flipBit x i) = 4)
            else true
        else true)
    else true

private theorem degreesOK_of (mask : Nat)
    (hne : ∀ x ∈ envelope mask, (neighborDirections (envelope mask) x).Nonempty)
    (hleaf : ∀ x ∈ envelope mask, ∀ i : Fin 4,
      neighborDirections (envelope mask) x = {i} →
        (neighborDirections (envelope mask) (flipBit x i)).card = 4) :
    degreesOK mask = true := by
  unfold degreesOK
  apply List.all_eq_true.mpr
  intro x _
  by_cases hx : occupied mask x = true
  · rw [if_pos hx]
    have hxP := (mem_envelope mask x).mpr hx
    apply Bool.and_eq_true_iff.mpr
    refine ⟨decide_eq_true ?_, ?_⟩
    · rw [degree_eq]
      exact Finset.card_pos.mpr (hne x hxP)
    by_cases hdeg : degree mask x = 1
    · rw [if_pos hdeg]
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp ((degree_eq mask x).symm.trans hdeg)
      apply List.all_eq_true.mpr
      intro i _
      by_cases hi : occupied mask (flipBit x i) = true
      · rw [if_pos hi]
        have hiMem : i ∈ neighborDirections (envelope mask) x :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_envelope mask _).mpr hi⟩
        have hij : i = j := Finset.mem_singleton.mp (hj ▸ hiMem)
        subst j
        exact decide_eq_true ((degree_eq mask _).trans (hleaf x hxP i hj))
      · rw [if_neg hi]
    · rw [if_neg hdeg]
  · rw [if_neg hx]

private def eligible (mask : Nat) : Bool :=
  (size mask == 8 || size mask == 9) &&
    ((List.finRange 4).all (antipodesOK mask) && degreesOK mask)

private def orbitMasks (nine : Bool) : List Nat :=
  (permsOfList (List.finRange 4)).flatMap fun σ =>
    vertices.map fun t => encode ((representative nine).image fun x => permute σ x ^^^ t)

-- Each range check reuses this numeric table.
private def orbitTable (nine : Bool) : List Nat :=
  if nine then [
    7129, 7130, 7132, 7160, 7609, 7610, 7612, 7672, 8120, 8152,
    10213, 10214, 10220, 10228, 11893, 11894, 11900, 12020, 12148, 12260,
    13741, 13742, 13756, 13804, 14252, 14308, 14941, 14942, 14972, 15068,
    15196, 15320, 15788, 15800, 15964, 15988, 18403, 18406, 18410, 18418,
    20083, 20086, 20090, 20210, 20338, 20450, 21451, 21454, 21466, 21482,
    22474, 22498, 23498, 23512, 23611, 23614, 23674, 23738, 23866, 23992,
    24122, 24178, 26594, 26596, 28274, 28276, 29263, 29278, 29294, 29390,
    29518, 29642, 29743, 29758, 29806, 29870, 29998, 30124, 30254, 30286,
    31310, 31324, 31790, 31802, 35795, 35797, 35801, 35825, 36275, 36277,
    36281, 36337, 36785, 36817, 39889, 39896, 40369, 40376, 41927, 41933,
    41941, 41957, 42949, 42980, 43973, 43985, 44087, 44093, 44149, 44213,
    44341, 44465, 44597, 44660, 45455, 45469, 45485, 45517, 45965, 46021,
    46477, 46508, 47135, 47165, 47197, 47261, 47389, 47501, 47645, 47708,
    48157, 48181, 50599, 50603, 50611, 50659, 51107, 51170, 51799, 51803,
    51827, 51923, 52051, 52177, 52643, 52657, 52819, 52850, 53647, 53659,
    53675, 53707, 54155, 54218, 54667, 54691, 55327, 55355, 55387, 55451,
    55579, 55691, 55835, 55891, 56347, 56378, 57935, 57943, 57959, 58055,
    58183, 58309, 58415, 58423, 58471, 58535, 58663, 58787, 58919, 58951,
    59975, 59987, 60455, 60469, 61835, 61837, 62023, 62030, 62503, 62510,
    63515, 63517
  ] else [
    7128, 7608, 10212, 11892, 13740, 14940, 18402, 20082, 21450, 23610,
    29262, 29742, 35793, 36273, 41925, 44085, 45453, 47133, 50595, 51795,
    53643, 55323, 57927, 58407
  ]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 120000000 in
-- Kernel reduction checks every table entry against the enumerated orbit.
private theorem orbitTable_checked (nine : Bool) :
    (orbitTable nine).all (orbitMasks nine).contains = true := by
  cases nine <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 120000000 in
-- The 64 block checks evaluate the eligibility tests on all 65,536 masks.
private theorem masks_checked (block : Fin 64) :
    ((List.range' (1024 * block.val) 1024).filter eligible).all
      (fun mask => (orbitTable (size mask == 9)).contains mask) = true := by
  fin_cases block <;> decide +kernel

private theorem mask_covered {mask : Nat} (hbound : mask < 65536)
    (heligible : eligible mask = true) : mask ∈ orbitMasks (size mask == 9) := by
  let block : Fin 64 := ⟨mask / 1024, by omega⟩
  have hmem : mask ∈ List.range' (1024 * block.val) 1024 := by
    apply List.mem_range'_1.mpr
    change 1024 * (mask / 1024) ≤ mask ∧ mask < 1024 * (mask / 1024) + 1024
    omega
  have htable := List.all_eq_true.mp (masks_checked block) mask
    (List.mem_filter.mpr ⟨hmem, heligible⟩)
  have hmemTable := List.contains_iff_mem.mp htable
  exact List.contains_iff_mem.mp
    (List.all_eq_true.mp (orbitTable_checked _) mask hmemTable)

/-- An eight- or nine-point envelope whose distinct parallel missing edges are
antipodal, with no isolated vertices and degree four at the neighbor of any
leaf, is an XOR translate of a coordinate permutation of the corresponding
representative. Missing edges are indexed by their false endpoints. The
classification uses only these conditions and the vertex count. -/
theorem small_projection_orbit (P : Finset (BitVec 4))
    (hsize : P.card = 8 ∨ P.card = 9)
    (hanti : ∀ (i : Fin 4) (x y : BitVec 4),
      x.getLsbD i.val = false → y.getLsbD i.val = false →
      x ∉ P → flipBit x i ∉ P → y ∉ P → flipBit y i ∉ P →
      x ≠ y → y = flipBit (x ^^^ 15) i)
    (hne : ∀ x ∈ P, (neighborDirections P x).Nonempty)
    (hleaf : ∀ x ∈ P, ∀ i : Fin 4, neighborDirections P x = {i} →
      (neighborDirections P (flipBit x i)).card = 4) :
    ∃ (t : BitVec 4) (σ : Equiv.Perm (Fin 4)),
      P = (representative (P.card == 9)).image (fun x => permute σ x ^^^ t) := by
  let mask := encode P
  have hdecode : envelope mask = P := envelope_encode P
  have hcard : size mask = P.card := (envelope_card mask).symm.trans (congrArg Finset.card hdecode)
  have hbound : mask < 65536 := by
    unfold mask encode
    exact BitVec.isLt _
  have heligible : eligible mask = true := by
    refine Bool.and_eq_true_iff.mpr ⟨?_, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
    · rcases hsize with h | h <;> simp [hcard, h]
    · exact antipodesOK_of mask (by simpa only [hdecode] using hanti)
    · exact degreesOK_of mask (by simpa only [hdecode] using hne)
        (by simpa only [hdecode] using hleaf)
  have hm := mask_covered hbound heligible
  rw [hcard] at hm
  unfold orbitMasks at hm
  obtain ⟨σ, _, hσ⟩ := List.mem_flatMap.mp hm
  obtain ⟨t, _, ht⟩ := List.mem_map.mp hσ
  exact ⟨t, σ, hdecode.symm.trans ((congrArg envelope ht).symm.trans (envelope_encode _))⟩

#print axioms small_projection_orbit

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q4SmallProjectionOrbits
