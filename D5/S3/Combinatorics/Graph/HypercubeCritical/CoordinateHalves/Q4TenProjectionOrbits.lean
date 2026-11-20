/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q4TenProjectionOrbits
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q4TenProjectionOrbits
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: XOR and coordinate-permutation orbits of ten-point four-cube projections. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q4SmallProjectionOrbits
import Mathlib.Data.List.Sort

/-! Ten-point four-cube projections for Hong–Wu–Xia, §7 Problem 2.
Vertex labels use little-endian bit indices. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q4TenProjectionOrbits

open Q9FourProjection (flipBit)
open Q4SmallProjectionOrbits (neighborDirections permute)
open private vertices occupied mem_envelope envelope envelope_card encode envelope_encode
  antipodesOK antipodesOK_of degree degree_eq size from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q4SmallProjectionOrbits

/-- Representatives of the six ten-point orbits. -/
def representative (r : Fin 6) : Finset (BitVec 4) :=
  match r.val with
  | 0 => {0, 1, 2, 3, 4, 5, 10, 11, 12, 14}
  | 1 => {0, 1, 2, 3, 4, 5, 10, 13, 14, 15}
  | 2 => {0, 1, 2, 3, 4, 7, 8, 12, 13, 15}
  | 3 => {0, 1, 2, 3, 4, 7, 9, 12, 13, 15}
  | 4 => {0, 1, 2, 3, 4, 11, 12, 13, 14, 15}
  | _ => {0, 1, 2, 4, 9, 10, 11, 12, 13, 14}

private def minDegreesOK (mask : Nat) : Bool :=
  vertices.all fun x => !occupied mask x || decide (2 ≤ degree mask x)

private theorem minDegreesOK_of (mask : Nat)
    (hmin : ∀ x ∈ envelope mask, 2 ≤ (neighborDirections (envelope mask) x).card) :
    minDegreesOK mask = true := by
  apply List.all_eq_true.mpr
  intro x _
  by_cases hx : occupied mask x = true
  · have h := hmin x ((mem_envelope mask x).mpr hx)
    simpa only [hx, Bool.not_true, Bool.false_or, decide_eq_true_eq, degree_eq] using h
  · simp [hx]

private def eligible (mask : Nat) : Bool :=
  (size mask == 10) && ((List.finRange 4).all (antipodesOK mask) && minDegreesOK mask)

private def orbitMasks (r : Fin 6) : List Nat :=
  (permsOfList (List.finRange 4)).flatMap fun σ =>
    vertices.map fun t => encode ((representative r).image fun x => permute σ x ^^^ t)

-- Sorted distinct masks for each representative, checked against the action below.
private def orbitTable (r : Fin 6) : List Nat :=
  match r.val with
  | 0 => [
    7131, 7133, 7162, 7611, 7613, 7676, 8122, 8156, 10215, 10222,
    10229, 11895, 11902, 12028, 12149, 12268, 13743, 13757, 13820, 14254,
    14324, 14943, 14974, 15100, 15197, 15352, 16220, 16244, 16300, 16312,
    18407, 18414, 18419, 20087, 20094, 20218, 20339, 20458, 21455, 21467,
    21498, 22478, 22514, 23615, 23678, 23802, 23867, 24056, 24378, 24434,
    24522, 24536, 29279, 29310, 29422, 29519, 29674, 29759, 29822, 29934,
    29999, 30188, 30510, 30542, 30690, 30692, 32302, 32314, 32334, 32348,
    32370, 32372, 35803, 35805, 35827, 36283, 36285, 36341, 36787, 36821,
    41935, 41959, 41973, 43981, 44017, 44095, 44221, 44277, 44599, 44788,
    44853, 44977, 44997, 45028, 45487, 45501, 45533, 45967, 46037, 47167,
    47293, 47325, 47647, 47836, 47901, 48013, 48081, 48088, 48413, 48437,
    48525, 48556, 48561, 48568, 50607, 50663, 50675, 51807, 51931, 51955,
    52651, 52721, 52823, 52978, 53075, 53155, 53201, 53218, 53691, 53711,
    53723, 54671, 54707, 55391, 55483, 55515, 56091, 56147, 56203, 56266,
    56273, 56280, 56351, 56506, 56603, 56715, 56753, 56760, 57975, 58063,
    58087, 58487, 58543, 58599, 59175, 59207, 59299, 59333, 59362, 59364,
    59983, 60019, 60463, 60533, 60967, 60999, 61042, 61044, 61867, 61901,
    62039, 62158, 62279, 62347, 62405, 62410, 62519, 62638, 62759, 62861,
    62883, 62892, 63547, 63581, 64027, 64078, 64083, 64092, 64541, 64558,
    64565, 64570
  ]
  | 1 => [
    7164, 7674, 8124, 8154, 10236, 12021, 12156, 12261, 13806, 14268,
    14310, 15069, 15228, 15321, 15789, 15801, 15852, 15864, 15966, 15990,
    16092, 16116, 16344, 16356, 18426, 20211, 20346, 20451, 21486, 22490,
    22502, 23499, 23513, 23530, 23544, 23739, 23930, 23993, 24126, 24182,
    24250, 24306, 24504, 24546, 26595, 26597, 26602, 26604, 28275, 28277,
    28282, 28284, 29391, 29550, 29643, 29871, 30062, 30125, 30270, 30302,
    30382, 30414, 30636, 30666, 31311, 31325, 31342, 31356, 31791, 31803,
    31854, 31866, 35829, 36339, 36789, 36819, 39891, 39893, 39898, 39900,
    40371, 40373, 40378, 40380, 41949, 42951, 42965, 42982, 42996, 43993,
    44005, 44151, 44349, 44405, 44473, 44529, 44662, 44725, 44916, 45009,
    45519, 45981, 46023, 46479, 46493, 46510, 46524, 47199, 47421, 47453,
    47533, 47565, 47710, 47773, 47964, 48069, 48159, 48183, 48285, 48309,
    50619, 51111, 51123, 51174, 51186, 51831, 52059, 52083, 52185, 52209,
    52665, 52707, 52854, 52947, 53106, 53169, 53679, 54159, 54171, 54222,
    54234, 54683, 54695, 55359, 55611, 55643, 55723, 55755, 55839, 55895,
    55963, 56019, 56382, 56475, 56634, 56739, 57951, 58191, 58215, 58317,
    58341, 58431, 58671, 58727, 58795, 58851, 58935, 58967, 59047, 59079,
    59995, 60007, 60477, 60519, 60981, 61011, 61869, 61899, 62046, 62151,
    62286, 62349, 62526, 62631, 62766, 62859, 63549, 63579, 64029, 64071,
    64539, 64551
  ]
  | 2 => [
    7134, 7161, 7614, 7673, 8121, 8153, 10221, 10230, 11901, 12022,
    12150, 12262, 13758, 13805, 14253, 14309, 14973, 15070, 15198, 15322,
    15790, 15802, 15965, 15989, 18411, 18422, 20091, 20214, 20342, 20454,
    21470, 21483, 22475, 22499, 23502, 23516, 23675, 23742, 23870, 23996,
    24123, 24179, 26610, 26612, 28402, 28404, 28530, 28532, 28642, 28644,
    29295, 29406, 29534, 29658, 29807, 29886, 30014, 30140, 30255, 30287,
    31438, 31452, 31566, 31580, 31690, 31704, 31918, 31930, 32046, 32058,
    32172, 32184, 35799, 35833, 36279, 36345, 36793, 36825, 39921, 39928,
    40433, 40440, 40881, 40888, 40913, 40920, 41943, 41965, 42957, 42988,
    43975, 43987, 44157, 44215, 44343, 44467, 44605, 44668, 45471, 45549,
    45997, 46053, 46541, 46572, 46989, 47020, 47045, 47076, 47229, 47263,
    47391, 47503, 47677, 47740, 48221, 48245, 48669, 48693, 48732, 48756,
    50615, 50667, 51115, 51178, 51835, 51927, 52055, 52181, 52647, 52661,
    52827, 52858, 53663, 53739, 54187, 54250, 54731, 54755, 55179, 55203,
    55242, 55266, 55419, 55455, 55583, 55695, 55867, 55923, 56411, 56442,
    56859, 56890, 56915, 56946, 57967, 58071, 58199, 58325, 58479, 58551,
    58679, 58803, 58927, 58959, 60103, 60115, 60231, 60243, 60357, 60369,
    60583, 60597, 60711, 60725, 60835, 60849, 61851, 61853, 62055, 62062,
    62567, 62574, 63015, 63022, 63047, 63054, 63643, 63645, 63771, 63773,
    63883, 63885
  ]
  | 3 => [
    6078, 6110, 6134, 7038, 7101, 7550, 7643, 8054, 10110, 10173,
    11133, 11245, 11257, 11965, 12007, 12217, 13694, 13799, 14174, 15037,
    15067, 15277, 15787, 15959, 18302, 18395, 19835, 19947, 19961, 20187,
    20199, 20441, 21374, 21479, 22334, 23501, 23741, 23771, 24011, 24119,
    26609, 28408, 28529, 28648, 29039, 29163, 29165, 29403, 29415, 29669,
    29885, 29927, 30179, 30239, 31468, 31565, 31720, 31978, 32043, 32232,
    32283, 32285, 32295, 32309, 32327, 32339, 32428, 32440, 32458, 32472,
    32482, 32484, 35773, 35815, 36315, 36327, 36535, 36567, 36598, 36838,
    39922, 40436, 40882, 40916, 41917, 41947, 42958, 43837, 44158, 44263,
    44347, 44743, 45531, 45543, 45727, 45783, 45790, 46042, 46556, 46990,
    47060, 47230, 47323, 47407, 47827, 48341, 48411, 48423, 48430, 48442,
    48476, 48500, 48523, 48547, 48581, 48593, 48600, 48612, 48663, 48852,
    50621, 50651, 51118, 51838, 51943, 52061, 52571, 52903, 53693, 53735,
    54202, 54431, 54455, 54462, 54716, 55182, 55218, 55422, 55485, 55631,
    55987, 56093, 56122, 56135, 56142, 56156, 56178, 56205, 56227, 56241,
    56248, 56261, 56290, 56501, 56855, 57010, 57982, 58075, 58229, 58494,
    58557, 58739, 59023, 59182, 59189, 59214, 59219, 59250, 59252, 59275,
    59277, 59308, 59313, 59338, 59345, 59503, 59515, 59517, 60028, 60237,
    60273, 60538, 60715, 60785, 61799, 62107, 62621, 62999, 63118, 63598,
    63787, 63821
  ]
  | 4 => [
    8184, 12276, 14316, 15324, 15804, 15996, 20466, 22506, 23514, 23994,
    24186, 26598, 28278, 29646, 30126, 30318, 31326, 31806, 36849, 39897,
    40377, 42981, 43989, 44469, 44661, 46029, 46509, 47517, 47709, 48189,
    51171, 52179, 52659, 52851, 54219, 54699, 55707, 55899, 56379, 58311,
    58791, 58983, 59991, 60471, 61839, 62031, 62511, 63519
  ]
  | _ => [
    6014, 11197, 19931, 29159, 32279, 32488, 36583, 45787, 48427, 48596,
    54461, 56141, 56242, 59249, 59278, 59518
  ]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 120000000 in
-- The kernel enumerates all 384 actions on each representative and sorts the results.
private theorem orbitTable_checked (r : Fin 6) :
    orbitTable r = (orbitMasks r).eraseDups.insertionSort (· ≤ ·) := by
  apply beq_iff_eq.mp
  fin_cases r <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 120000000 in
-- The kernel evaluates the eligibility predicate on all 65,536 masks.
-- Equality of lists also checks disjointness, since each range has no duplicates.
private theorem masks_checked (block : Fin 64) :
    ((List.range' (1024 * block.val) 1024).filter eligible) =
      (((List.finRange 6).flatMap orbitTable).filter fun mask =>
        decide (1024 * block.val ≤ mask ∧ mask < 1024 * block.val + 1024)).insertionSort
          (· ≤ ·) := by
  apply beq_iff_eq.mp
  fin_cases block <;> decide +kernel

private theorem mask_covered {mask : Nat} (hbound : mask < 65536)
    (heligible : eligible mask = true) : ∃ r : Fin 6, mask ∈ orbitMasks r := by
  let block : Fin 64 := ⟨mask / 1024, by omega⟩
  have hmem : mask ∈ List.range' (1024 * block.val) 1024 := by
    apply List.mem_range'_1.mpr
    change 1024 * (mask / 1024) ≤ mask ∧ mask < 1024 * (mask / 1024) + 1024
    omega
  have hfiltered := List.mem_filter.mpr ⟨hmem, heligible⟩
  rw [masks_checked block] at hfiltered
  have htable := (List.mem_filter.mp ((List.mem_insertionSort (· ≤ ·)).mp hfiltered)).1
  obtain ⟨r, _, hr⟩ := List.mem_flatMap.mp htable
  rw [orbitTable_checked] at hr
  exact ⟨r, List.mem_eraseDups.mp ((List.mem_insertionSort (· ≤ ·)).mp hr)⟩

/-- A ten-point projection with minimum degree two and antipodal distinct
parallel complement edges is a translate of a coordinate permutation of
one of the six representatives. Complement edges are indexed by their false endpoints. -/
theorem ten_projection_orbit (P : Finset (BitVec 4))
    (hsize : P.card = 10)
    (hanti : ∀ (i : Fin 4) (x y : BitVec 4),
      x.getLsbD i.val = false → y.getLsbD i.val = false →
      x ∉ P → flipBit x i ∉ P → y ∉ P → flipBit y i ∉ P →
      x ≠ y → y = flipBit (x ^^^ 15) i)
    (hmin : ∀ x ∈ P, 2 ≤ (neighborDirections P x).card) :
    ∃ (r : Fin 6) (t : BitVec 4) (σ : Equiv.Perm (Fin 4)),
      P = (representative r).image (fun x => permute σ x ^^^ t) := by
  let mask := encode P
  have hdecode : envelope mask = P := envelope_encode P
  have hcard : size mask = P.card := (envelope_card mask).symm.trans (congrArg Finset.card hdecode)
  have hbound : mask < 65536 := by
    unfold mask encode
    exact BitVec.isLt _
  have heligible : eligible mask = true := by
    refine Bool.and_eq_true_iff.mpr ⟨by simp [hcard, hsize], Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
    · exact antipodesOK_of mask (by simpa only [hdecode] using hanti)
    · exact minDegreesOK_of mask (by simpa only [hdecode] using hmin)
  obtain ⟨r, hr⟩ := mask_covered hbound heligible
  obtain ⟨σ, _, hσ⟩ := List.mem_flatMap.mp hr
  obtain ⟨t, _, ht⟩ := List.mem_map.mp hσ
  exact ⟨r, t, σ, hdecode.symm.trans ((congrArg envelope ht).symm.trans (envelope_encode _))⟩

#print axioms ten_projection_orbit

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q4TenProjectionOrbits
