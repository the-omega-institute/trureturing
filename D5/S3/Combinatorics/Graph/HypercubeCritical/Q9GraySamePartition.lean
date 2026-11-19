import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9GrayEasyPlacements
import D5.S3.Combinatorics.Graph.HypercubeCritical.GrayOmissionCounting

/-! An integer omission certificate for the same-partition Gray pair. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Q9GraySamePartition

open Finset
open Q9GrayCrossedPlacement (cube)
open GrayOmissionCounting (Row demand coefficient Valid weighted_omissions)

private instance : Fintype (BitVec 9) :=
  Fintype.ofEquiv (Fin (2 ^ 9)) (BitVec.equivFin (m := 9)).toEquiv.symm

private def regionMask : Nat :=
  (0xffffffffffffffff971717e817e8e8e9971717e817e8e8e90100000000000080 <<< 256) |||
    0x971717e817e8e8e90100000000000080010000000000008097010180018080e9

private def region : Finset (BitVec 9) :=
  univ.filter fun x => regionMask.testBit x.toNat = true

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
-- Verify the packed representation once before checking all the local rows.
private theorem region_eq_residual : region = Q9GrayEasyPlacements.residual 0 63 := by
  decide +kernel

private def certificate : List (Row (BitVec 9) × ℕ) :=
  [
    (.degree 7, 479),
    (.degree 56, 479),
    (.degree 195, 1006),
    (.degree 197, 635),
    (.degree 198, 1058),
    (.degree 199, 19),
    (.degree 216, 151),
    (.degree 231, 60),
    (.degree 232, 151),
    (.degree 240, 797),
    (.degree 248, 180),
    (.degree 249, 31),
    (.degree 250, 665),
    (.degree 323, 370),
    (.degree 326, 422),
    (.degree 327, 19),
    (.degree 335, 635),
    (.degree 343, 635),
    (.degree 359, 696),
    (.degree 368, 646),
    (.degree 376, 180),
    (.degree 377, 182),
    (.degree 378, 817),
    (.degree 380, 151),
    (.degree 387, 370),
    (.degree 390, 422),
    (.degree 391, 19),
    (.degree 399, 635),
    (.degree 407, 635),
    (.degree 408, 90),
    (.degree 423, 696),
    (.degree 424, 90),
    (.degree 432, 737),
    (.degree 440, 180),
    (.degree 441, 92),
    (.degree 442, 726),
    (.degree 444, 60),
    (.degree 448, 326),
    (.degree 449, 515),
    (.degree 452, 327),
    (.star 453 {197, 325, 449, 455}, 1007),
    (.degree 459, 201),
    (.star 459 {203, 331, 395, 458}, 1671),
    (.degree 461, 127),
    (.star 461 {205, 333, 397, 460}, 420),
    (.star 461 {205, 333, 397, 493}, 1696),
    (.degree 462, 211),
    (.star 462 {206, 334, 398, 458}, 468),
    (.star 462 {206, 334, 398, 460}, 243),
    (.star 462 {206, 334, 398, 478}, 897),
    (.star 463 {207, 335, 399, 455}, 217),
    (.degree 464, 72),
    (.degree 467, 201),
    (.star 467 {211, 339, 403, 466}, 1337),
    (.star 467 {211, 339, 403, 475}, 334),
    (.degree 469, 127),
    (.star 469 {213, 341, 405, 465}, 1760),
    (.star 469 {213, 341, 405, 468}, 356),
    (.degree 470, 211),
    (.star 470 {214, 342, 406, 466}, 15),
    (.star 470 {214, 342, 406, 468}, 1594),
    (.star 471 {343, 407, 479, 503}, 1067),
    (.star 472 {216, 456, 464, 504}, 152),
    (.star 472 {344, 408, 464, 504}, 2182),
    (.degree 473, 36),
    (.star 473 {217, 345, 409, 457}, 717),
    (.star 473 {217, 345, 409, 475}, 1943),
    (.degree 474, 163),
    (.star 474 {218, 346, 410, 466}, 584),
    (.star 474 {218, 346, 410, 478}, 1314),
    (.degree 476, 30),
    (.star 476 {220, 348, 412, 460}, 139),
    (.star 476 {220, 348, 412, 477}, 2558),
    (.degree 480, 6),
    (.degree 483, 213),
    (.star 483 {227, 355, 419, 481}, 1519),
    (.star 483 {227, 355, 419, 482}, 80),
    (.degree 485, 139),
    (.star 485 {229, 357, 421, 481}, 51),
    (.star 485 {229, 357, 421, 484}, 1992),
    (.degree 486, 223),
    (.star 486 {230, 358, 422, 502}, 1536),
    (.star 488 {232, 360, 456, 480}, 2397),
    (.star 488 {360, 424, 456, 504}, 3),
    (.degree 489, 36),
    (.star 489 {233, 361, 425, 457}, 1245),
    (.star 489 {233, 361, 425, 491}, 1415),
    (.degree 490, 163),
    (.star 490 {234, 362, 426, 482}, 1899),
    (.degree 492, 30),
    (.star 492 {236, 364, 428, 460}, 1348),
    (.star 492 {236, 364, 428, 494}, 1349),
    (.degree 495, 850),
    (.degree 497, 165),
    (.star 497 {241, 369, 433, 481}, 231),
    (.star 497 {241, 369, 433, 499}, 883),
    (.star 497 {241, 369, 433, 501}, 769),
    (.degree 498, 292),
    (.star 498 {242, 370, 434, 499}, 1123),
    (.degree 500, 159),
    (.star 500 {244, 372, 436, 501}, 1518),
    (.star 500 {244, 372, 436, 502}, 404),
    (.star 505 {249, 377, 441, 509}, 2333),
    (.star 508 {252, 380, 444, 510}, 2397),
    (.degree 510, 50),
    (.degree 511, 329)
  ]

private def row (i : Fin certificate.length) : Row (BitVec 9) := (certificate.get i).1

private def weight (i : Fin certificate.length) : ℕ := (certificate.get i).2

set_option maxRecDepth 4096 in
set_option maxHeartbeats 16000000 in
-- Check the region size, the local star and degree rows, and their integer loads.
private theorem checked :
    region.card = 188 ∧ (∀ i, Valid cube region (row i)) ∧
    (∀ x ∈ region, (∑ i, weight i * coefficient cube region (row i) x) ≤ 2880) ∧
    2880 * 38 < (∑ i, weight i * demand cube region (row i)) := by
  decide +kernel

/-- The residual region of the same-partition pair admits at most 149
selected vertices of induced maximum degree three. -/
theorem residual_card_le (S : Finset (BitVec 9))
    (hS : S ⊆ Q9GrayEasyPlacements.residual 0 63)
    (hdeg : ∀ v ∈ S, (S.filter (cube.Adj v)).card ≤ 3) : S.card ≤ 149 := by
  obtain ⟨hcard, hrows, hload, hbound⟩ := checked
  have hsub : S ⊆ region := by simpa only [region_eq_residual] using hS
  have h := hbound.trans_le (weighted_omissions cube region S hsub hdeg row weight 2880 hrows hload)
  rw [hcard] at h
  omega

#print axioms residual_card_le

end D5.S3.Combinatorics.Graph.HypercubeCritical.Q9GraySamePartition
