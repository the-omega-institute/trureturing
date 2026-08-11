/- GID: D5/S1/Words/ReturnWords/GoldenRankArcs
   generality: I
   mirror-B: none(waiver:formal-interface-precedes-first-return-dichotomy)
   mirror-E: none(waiver:kernel-symbolic-golden-rank-interface)
   anchors: []
   digest: Golden cylinder ranks are exactly the sorted irrational-rotation gap arcs. -/

import D5.S1.Words.ReturnWords.GoldenOccurrenceGaps
import D5.S1.Words.ReturnWords.RotationGapArcs

namespace D5.S1.Words

open Set

/-- The public endpoint used by the length-`n` golden cylinder partition. -/
noncomputable def goldenCylinderEndpoint (m : Nat) : Real :=
  1 - Int.fract (((m + 1 : Nat) : Real) * goldenMechanicalSlope)

/-- The public finite set of length-`n` golden cylinder endpoints. -/
noncomputable def goldenCylinderEndpointSet (n : Nat) : Finset Real :=
  (Finset.range n).image goldenCylinderEndpoint

private theorem golden_cylinder_rank_public (n i : Nat) :
    goldenCylinderRank n i =
      ((goldenCylinderEndpointSet n).filter fun x => x ≤ goldenPhase i).card := by
  rfl

/-- The golden mechanical slope is irrational. -/
theorem golden_mechanical_slope_irrational : Irrational goldenMechanicalSlope :=
  Real.goldenRatio_irrational.inv

instance goldenMechanicalSlopeIrrationalFact :
    Fact (Irrational goldenMechanicalSlope) :=
  ⟨golden_mechanical_slope_irrational⟩

private theorem golden_phase_mem_Ico (i : Nat) :
    goldenPhase i ∈ Ico (0 : Real) 1 := by
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

private theorem golden_endpoint_fract_ne_zero (m : Nat) :
    Int.fract (((m + 1 : Nat) : Real) * goldenMechanicalSlope) ≠ 0 := by
  rw [Int.fract_ne_zero_iff]
  rintro ⟨z, hz⟩
  have hi : Irrational (((m + 1 : Nat) : Real) * goldenMechanicalSlope) :=
    golden_mechanical_slope_irrational.natCast_mul (Nat.succ_ne_zero m)
  exact hi.ne_int z hz.symm

private theorem golden_endpoint_mem_Ioo (m : Nat) :
    goldenCylinderEndpoint m ∈ Ioo (0 : Real) 1 := by
  have hnonneg := Int.fract_nonneg
    (((m + 1 : Nat) : Real) * goldenMechanicalSlope)
  have hlt := Int.fract_lt_one
    (((m + 1 : Nat) : Real) * goldenMechanicalSlope)
  have hne := golden_endpoint_fract_ne_zero m
  have hpos : 0 < Int.fract (((m + 1 : Nat) : Real) * goldenMechanicalSlope) :=
    lt_of_le_of_ne hnonneg (Ne.symm hne)
  simp only [goldenCylinderEndpoint, mem_Ioo]
  constructor <;> linarith

private theorem golden_endpoint_eq_negative_rotation (m : Nat) :
    goldenCylinderEndpoint m =
      Int.fract (((m + 1 : Nat) : Real) * (-goldenMechanicalSlope)) := by
  calc
    goldenCylinderEndpoint m =
        1 - Int.fract (((m + 1 : Nat) : Real) * goldenMechanicalSlope) := rfl
    _ = Int.fract (-(((m + 1 : Nat) : Real) * goldenMechanicalSlope)) :=
      (Int.fract_neg (golden_endpoint_fract_ne_zero m)).symm
    _ = Int.fract (((m + 1 : Nat) : Real) * (-goldenMechanicalSlope)) := by
      congr 1
      ring

/-- Golden cylinder endpoints are exactly the non-boundary negative rotation cuts. -/
theorem golden_cylinder_endpoint_set_eq_rotation_interior_cut_set (n : Nat) :
    goldenCylinderEndpointSet n =
      rotationInteriorCutSet goldenMechanicalSlope (n + 1) := by
  ext x
  constructor
  · intro hx
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
    have hm_lt : m < n := Finset.mem_range.mp hm
    have hinside := golden_endpoint_mem_Ioo m
    rw [rotationInteriorCutSet]
    simp only [Finset.mem_erase]
    refine ⟨hinside.2.ne, hinside.1.ne', ?_⟩
    rw [rotationCutSet, Finset.mem_insert]
    right
    rw [D5.S1.Recurrence.RotationOrbitGapsPartition.rotationOrbit, Finset.mem_image]
    refine ⟨m + 1, Finset.mem_range.mpr ?_, ?_⟩
    · omega
    · exact (golden_endpoint_eq_negative_rotation m).symm
  · intro hx
    rw [rotationInteriorCutSet] at hx
    simp only [Finset.mem_erase] at hx
    obtain ⟨hxone, hxzero, hxcut⟩ := hx
    rw [rotationCutSet, Finset.mem_insert] at hxcut
    rcases hxcut with rfl | hxorbit
    · exact (hxone rfl).elim
    · rw [D5.S1.Recurrence.RotationOrbitGapsPartition.rotationOrbit,
        Finset.mem_image] at hxorbit
      obtain ⟨k, hk, rfl⟩ := hxorbit
      have hk_lt : k < n + 1 := Finset.mem_range.mp hk
      have hkzero : k ≠ 0 := by
        intro hkzero
        subst k
        simp at hxzero
      let m := k - 1
      have hm : m < n := by
        dsimp [m]
        omega
      refine Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr hm, ?_⟩
      rw [golden_endpoint_eq_negative_rotation]
      rw [show m + 1 = k by dsimp [m]; omega]

/-- A golden cylinder rank is exactly membership in the equally numbered rotation gap arc. -/
theorem golden_cylinder_rank_iff_mem_rotation_gap_arc
    (n i : Nat) (r : Fin (n + 1)) :
    goldenCylinderRank n i = r.val ↔
      goldenPhase i ∈ rotationGapArc goldenMechanicalSlope (n + 1) r := by
  rw [golden_cylinder_rank_public,
    golden_cylinder_endpoint_set_eq_rotation_interior_cut_set]
  exact rotation_gap_rank_iff_mem_rotation_gap_arc goldenMechanicalSlope (n + 1)
    (golden_phase_mem_Ico i) r

private def rotationGapBoundaryIndexReadout (N : Nat) : List (Nat × Nat) :=
  List.ofFn fun r : Fin N => (r.castSucc.val, r.succ.val)

-- Length two has three cylinders, with the frozen half-open boundary convention.
private theorem golden_rank_arcs_two_boundary_index_readout :
    rotationGapBoundaryIndexReadout (2 + 1) = [(0, 1), (1, 2), (2, 3)] := by
  decide

#print axioms golden_mechanical_slope_irrational
#print axioms golden_cylinder_endpoint_set_eq_rotation_interior_cut_set
#print axioms golden_cylinder_rank_iff_mem_rotation_gap_arc

end D5.S1.Words
