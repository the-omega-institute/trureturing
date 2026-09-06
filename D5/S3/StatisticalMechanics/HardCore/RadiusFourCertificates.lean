/- GID: D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates
   generality: S
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/RadiusFourCertificates
   mirror-E: none(waiver:kernel-replayed-geometric-certificate)
   anchors: []
   digest: A concrete radius-four geometric certificate bounds all finite-domain counts. -/

import D5.S3.StatisticalMechanics.HardCore.MemoryRefinement
import D5.S3.StatisticalMechanics.HardCore.RadiusFourData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace D5.S3.StatisticalMechanics.HardCore.RadiusFourCertificates

open scoped BigOperators
open D5.S3.StatisticalMechanics.HardCore.BranchingPotential
open D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory
open D5.S3.StatisticalMechanics.HardCore.MemoryRefinement
open D5.S3.StatisticalMechanics.HardCore.RadiusFourData

private def row (i : Fin 851) : ℕ × ℕ := radiusFourRows[i.val]!

private def pointList : List Point := [
  (-4,0), (-3,-1), (-3,0), (-3,1), (-2,-2), (-2,-1), (-2,0), (-2,1),
  (-2,2), (-1,-3), (-1,-2), (-1,-1), (-1,0), (-1,1), (-1,2), (-1,3),
  (0,-4), (0,-3), (0,-2), (0,-1), (0,1), (0,2), (0,3), (0,4),
  (1,-3), (1,-2), (1,-1), (1,0), (1,1), (1,2), (1,3), (2,-2),
  (2,-1), (2,0), (2,1), (2,2), (3,-1), (3,0), (3,1), (4,0), (0,0)]

private def point (k : Fin 41) : Point := pointList[k.val]!

private def encode (F : Finset Point) : ℕ :=
  ∑ k : Fin 41, if point k ∈ F then 2 ^ k.val else 0

/-- Decode the actual geometric blocked set of a represented state. -/
def radiusFourMask (i : Fin 851) : Finset Point :=
  (Finset.univ.filter fun k : Fin 41 => (row i).1.testBit k.val).image point

private def lookup (code : ℕ) : Option (Fin 851) :=
  let k := radiusFourRows.findIdx (fun r => r.1 == code)
  if hk : k < 851 then some ⟨k, hk⟩ else none

/-- Compute fixed-SRL geometric successors. Only action zero is implemented;
other actions return none and carry no geometric coverage claim. The finite
certificate proves exact closure of every selected SRL direction. -/
def radiusFourStep (i : Fin 851) (a : Fin 6) (d : Fin 3) : Option (Fin 851) :=
  if a ≠ 0 then none
  else if direction d ∈ radiusFourMask i then none
  else lookup (encode (memoryStep 4 (radiusFourMask i) 0 d))

/-- Positive integer super-potential for the complete fixed-SRL closure. -/
def radiusFourWeight (i : Fin 851) : ℕ := (row i).2

/-- Complete direction-preserving geometric semantics of the finite table.
This is a fixed-policy closure, not a claim covering unused orderings. -/
theorem radiusFour_geometry :
    radiusFourRows.length = 851 ∧
    (radiusFourRows.map fun r => r.1).Nodup ∧
    radiusFourMask 0 = {(-1, 0)} ∧
    (∀ i : Fin 851, (-1, 0) ∈ radiusFourMask i ∧ (0, 0) ∉ radiusFourMask i) ∧
    (∀ (i : Fin 851) (d : Fin 3),
      (radiusFourStep i 0 d).map radiusFourMask = geometricStep 4 (radiusFourMask i) 0 d) := by
  decide +kernel

/-- Every row is checked with integers. The root weight and a uniform weight
cap are exactly twenty thousand. Equality in some rows is permitted. -/
theorem radiusFour_potential :
    (∀ i : Fin 851, 1 ≤ radiusFourWeight i ∧ radiusFourWeight i ≤ 20000) ∧
    (∀ i : Fin 851,
      10000 * childWeight radiusFourStep radiusFourWeight i 0 ≤
        24827 * radiusFourWeight i) ∧
    radiusFourWeight 0 = 20000 := by
  decide +kernel

/-- The actual represented branching system has the stated all-depth bound. -/
theorem radiusFour_table_upper (n : ℕ) (h : List (Fin 3)) (i : Fin 851) :
    10000 ^ n * pathCount radiusFourStep (fun _ _ => 0) n h i ≤
      24827 ^ n * radiusFourWeight i := by
  exact upper_of_superpotential radiusFourStep (fun _ _ => 0) radiusFourWeight
    24827 10000 (fun j => (radiusFour_potential.1 j).1)
    (fun _ j => radiusFour_potential.2.1 j) n h i

/-- The bound is transported to the raw geometric process, without a supplied
path-count equality or a claimed spectral radius for an unrelated matrix. -/
theorem radiusFour_geometric_upper (n : ℕ) (h : List (Fin 3)) :
    10000 ^ n * pathCount (geometricStep 4) (fun _ _ => 0) n h {(-1, 0)} ≤
      20000 * 24827 ^ n := by
  have he := fixed_presentation_count radiusFourStep radiusFourMask 4 0
    radiusFour_geometry.2.2.2.2 n h 0
  rw [radiusFour_geometry.2.2.1] at he
  rw [← he]
  have hu := radiusFour_table_upper n h 0
  rw [radiusFour_potential.2.2] at hu
  simpa [Nat.mul_comm] using hu

/-- Every actual finite vertex domain with its parent removed satisfies the
same bound. Availability is decided by V, and the counter uses raw geometry,
so a missing table entry cannot suppress a genuine child by definition. -/
theorem radiusFour_finite_domain_upper (n : ℕ) (V : Finset Point)
    (hparent : (-1, 0) ∉ V) :
    10000 ^ n * orderedCount (geometricStep 4) (fun _ => 0) ∅ n V {(-1, 0)} ≤
      20000 * 24827 ^ n := by
  have hb : ∀ (F : Finset Point) (a : Fin 6) (d : Fin 3),
      geometricStep 4 F a d = none ↔ direction d ∈ F := by
    intro F a d
    by_cases hd : direction d ∈ F <;> simp [geometricStep, hd]
  have hn : ∀ (F : Finset Point) (a : Fin 6) (d : Fin 3) (G : Finset Point),
      geometricStep 4 F a d = some G → G = memoryStep 4 F a d := by
    intro F a d G hs
    unfold geometricStep at hs
    split_ifs at hs with hd
    · simp at hs
    · exact (Option.some.inj hs).symm
  have hd : Disjoint V ({(-1, 0)} : Finset Point) := by
    apply Finset.disjoint_left.mpr
    intro p hpV hp
    have he := Finset.mem_singleton.mp hp
    subst p
    exact hparent hpV
  have hc := orderedCount_le_pathCount (geometricStep 4) (fun _ => 0) ∅
    (fun F => F) 4 hb hn n V {(-1, 0)} [] hd
  exact (Nat.mul_le_mul_left (10000 ^ n) hc).trans (radiusFour_geometric_upper n [])

#print axioms radiusFour_geometry
#print axioms radiusFour_potential
#print axioms radiusFour_table_upper
#print axioms radiusFour_geometric_upper
#print axioms radiusFour_finite_domain_upper

end D5.S3.StatisticalMechanics.HardCore.RadiusFourCertificates
