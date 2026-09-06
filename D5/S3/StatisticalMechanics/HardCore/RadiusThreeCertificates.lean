/- GID: D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates
   generality: S
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates
   mirror-E: none(waiver:kernel-replayed-finite-certificate)
   anchors: []
   digest: Geometric radius-three coverage, adaptive growth bounds and an all-controller floor. -/

import D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory
import D5.S3.StatisticalMechanics.HardCore.RadiusThreeData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace D5.S3.StatisticalMechanics.HardCore.RadiusThreeCertificates

open scoped BigOperators
open D5.S3.StatisticalMechanics.HardCore.BranchingPotential
open D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory
open D5.S3.StatisticalMechanics.HardCore.RadiusThreeData

private def row (i : Fin 483) : ℕ × ℕ × ℕ × ℕ × ℕ := radiusThreeRows[i.val]!

private def pointList : List Point := [
  (-3,0), (-2,-1), (-2,0), (-2,1), (-1,-2), (-1,-1), (-1,0), (-1,1),
  (-1,2), (0,-3), (0,-2), (0,-1), (0,1), (0,2), (0,3), (1,-2),
  (1,-1), (1,0), (1,1), (1,2), (2,-1), (2,0), (2,1), (3,0), (0,0)]

private def point (k : Fin 25) : Point := pointList[k.val]!

private def encode (F : Finset Point) : ℕ :=
  ∑ k : Fin 25, if point k ∈ F then 2 ^ k.val else 0

/-- The actual geometric blocked set represented by a state. -/
def radiusThreeMask (i : Fin 483) : Finset Point :=
  (Finset.univ.filter fun k : Fin 25 => (row i).1.testBit k.val).image point

private def lookup (code : ℕ) : Option (Fin 483) :=
  let k := radiusThreeRows.findIdx (fun r => r.1 == code)
  if hk : k < 483 then some ⟨k, hk⟩ else none

/-- Transitions are computed from the geometric update, not a supplied edge
list. The closure certificate below excludes failure of the lookup. -/
def radiusThreeStep (i : Fin 483) (a : Fin 6) (d : Fin 3) : Option (Fin 483) :=
  if direction d ∈ radiusThreeMask i then none
  else lookup (encode (memoryStep 3 (radiusThreeMask i) a d))

/-- Nonnegative sub-potential valid for all six orderings, including dead states. -/
def radiusThreeLower (i : Fin 483) : ℕ := (row i).2.1

/-- Strictly positive super-potential for the selected stationary controller. -/
def radiusThreeUpper (i : Fin 483) : ℕ := (row i).2.2.1

/-- Sub-potential for fixed straight-right-left ordering. -/
def radiusThreeFixedLower (i : Fin 483) : ℕ := (row i).2.2.2.1

/-- A concrete mask-dependent ordering. Range validity is independently checked
below; modulo merely makes the data accessor total. -/
def radiusThreeChoice (i : Fin 483) : Fin 6 :=
  ⟨(row i).2.2.2.2 % 6, Nat.mod_lt _ (by decide)⟩

/-- Full geometric closure, not bounded-depth sampling. Every unblocked move
has a represented successor with exactly the required truncated blocked set. -/
theorem radiusThree_geometry :
    radiusThreeRows.length = 483 ∧
    (radiusThreeRows.map fun r => r.1).Nodup ∧
    radiusThreeMask 0 = {(-1, 0)} ∧
    (∀ i : Fin 483, (row i).2.2.2.2 < 6 ∧
      (-1, 0) ∈ radiusThreeMask i ∧ (0, 0) ∉ radiusThreeMask i) ∧
    (∀ (i : Fin 483) (a : Fin 6) (d : Fin 3),
      match radiusThreeStep i a d with
      | none => direction d ∈ radiusThreeMask i
      | some j => direction d ∉ radiusThreeMask i ∧
          radiusThreeMask j = memoryStep 3 (radiusThreeMask i) a d) := by
  decide +kernel

/-- Exact integer row certificates. The all-order lower row is essential:
it rules out every history-dependent ordering on this memory model. -/
theorem radiusThree_potentials :
    (∀ i : Fin 483, radiusThreeLower i ≤ 1000000000 ∧
      1 ≤ radiusThreeUpper i ∧ radiusThreeFixedLower i ≤ 1000000000) ∧
    (∀ (i : Fin 483) (a : Fin 6),
      5041 * radiusThreeLower i ≤
        2000 * childWeight radiusThreeStep radiusThreeLower i a) ∧
    (∀ i : Fin 483,
      5000 * childWeight radiusThreeStep radiusThreeUpper i (radiusThreeChoice i) ≤
        12603 * radiusThreeUpper i) ∧
    (∀ i : Fin 483,
      25209 * radiusThreeFixedLower i ≤
        10000 * childWeight radiusThreeStep radiusThreeFixedLower i 0) ∧
    radiusThreeLower 0 = 1000000000 ∧
    radiusThreeUpper 0 = 1000000000 ∧
    radiusThreeFixedLower 0 = 1000000000 := by
  decide +kernel

private theorem rejected_iff (i : Fin 483) (a : Fin 6) (d : Fin 3) :
    radiusThreeStep i a d = none ↔ direction d ∈ radiusThreeMask i := by
  constructor
  · intro h
    have hg := radiusThree_geometry.2.2.2.2 i a d
    simpa [h] using hg
  · intro h
    simp [radiusThreeStep, h]

private theorem successor_mask (i : Fin 483) (a : Fin 6) (d : Fin 3)
    (j : Fin 483) (h : radiusThreeStep i a d = some j) :
    radiusThreeMask j = memoryStep 3 (radiusThreeMask i) a d := by
  have hg := radiusThree_geometry.2.2.2.2 i a d
  rw [h] at hg
  exact hg.2

/-- One explicit policy has branching rate at most 12603/5000, in the
all-depth integer sense displayed. The prefactor is explicit and root independent. -/
theorem radiusThree_adaptive_upper (n : ℕ) (history : List (Fin 3)) (i : Fin 483) :
    5000 ^ n * pathCount radiusThreeStep (fun _ j => radiusThreeChoice j) n history i ≤
      12603 ^ n * radiusThreeUpper i := by
  exact upper_of_superpotential radiusThreeStep (fun _ j => radiusThreeChoice j)
    radiusThreeUpper 12603 5000 (fun j => (radiusThree_potentials.1 j).2.1)
    (fun _ j => radiusThree_potentials.2.2.1 j) n history i

/-- Every controller, including arbitrary history-dependent choices, has at
least (5041/2000)^n descendants from the initial parent-blocked mask. -/
theorem radiusThree_all_controllers_lower
    (policy : List (Fin 3) → Fin 483 → Fin 6) (n : ℕ) :
    5041 ^ n ≤ 2000 ^ n * pathCount radiusThreeStep policy n [] 0 := by
  have h := lower_of_subpotential radiusThreeStep policy radiusThreeLower
    5041 2000 1000000000 (fun j => (radiusThree_potentials.1 j).1)
    (fun _ j => radiusThree_potentials.2.1 j _) n [] 0
  rw [radiusThree_potentials.2.2.2.2.1] at h
  nlinarith

/-- Fixed SRL ordering has a larger certified lower growth rate. This is a
lower bound for the relaxed memory tree, not for the actual grid Weitz tree. -/
theorem radiusThree_fixed_order_lower (n : ℕ) :
    25209 ^ n ≤ 10000 ^ n * pathCount radiusThreeStep (fun _ _ => 0) n [] 0 := by
  have h := lower_of_subpotential radiusThreeStep (fun _ _ => 0) radiusThreeFixedLower
    25209 10000 1000000000 (fun j => (radiusThree_potentials.1 j).2.2)
    (fun _ j => radiusThree_potentials.2.2.2.1 j) n [] 0
  rw [radiusThree_potentials.2.2.2.2.2.2] at h
  nlinarith

/-- A real finite grid-domain consumer. No path is removed merely because the
table rejects it: full geometry establishes that rejected children are absent.
No partition-function identity or complex zero-free conclusion is asserted. -/
theorem radiusThree_finite_domain_upper (n : ℕ) (V : Finset Point)
    (hparent : (-1, 0) ∉ V) :
    5000 ^ n * orderedCount radiusThreeStep radiusThreeChoice 0 n V 0 ≤
      1000000000 * 12603 ^ n := by
  have hd : Disjoint V (radiusThreeMask 0) := by
    rw [radiusThree_geometry.2.2.1]
    simpa using hparent
  have hs := orderedCount_le_pathCount radiusThreeStep radiusThreeChoice 0
    radiusThreeMask 3 rejected_iff successor_mask n V 0 [] hd
  have hu := radiusThree_adaptive_upper n [] 0
  rw [radiusThree_potentials.2.2.2.2.2.1] at hu
  calc
    _ ≤ 5000 ^ n * pathCount radiusThreeStep
          (fun _ j => radiusThreeChoice j) n [] 0 := Nat.mul_le_mul_left _ hs
    _ ≤ 12603 ^ n * 1000000000 := hu
    _ = _ := by ring

#print axioms radiusThree_geometry
#print axioms radiusThree_potentials
#print axioms radiusThree_adaptive_upper
#print axioms radiusThree_all_controllers_lower
#print axioms radiusThree_fixed_order_lower
#print axioms radiusThree_finite_domain_upper

end D5.S3.StatisticalMechanics.HardCore.RadiusThreeCertificates
