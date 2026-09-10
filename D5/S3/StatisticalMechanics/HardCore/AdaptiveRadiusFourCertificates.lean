/- GID: D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates
   generality: S
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates
   mirror-E: none(waiver:kernel-replayed-geometric-certificate)
   anchors: []
   digest: Certify a radius-four controller with uniform all-domain growth at most 2.4808. -/

import D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory
import D5.S3.StatisticalMechanics.HardCore.AdaptiveRadiusFourData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace D5.S3.StatisticalMechanics.HardCore.AdaptiveRadiusFourCertificates

open scoped BigOperators
open D5.S3.StatisticalMechanics.HardCore.BranchingPotential
open D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory
open D5.S3.StatisticalMechanics.HardCore.AdaptiveRadiusFourData

private def row (i : Fin 881) : ℕ × ℕ × ℕ := radiusFourRows[i.val]!

private def pointList : List Point := [
  (-4,0), (-3,-1), (-3,0), (-3,1), (-2,-2), (-2,-1), (-2,0), (-2,1), (-2,2),
  (-1,-3), (-1,-2), (-1,-1), (-1,0), (-1,1), (-1,2), (-1,3),
  (0,-4), (0,-3), (0,-2), (0,-1), (0,0), (0,1), (0,2), (0,3), (0,4),
  (1,-3), (1,-2), (1,-1), (1,0), (1,1), (1,2), (1,3),
  (2,-2), (2,-1), (2,0), (2,1), (2,2), (3,-1), (3,0), (3,1), (4,0)]

private def point (k : Fin 41) : Point := pointList[k.val]!

/-- Actual blocked grid vertices, not an arbitrary finite-state label. -/
def radiusFourMask (i : Fin 881) : Finset Point :=
  (Finset.univ.filter fun k : Fin 41 => (row i).1.testBit k.val).image point

/-- An explicit local order for each represented mask. -/
def radiusFourChoice (i : Fin 881) : Fin 6 :=
  ⟨(row i).2.2 % 6, Nat.mod_lt _ (by decide)⟩

private def encode (F : Finset Point) : ℕ :=
  ∑ k : Fin 41, if point k ∈ F then 2 ^ k.val else 0

private def lookup (code : ℕ) : Option (Fin 881) :=
  let k := radiusFourRows.findIdx (fun r => r.1 == code)
  if hk : k < 881 then some ⟨k, hk⟩ else none

/-- Compute the selected controller's successor from actual grid geometry.
The unused action argument matches the shared counting interface. Only the
selected action is claimed; the finite closure theorem excludes lookup failure. -/
def radiusFourStep (i : Fin 881) (_a : Fin 6) (d : Fin 3) : Option (Fin 881) :=
  if direction d ∈ radiusFourMask i then none
  else lookup (encode (memoryStep 4 (radiusFourMask i) (radiusFourChoice i) d))

/-- Positive integer upper potential. All values are at most one hundred thousand. -/
def radiusFourWeight (i : Fin 881) : ℕ := (row i).2.1

private instance geometry_step_decidable (i : Fin 881) (d : Fin 3) :
    Decidable (match radiusFourStep i (radiusFourChoice i) d with
    | none => direction d ∈ radiusFourMask i
    | some j => direction d ∉ radiusFourMask i ∧
        radiusFourMask j = memoryStep 4 (radiusFourMask i) (radiusFourChoice i) d) := by
  cases radiusFourStep i (radiusFourChoice i) d <;> infer_instance

/-- Complete selected-controller closure on the actual geometry. The finite
lookup is not allowed to omit an unblocked geometric successor. -/
theorem radiusFour_geometry :
    radiusFourRows.length = 881 ∧
    (radiusFourRows.map fun r => r.1).Nodup ∧
    radiusFourMask 0 = {(-1, 0)} ∧
    (∀ i : Fin 881, (row i).1 < 2199023255552 ∧ (row i).2.2 < 6 ∧ (-1, 0) ∈ radiusFourMask i ∧
      (0, 0) ∉ radiusFourMask i) ∧
    (∀ (i : Fin 881) (d : Fin 3),
      match radiusFourStep i (radiusFourChoice i) d with
      | none => direction d ∈ radiusFourMask i
      | some j => direction d ∉ radiusFourMask i ∧
          radiusFourMask j = memoryStep 4 (radiusFourMask i) (radiusFourChoice i) d) := by
  decide +kernel

/-- Exact integer rows. No numerical spectral-radius assertion is a premise. -/
theorem radiusFour_potential :
    (∀ i : Fin 881, 1 ≤ radiusFourWeight i ∧ radiusFourWeight i ≤ 100000 ∧
      2500 * childWeight radiusFourStep radiusFourWeight i (radiusFourChoice i) ≤
        6202 * radiusFourWeight i) ∧ radiusFourWeight 0 = 100000 := by
  decide +kernel

private theorem rejected_iff (i : Fin 881) (d : Fin 3) :
    radiusFourStep i (radiusFourChoice i) d = none ↔ direction d ∈ radiusFourMask i := by
  have hg := radiusFour_geometry.2.2.2.2 i d
  constructor
  · intro hs
    simpa [hs] using hg
  · intro hm
    cases hs : radiusFourStep i (radiusFourChoice i) d with
    | none => rfl
    | some j =>
        rw [hs] at hg
        exact False.elim (hg.1 hm)

private theorem successor_mask (i : Fin 881) (d : Fin 3) (j : Fin 881)
    (hs : radiusFourStep i (radiusFourChoice i) d = some j) :
    radiusFourMask j = memoryStep 4 (radiusFourMask i) (radiusFourChoice i) d := by
  have hg := radiusFour_geometry.2.2.2.2 i d
  rw [hs] at hg
  exact hg.2

/-- Every state and every depth has an explicit upper bound. -/
theorem radiusFour_count_upper (n : ℕ) (h : List (Fin 3)) (i : Fin 881) :
    2500 ^ n * pathCount radiusFourStep (fun _ j => radiusFourChoice j) n h i ≤
      6202 ^ n * radiusFourWeight i := by
  exact upper_of_superpotential radiusFourStep (fun _ j => radiusFourChoice j)
    radiusFourWeight 6202 2500 (fun j => (radiusFour_potential.1 j).1)
    (fun _ j => (radiusFour_potential.1 j).2.2) n h i

/-- Uniform finite-domain bound at every represented memory state, with a
single prefactor for all domains, holes, boundaries, states and depths. -/
theorem radiusFour_domain_upper (n : ℕ) (V : Finset Point) (i : Fin 881)
    (hdis : Disjoint V (radiusFourMask i)) :
    2500 ^ n * orderedCount radiusFourStep radiusFourChoice 0 n V i ≤
      100000 * 6202 ^ n := by
  have hs := orderedCount_le_pathCount_selected radiusFourStep radiusFourChoice 0
    radiusFourMask 4 rejected_iff successor_mask n V i [] hdis
  calc
    _ ≤ 2500 ^ n * pathCount radiusFourStep
          (fun _ j => radiusFourChoice j) n [] i := Nat.mul_le_mul_left _ hs
    _ ≤ 6202 ^ n * radiusFourWeight i := radiusFour_count_upper n [] i
    _ ≤ 6202 ^ n * 100000 := Nat.mul_le_mul_left _ (radiusFour_potential.1 i).2.1
    _ = _ := by ring

/-- The same certificate applies to every parent-deleted finite grid domain. -/
theorem radiusFour_parent_domain_upper (n : ℕ) (V : Finset Point)
    (hp : (-1, 0) ∉ V) :
    2500 ^ n * orderedCount radiusFourStep radiusFourChoice 0 n V 0 ≤
      100000 * 6202 ^ n := by
  apply radiusFour_domain_upper
  rw [radiusFour_geometry.2.2.1]
  simpa using hp

/-- All four grid directions at an unconditioned root. -/
def rootDirection (e : Fin 4) : Point :=
  if e = 0 then (1, 0) else if e = 1 then (0, -1)
  else if e = 2 then (0, 1) else (-1, 0)

private def rootRecenter (e : Fin 4) (p : Point) : Point :=
  if e = 0 then (p.1 - 1, p.2) else if e = 1 then (-p.2 - 1, p.1)
  else if e = 2 then (p.2 - 1, -p.1) else (-p.1 - 1, -p.2)

private def rootDeleted (e : Fin 4) : Finset Point :=
  insert (0, 0) ((Finset.univ.filter fun j : Fin 4 => j < e).image rootDirection)

/-- The actual root branch after earlier neighbors and the root are deleted. -/
def rootDomain (V : Finset Point) (e : Fin 4) : Finset Point :=
  (V \ rootDeleted e).image (rootRecenter e)

private theorem root_preimage_parent (e : Fin 4) (p : Point)
    (hp : rootRecenter e p = (-1, 0)) : p = (0, 0) := by
  have hx := congrArg Prod.fst hp
  have hy := congrArg Prod.snd hp
  apply Prod.ext
  · fin_cases e <;> simp [rootRecenter] at hx hy ⊢ <;> omega
  · fin_cases e <;> simp [rootRecenter] at hx hy ⊢ <;> omega

private theorem parent_absent_rootDomain (V : Finset Point) (e : Fin 4) :
    (-1, 0) ∉ rootDomain V e := by
  intro hp
  rcases Finset.mem_image.mp hp with ⟨p, hp, heq⟩
  have hzero := root_preimage_parent e p heq
  have hnot := (Finset.mem_sdiff.mp hp).2
  apply hnot
  rw [hzero]
  simp [rootDeleted]

/-- Four-neighbor root with actual domain-membership tests. An absent root
contributes zero. Nonroot branches use the certified radius-four controller. -/
def rootCount : ℕ → Finset Point → ℕ
  | 0, V => if (0, 0) ∈ V then 1 else 0
  | n + 1, V => if (0, 0) ∈ V then
      ∑ e : Fin 4, if rootDirection e ∈ V then
        orderedCount radiusFourStep radiusFourChoice 0 n (rootDomain V e) 0 else 0
      else 0

/-- A single all-root prefactor. This closes the omitted four-direction root
for the deletion-path count, not the separate partition-polynomial identity. -/
theorem radiusFour_root_upper (n : ℕ) (V : Finset Point) :
    2500 ^ n * rootCount n V ≤ 400000 * 6202 ^ n := by
  cases n with
  | zero => by_cases h0 : (0, 0) ∈ V <;> simp [rootCount, h0]
  | succ n =>
      have hpart : 2500 ^ n * rootCount (n + 1) V ≤ 400000 * 6202 ^ n := by
        by_cases h0 : (0, 0) ∈ V
        · calc
            _ = ∑ e : Fin 4, 2500 ^ n *
                  (if rootDirection e ∈ V then
                    orderedCount radiusFourStep radiusFourChoice 0 n (rootDomain V e) 0
                    else 0) := by simp only [rootCount, if_pos h0, Finset.mul_sum]
            _ ≤ ∑ _e : Fin 4, 100000 * 6202 ^ n := by
              apply Finset.sum_le_sum
              intro e _
              by_cases he : rootDirection e ∈ V
              · rw [if_pos he]
                exact radiusFour_parent_domain_upper n (rootDomain V e)
                  (parent_absent_rootDomain V e)
              · simp [he]
            _ = _ := by simp <;> ring
        · simp [rootCount, h0]
      calc
        _ = 2500 * (2500 ^ n * rootCount (n + 1) V) := by rw [pow_succ]; ring
        _ ≤ 2500 * (400000 * 6202 ^ n) := Nat.mul_le_mul_left _ hpart
        _ ≤ _ := by rw [pow_succ]; nlinarith [Nat.zero_le (6202 ^ n)]

#print axioms radiusFour_geometry
#print axioms radiusFour_potential
#print axioms radiusFour_count_upper
#print axioms radiusFour_domain_upper
#print axioms radiusFour_parent_domain_upper
#print axioms radiusFour_root_upper

end D5.S3.StatisticalMechanics.HardCore.AdaptiveRadiusFourCertificates
