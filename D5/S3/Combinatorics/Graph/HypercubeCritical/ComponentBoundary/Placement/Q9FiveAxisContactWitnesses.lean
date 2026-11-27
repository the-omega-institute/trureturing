/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisContactWitnesses
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisContactWitnesses
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: An even endpoint with the specified displacement supplies a witness at the corresponding little-endian index. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9EightMaskClauses
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisOrbitGeometry

/-! Witness variables for the eight remaining masks after choosing the root contact. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisContactWitnesses

open Finset
open D5.S3.Combinatorics.Graph.HypercubeCritical (cubeBitVec)
open BalancedCriticalSpectrum (Q)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9IsotropicHuang (parity)
open Q9SharedContactCNF (Word)
open Q9FiveAxisOrbitGeometry (family)
open private evenWord indexOfWord evenWord_index axesOf xor_mask positive_list from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9EightMaskClauses
open private mem_minimumDisplacements from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator

private def masks : Fin 8 → Word := ![5, 9, 10, 12, 17, 18, 20, 24]

private theorem masks_mem (m : Fin 8) : axesOf (masks m) ∈ family := by
  fin_cases m <;> decide +kernel

/-- The first mask witness has DIMACS index 10241. -/
def witnessIndex (m : Fin 8) (i : Fin 256) : ℕ := 10240 + 256 * m.val + i.val

/-- The supplied valuation on the other indices is preserved. -/
def installWitnesses (C D : Finset (Q 9)) (other : Sat.Valuation) : Sat.Valuation := fun n =>
  if hn : 10240 ≤ n ∧ n < 12288 then
    let k := n - 10240
    let m : Fin 8 := ⟨k / 256, by omega⟩
    let i : Fin 256 := ⟨k % 256, Nat.mod_lt _ (by decide)⟩
    cubeBitVec 9 (evenWord i) ∈ C ∧ cubeBitVec 9 (evenWord i ^^^ masks m) ∈ D
  else other n

private theorem witness_value (C D : Finset (Q 9)) (other : Sat.Valuation)
    (m : Fin 8) (i : Fin 256) :
    installWitnesses C D other (witnessIndex m i) ↔
      cubeBitVec 9 (evenWord i) ∈ C ∧ cubeBitVec 9 (evenWord i ^^^ masks m) ∈ D := by
  have hm := m.isLt
  have hi := i.isLt
  have hn : 10240 ≤ witnessIndex m i ∧ witnessIndex m i < 12288 := by
    unfold witnessIndex
    omega
  have hdiv : (witnessIndex m i - 10240) / 256 = m.val := by
    unfold witnessIndex
    omega
  have hmod : (witnessIndex m i - 10240) % 256 = i.val := by
    unfold witnessIndex
    omega
  have hM (h : ((witnessIndex m i - 10240) / 256) < 8) :
      (⟨(witnessIndex m i - 10240) / 256, h⟩ : Fin 8) = m := Fin.ext hdiv
  have hI (h : ((witnessIndex m i - 10240) % 256) < 256) :
      (⟨(witnessIndex m i - 10240) % 256, h⟩ : Fin 256) = i := Fin.ext hmod
  simp only [installWitnesses, dite_eq_left hn, hM, hI]

/-- Every required mask has a true SAT witness in the even parity. -/
theorem realized_clause {C D : Finset (Q 9)} {other : Sat.Valuation}
    (hfamily : minimumDisplacements C D false 2 = family) (m : Fin 8) :
    (installWitnesses C D other).satisfies
      ((List.finRange 256).map fun i => Sat.Literal.pos (witnessIndex m i)) := by
  have hm : axesOf (masks m) ∈ minimumDisplacements C D false 2 := by
    rw [hfamily]
    exact masks_mem m
  obtain ⟨x, hx, y, hy, hp, _, hmask⟩ := mem_minimumDisplacements.mp hm
  obtain ⟨u, rfl⟩ := (cubeBitVec 9).surjective x
  obtain ⟨v, rfl⟩ := (cubeBitVec 9).surjective y
  have hax : axesOf (u ^^^ v) = axesOf (masks m) := xor_mask.symm.trans hmask
  have he : u ^^^ v = masks m := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have h := (Finset.ext_iff.mp hax ⟨j, hj⟩)
    simp only [axesOf, mem_filter, mem_univ, true_and] at h
    exact Bool.eq_iff_iff.mpr h
  have hv : u ^^^ masks m = v := by
    rw [← he, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  let i := indexOfWord u
  have hw : installWitnesses C D other (witnessIndex m i) := by
    apply (witness_value C D other m i).mpr
    rw [show evenWord i = u from evenWord_index u hp, hv]
    exact ⟨hx, hy⟩
  have hmem : witnessIndex m i ∈ (List.finRange 256).map (witnessIndex m) :=
    List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
  have clause := positive_list (v := installWitnesses C D other) ⟨_, hmem, hw⟩
  rw [List.map_map] at clause
  exact clause

#print axioms realized_clause

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisContactWitnesses
