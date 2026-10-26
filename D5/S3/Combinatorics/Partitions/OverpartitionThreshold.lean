/- GID: D5/S3/Combinatorics/Partitions/OverpartitionThreshold
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/OverpartitionThreshold
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram]
   utility: none
   digest: Native overpartition threshold counts and nonoverlined frequencies. -/

import D5.S1.Words.Compositions.StrictFirstSumsGapfreeOddParts
import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace D5.S3.Combinatorics.Partitions.OverpartitionThreshold

/-- A mark selects the first occurrence of each chosen positive part size. -/
abbrev Overpartition (n : ℕ) := Σ p : Nat.Partition n, ↥p.parts.toFinset.powerset

/-- All occurrences, including the possibly marked first occurrence. -/
def multiplicity {n : ℕ} (o : Overpartition n) (r : ℕ) : ℕ := o.1.parts.count r

/-- The empty partition has largest part zero. -/
def largest {n : ℕ} (o : Overpartition n) : ℕ := o.1.parts.toFinset.sup id

/-- Missing positive sizes below the largest part are included. -/
def U (k n : ℕ) : ℤ := ∑ o : Overpartition n,
  (((Finset.Icc 1 (largest o)).filter (fun r => multiplicity o r < k)).card : ℤ)

/-- Total number of parts, including all marked occurrences. -/
def T (n : ℕ) : ℤ := ∑ o : Overpartition n, (o.1.parts.card : ℤ)

/-- The mark removes exactly one occurrence from the nonoverlined count. -/
def N (j n : ℕ) : ℤ := ∑ o : Overpartition n,
  ((multiplicity o j : ℤ) - if j ∈ o.2.1 then 1 else 0)

private def weight {n : ℕ} (p : Nat.Partition n) : ℤ := 2 ^ p.parts.toFinset.card

private theorem sum_marks {n : ℕ} (f : Nat.Partition n → ℤ) :
    (∑ o : Overpartition n, f o.1) = ∑ p : Nat.Partition n, weight p * f p := by
  classical
  simp [Overpartition, Fintype.sum_sigma, weight, Fintype.card_coe, Finset.card_powerset]

private theorem corner_inverse (d : YoungDiagram) (r : ℕ) (hr : r ∈ d.rowLens) :
    d.rowLen (d.colLen (r - 1) - 1) = r := by
  have rp := d.pos_of_mem_rowLens r hr
  have drop := (D5.S1.Words.Compositions.StrictFirstSumsGapfreeOddParts.height_mem_iff
    d.transpose r rp).mp (by simpa using hr)
  simp only [YoungDiagram.rowLen_transpose] at drop
  have hp : 0 < d.colLen (r - 1) := by omega
  have a : (d.colLen (r - 1) - 1, r - 1) ∈ d :=
    YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  have b : ¬ (d.colLen (r - 1) - 1, r) ∈ d := by
    rw [YoungDiagram.mem_iff_lt_colLen]
    omega
  rw [YoungDiagram.mem_iff_lt_rowLen] at a b
  omega

private theorem corner_mem (d : YoungDiagram) (r : ℕ) (hr : r ∈ d.rowLens) :
    d.colLen (r - 1) ∈ d.transpose.rowLens := by
  obtain ⟨i, hi, he⟩ := List.mem_map.mp hr
  change d.rowLen i = r at he
  have rp := d.pos_of_mem_rowLens r hr
  have rb : r ≤ d.rowLen 0 := he ▸ d.rowLen_anti 0 i (Nat.zero_le _)
  apply List.mem_map.mpr
  refine ⟨r - 1, ?_, ?_⟩
  · simpa only [List.mem_range, YoungDiagram.colLen_transpose] using (show r - 1 < d.rowLen 0 by omega)
  · exact YoungDiagram.rowLen_transpose d (r - 1)

private def cornerEquiv (d : YoungDiagram) :
    ↥d.rowLens.toFinset ≃ ↥d.transpose.rowLens.toFinset where
  toFun r := ⟨d.colLen (r.1 - 1), List.mem_toFinset.mpr (corner_mem d r.1 (List.mem_toFinset.mp r.2))⟩
  invFun h := ⟨d.rowLen (h.1 - 1), by
    simpa using corner_mem d.transpose h.1 (List.mem_toFinset.mp h.2)⟩
  left_inv r := Subtype.ext (corner_inverse d r.1 (List.mem_toFinset.mp r.2))
  right_inv h := Subtype.ext (by
    simpa using corner_inverse d.transpose h.1 (List.mem_toFinset.mp h.2))

private theorem conjugate_support_card {n : ℕ} (p : Nat.Partition n) :
    p.conjugate.parts.toFinset.card = p.parts.toFinset.card := by
  have h := Fintype.card_congr (cornerEquiv (YoungDiagram.ofPartition p))
  simpa [Nat.Partition.conjugate, YoungDiagram.toPartition,
    YoungDiagram.rowLens_ofPartition_eq_sort_parts, Multiset.toFinset_sort] using h.symm

private theorem row_sup (d : YoungDiagram) : d.rowLens.toFinset.sup id = d.rowLen 0 := by
  apply le_antisymm
  · apply Finset.sup_le
    intro r hr
    obtain ⟨i, hi, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hr)
    change d.rowLen i = r at he
    exact he ▸ d.rowLen_anti 0 i (Nat.zero_le _)
  · by_cases h : d.rowLen 0 = 0
    · simp [h]
    · have a : (0, 0) ∈ d := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have b := YoungDiagram.mem_iff_lt_colLen.mp a
      apply Finset.le_sup (f := id)
      apply List.mem_toFinset.mpr
      exact List.mem_map.mpr ⟨0, by simpa using b, rfl⟩

private theorem conjugate_largest {n : ℕ} (p : Nat.Partition n) :
    p.conjugate.parts.toFinset.sup id = p.parts.card := by
  change (YoungDiagram.ofPartition p).transpose.rowLens.toFinset.sup id = _
  rw [row_sup, YoungDiagram.rowLen_transpose]
  have h := YoungDiagram.length_rowLens (μ := YoungDiagram.ofPartition p)
  simpa using h.symm

private theorem sum_largest (n : ℕ) :
    (∑ o : Overpartition n, (largest o : ℤ)) = T n := by
  classical
  rw [show T n = ∑ p : Nat.Partition n, weight p * (p.parts.card : ℤ) from sum_marks _]
  change (∑ o : Overpartition n, ((o.1.parts.toFinset.sup id : ℕ) : ℤ)) = _
  rw [sum_marks]
  let e : Nat.Partition n ≃ Nat.Partition n :=
    ⟨Nat.Partition.conjugate, Nat.Partition.conjugate,
      Nat.Partition.conjugate_conjugate, Nat.Partition.conjugate_conjugate⟩
  rw [← e.sum_comp (fun p => weight p * ((p.parts.toFinset.sup id : ℕ) : ℤ))]
  apply Finset.sum_congr rfl
  intro p _
  change weight p.conjugate * ((p.conjugate.parts.toFinset.sup id : ℕ) : ℤ) = _
  rw [conjugate_largest]
  simp only [weight, conjugate_support_card]

end D5.S3.Combinatorics.Partitions.OverpartitionThreshold
