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

/-! Native optional-first-mark partitions and their uniform threshold statistics. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators symmDiff

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
  rw [Fintype.card_coe, Fintype.card_coe] at h
  have hp : (YoungDiagram.ofPartition p).rowLens.toFinset = p.parts.toFinset := by
    ext r
    simp
  change (YoungDiagram.ofPartition p).transpose.rowLens.toFinset.card = _
  rw [← h, hp]

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
  rw [show T n = ∑ p : Nat.Partition n, weight p * (p.parts.card : ℤ) from by simpa only [T] using sum_marks (fun p => (p.parts.card : ℤ))]
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

private def count (n : ℕ) : ℤ := ∑ p : Nat.Partition n, weight p

private def threshold (k n r : ℕ) : ℤ :=
  ∑ p : Nat.Partition n, if k ≤ p.parts.count r then weight p else 0

private def shiftEquiv (n k r : ℕ) (hr : 0 < r) (hn : k * r ≤ n) :
    {p : Nat.Partition n // k ≤ p.parts.count r} ≃ Nat.Partition (n - k * r) where
  toFun p := {
    parts := p.1.parts - Multiset.replicate k r
    parts_pos := by
      intro x hx
      exact p.1.parts_pos (Multiset.mem_of_le (tsub_le_self) hx)
    parts_sum := by
      have hle := Multiset.le_count_iff_replicate_le.mp p.2
      have he := congrArg Multiset.sum (tsub_add_cancel_of_le hle)
      simp only [Multiset.sum_add, Multiset.sum_replicate, p.1.parts_sum] at he
      omega }
  invFun q := ⟨{
    parts := q.parts + Multiset.replicate k r
    parts_pos := by
      intro x hx
      rcases Multiset.mem_add.mp hx with hx | hx
      · exact q.parts_pos hx
      · have he := Multiset.eq_of_mem_replicate hx
        simpa [he] using hr
    parts_sum := by simp [q.parts_sum, Nat.sub_add_cancel hn] }, by simp⟩
  left_inv p := Subtype.ext (Nat.Partition.ext
    (tsub_add_cancel_of_le (Multiset.le_count_iff_replicate_le.mp p.2)))
  right_inv q := Nat.Partition.ext (by simp)

private theorem shift_support (n k r : ℕ) (hk : 0 < k) (hr : 0 < r)
    (hn : k * r ≤ n) (q : Nat.Partition (n - k * r)) :
    ((shiftEquiv n k r hr hn).symm q).1.parts.toFinset = insert r q.parts.toFinset := by
  ext x
  simp [shiftEquiv, Multiset.mem_replicate, hk.ne', eq_comm, or_comm]

private theorem shift_weight (n k r : ℕ) (hk : 0 < k) (hr : 0 < r)
    (hn : k * r ≤ n) (q : Nat.Partition (n - k * r)) :
    weight ((shiftEquiv n k r hr hn).symm q).1 =
      if r ∈ q.parts then weight q else 2 * weight q := by
  classical
  unfold weight
  rw [shift_support n k r hk hr hn]
  by_cases h : r ∈ q.parts
  · simp [h]
  · simp [h, pow_succ, mul_comm]

private theorem threshold_shift (k n r : ℕ) (hk : 0 < k) (hr : 0 < r)
    (hn : k * r ≤ n) :
    threshold k n r + threshold (k + 1) n r = 2 * count (n - k * r) := by
  classical
  let e := shiftEquiv n k r hr hn
  have hsub : (∑ p : {p : Nat.Partition n // k ≤ p.parts.count r},
      (weight p.1 + if k + 1 ≤ p.1.parts.count r then weight p.1 else 0)) =
      threshold k n r + threshold (k + 1) n r := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun p : Nat.Partition n =>
      k ≤ p.parts.count r)) (by simp)]
    simp only [Finset.sum_filter]
    unfold threshold
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> omega
  rw [← hsub, ← e.symm.sum_comp]
  unfold count
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [shift_weight n k r hk hr hn]
  have hc : (e.symm q).1.parts.count r = q.parts.count r + k := by
    simp [e, shiftEquiv]
  rw [hc]
  by_cases hm : r ∈ q.parts
  · have hm' := Multiset.count_pos.mpr hm
    simp [hm, show k + 1 ≤ q.parts.count r + k by omega]
    ring
  · have hm' := Multiset.count_eq_zero.mpr hm
    simp [hm, hm']

private theorem threshold_zero (k n r : ℕ) (hr : 0 < r) (hn : n < k * r) :
    threshold k n r = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro p _
  have hb : p.parts.count r * r ≤ n := by
    have h := Multiset.sum_le_sum
      (Multiset.le_count_iff_replicate_le.mp (le_refl (p.parts.count r)))
    simpa [Multiset.sum_replicate, p.parts_sum] using h
  have : ¬ k ≤ p.parts.count r := by nlinarith
  simp [this]

private def markTotal (s : Finset ℕ) (j : ℕ) : ℤ :=
  ∑ t : ↥s.powerset, if j ∈ t.1 then 1 else 0

private theorem markTotal_absent (s : Finset ℕ) (j : ℕ) (hj : j ∉ s) :
    markTotal s j = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro t _
  have : j ∉ t.1 := fun h => hj (Finset.mem_powerset.mp t.2 h)
  simp [this]

private def toggle (s : Finset ℕ) (j : ℕ) (hj : j ∈ s) :
    ↥s.powerset ≃ ↥s.powerset where
  toFun t := ⟨t.1 ∆ {j}, by
    apply Finset.mem_powerset.mpr
    intro x hx
    rcases Finset.mem_symmDiff.mp hx with hx | hx
    · exact Finset.mem_powerset.mp t.2 hx.1
    · have : x = j := Finset.mem_singleton.mp hx.1
      simpa [this] using hj⟩
  invFun t := ⟨t.1 ∆ {j}, by
    apply Finset.mem_powerset.mpr
    intro x hx
    rcases Finset.mem_symmDiff.mp hx with hx | hx
    · exact Finset.mem_powerset.mp t.2 hx.1
    · have : x = j := Finset.mem_singleton.mp hx.1
      simpa [this] using hj⟩
  left_inv t := Subtype.ext (by simp)
  right_inv t := Subtype.ext (by simp)

private theorem twice_markTotal (s : Finset ℕ) (j : ℕ) (hj : j ∈ s) :
    2 * markTotal s j = (2 : ℤ) ^ s.card := by
  classical
  have he := (toggle s j hj).sum_comp
    (fun t : ↥s.powerset => if j ∈ t.1 then (1 : ℤ) else 0)
  have hi : (∑ t : ↥s.powerset, if j ∈ (toggle s j hj t).1 then (1 : ℤ) else 0) =
      ∑ t : ↥s.powerset, (1 - if j ∈ t.1 then (1 : ℤ) else 0) := by
    apply Finset.sum_congr rfl
    intro t _
    by_cases h : j ∈ t.1 <;> simp [toggle, Finset.mem_symmDiff, h]
  rw [hi] at he
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    Fintype.card_coe, Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat] at he
  change (2 : ℤ) ^ s.card * 1 - markTotal s j = markTotal s j at he
  linarith

private def frequency {n : ℕ} (j : ℕ) (p : Nat.Partition n) : ℤ :=
  (p.parts.count j : ℤ) * weight p - markTotal p.parts.toFinset j

private theorem N_frequency (j n : ℕ) : N j n = ∑ p : Nat.Partition n, frequency j p := by
  classical
  unfold N
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro p _
  simp [multiplicity, frequency, weight, markTotal, Finset.sum_sub_distrib,
    Finset.card_powerset, mul_comm]

private theorem frequency_absent {n : ℕ} (j : ℕ) (p : Nat.Partition n)
    (hj : j ∉ p.parts) : frequency j p = 0 := by
  simp [frequency, Multiset.count_eq_zero.mpr hj, markTotal_absent _ j (by simpa using hj)]

private theorem frequency_insert (j n : ℕ) (hj : 0 < j) (hn : j ≤ n)
    (q : Nat.Partition (n - j)) :
    frequency j (((Nat.Partition.partitionWithPartEquiv hj hn).symm q).1) =
      frequency j q + weight q := by
  classical
  let p := ((Nat.Partition.partitionWithPartEquiv hj hn).symm q).1
  have hp : p.parts = j ::ₘ q.parts := by
    exact Nat.Partition.partitionWithPartEquiv_symm_apply_parts hj hn q
  have hs : p.parts.toFinset = insert j q.parts.toFinset := by simp [hp]
  have hm : j ∈ p.parts.toFinset := by simp [hs]
  have hmark := twice_markTotal p.parts.toFinset j hm
  have hw : weight p = if j ∈ q.parts then weight q else 2 * weight q := by
    unfold weight
    rw [hs]
    by_cases h : j ∈ q.parts <;> simp [h, pow_succ, mul_comm]
  change frequency j p = _
  unfold frequency
  have hc : p.parts.count j = q.parts.count j + 1 := by simp [hp]
  rw [hc, Nat.cast_add, Nat.cast_one, hw]
  change 2 * markTotal p.parts.toFinset j = weight p at hmark
  rw [hw] at hmark
  by_cases h : j ∈ q.parts
  · have hq := twice_markTotal q.parts.toFinset j (by simpa using h)
    change 2 * markTotal q.parts.toFinset j = weight q at hq
    simp only [if_pos h] at hmark ⊢
    nlinarith
  · have hq := markTotal_absent q.parts.toFinset j (by simpa using h)
    have hcq := Multiset.count_eq_zero.mpr h
    simp only [if_neg h] at hmark ⊢
    rw [hcq, Nat.cast_zero, hq]
    nlinarith

private theorem N_step (j n : ℕ) (hj : 0 < j) (hn : j ≤ n) :
    N j n = N j (n - j) + count (n - j) := by
  classical
  rw [N_frequency, N_frequency, ← Finset.sum_add_distrib]
  have hs : (∑ p : {p : Nat.Partition n // j ∈ p.parts}, frequency j p.1) =
      ∑ p : Nat.Partition n, frequency j p := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun p : Nat.Partition n =>
      j ∈ p.parts)) (by simp), Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : j ∈ p.parts
    · simp [h]
    · simp [h, frequency_absent j p h]
  rw [← hs, ← (Nat.Partition.partitionWithPartEquiv hj hn).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro q _
  exact frequency_insert j n hj hn q

private theorem N_zero (j n : ℕ) (hn : n < j) : N j n = 0 := by
  classical
  rw [N_frequency]
  apply Finset.sum_eq_zero
  intro p _
  exact frequency_absent j p (fun hm => Nat.not_le_of_lt hn (p.le_of_mem_parts hm))

end D5.S3.Combinatorics.Partitions.OverpartitionThreshold
