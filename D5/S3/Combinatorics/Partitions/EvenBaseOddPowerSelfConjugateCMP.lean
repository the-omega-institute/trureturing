/- GID: D5/S3/Combinatorics/Partitions/EvenBaseOddPowerSelfConjugateCMP
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/EvenBaseOddPowerSelfConjugateCMP
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Lower bound on the odd exponent of a self-conjugate CMP of an even-base power. -/

import D5.S3.Combinatorics.Partitions.OddPowerSelfConjugateCMP
import Mathlib.NumberTheory.Multiplicity

/-! A square congruence and the area bounds of a self-conjugate Young diagram
give a lower bound on the odd exponent of an even-base power. -/

namespace D5.S3.Combinatorics.Partitions.EvenBaseOddPowerSelfConjugateCMP

open OddPowerSelfConjugateCMP

private theorem area_bounds (μ : YoungDiagram) (hne : 0 < μ.rowLen 0)
    (hself : μ.transpose = μ) :
    2 * μ.rowLen 0 - 1 ≤ μ.card ∧ μ.card ≤ (μ.rowLen 0) ^ 2 := by
  classical
  have hheight : μ.colLen 0 = μ.rowLen 0 := by
    rw [← YoungDiagram.rowLen_transpose, hself]
  have hinter : μ.row 0 ∩ μ.col 0 = {(0, 0)} := by
    ext ⟨i, j⟩
    rw [Finset.mem_inter, YoungDiagram.row_eq_prod, YoungDiagram.col_eq_prod, hheight]
    simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hi, _⟩, ⟨_, hj⟩⟩
      exact ⟨hi, hj⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨rfl, hne⟩, ⟨hne, rfl⟩⟩
  have hcross : μ.row 0 ∪ μ.col 0 ⊆ μ.cells := by
    intro cell hcell
    rcases Finset.mem_union.mp hcell with hrow | hcol
    · exact (Finset.mem_filter.mp hrow).1
    · exact (Finset.mem_filter.mp hcol).1
  have hcrossCard := Finset.card_le_card hcross
  have hsum := Finset.card_union_add_card_inter (μ.row 0) (μ.col 0)
  rw [hinter, Finset.card_singleton, ← YoungDiagram.rowLen_eq_card,
    ← YoungDiagram.colLen_eq_card, hheight] at hsum
  change (μ.row 0 ∪ μ.col 0).card ≤ μ.card at hcrossCard
  refine ⟨by omega, ?_⟩
  have hbox : μ.cells ⊆ Finset.range (μ.rowLen 0) ×ˢ Finset.range (μ.rowLen 0) := by
    intro ⟨i, j⟩ hcell
    have hj := YoungDiagram.mem_iff_lt_rowLen.mp hcell
    have hi := YoungDiagram.mem_iff_lt_colLen.mp hcell
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨hi.trans_le ((μ.colLen_anti 0 j (Nat.zero_le j)).trans_eq hheight),
      hj.trans_le (μ.rowLen_anti 0 i (Nat.zero_le i))⟩
  simpa only [Finset.card_product, Finset.card_range, pow_two] using Finset.card_le_card hbox

/-- The lower bound in Question 5.12 of Dietz, Flowers and Lockard. -/
theorem lower_bound (m : ℕ) (hm : 2 ≤ m) (_hmEven : Even m)
    (e : ℕ) (he : Odd e) (μ : YoungDiagram) (hcard : μ.card = m ^ e)
    (hcmp : IsCMP m μ) (hself : μ.transpose = μ) : m + 1 ≤ e := by
  have hmOne : 1 < m := hm
  have hePos : 0 < e := by
    obtain ⟨j, hj⟩ := he
    omega
  have hcardOne : 1 < μ.card := by
    rw [hcard]
    exact one_lt_pow₀ hmOne hePos.ne'
  have hcells : 0 < μ.cells.card := by
    change 0 < μ.card
    omega
  obtain ⟨⟨i, j⟩, hij⟩ := Finset.card_pos.mp hcells
  have hne : 0 < μ.rowLen 0 := YoungDiagram.mem_iff_lt_rowLen.mp
    (μ.up_left_mem (Nat.zero_le i) (Nat.zero_le j) hij)
  obtain ⟨hcross, hbox⟩ := area_bounds μ hne hself
  have hwidth : 1 < μ.rowLen 0 := by
    by_contra! hle
    have hone : μ.rowLen 0 = 1 := by omega
    simp [hone] at hbox
    omega
  obtain ⟨K, hK⟩ := hcmp.1 0 hne
  have hpow : StrictMono (fun n : ℕ => m ^ n) := pow_right_strictMono₀ hmOne
  have hKe : K < e := hpow.lt_iff_lt.mp (by
    have hle : μ.rowLen 0 < μ.card := by omega
    simpa only [hK, hcard] using hle)
  have heK : e ≤ 2 * K := hpow.le_iff_le.mp (by
    simpa only [hK, hcard, ← pow_mul, Nat.mul_comm K 2] using hbox)
  have hgap : 0 < 2 * K - e ∧ 2 * K - e ≤ e - 2 := by
    obtain ⟨k, hk⟩ := he
    omega

  let d : ℤ := (m : ℤ) - 1
  have hdPos : 0 < d := by
    dsimp [d]
    omega
  have hbase : (1 : ℤ) + d = (m : ℤ) := by
    dsimp [d]
    ring
  have hgeom : d ^ 2 ∣ (m : ℤ) ^ e - (2 * (m : ℤ) ^ K - 1) := by
    simpa only [d, hcard, hK, Nat.cast_pow] using square_modulus m μ hcmp hne hself
  have heRem : d ^ 2 ∣ (m : ℤ) ^ e - d * (e : ℤ) - 1 := by
    simpa only [hbase, one_pow, one_mul] using sq_dvd_add_pow_sub_sub d (1 : ℤ) e
  have hKRem : d ^ 2 ∣ (m : ℤ) ^ K - d * (K : ℤ) - 1 := by
    simpa only [hbase, one_pow, one_mul] using sq_dvd_add_pow_sub_sub d (1 : ℤ) K
  have hmultiple : d ^ 2 ∣ d * (2 * (K : ℤ) - (e : ℤ)) := by
    convert dvd_sub (dvd_sub heRem (dvd_add hKRem hKRem)) hgeom using 1 <;> ring
  have hdiv : d ∣ 2 * (K : ℤ) - (e : ℤ) :=
    Int.dvd_of_mul_dvd_mul_left hdPos.ne' (by simpa only [pow_two] using hmultiple)
  have hgapCast : ((2 * K - e : ℕ) : ℤ) = 2 * (K : ℤ) - (e : ℤ) := by
    rw [Nat.cast_sub heK, Nat.cast_mul, Nat.cast_ofNat]
  rw [← hgapCast] at hdiv
  have hle : d ≤ ((2 * K - e : ℕ) : ℤ) :=
    Int.le_of_dvd (by exact_mod_cast hgap.1) hdiv
  dsimp [d] at hle
  omega

end D5.S3.Combinatorics.Partitions.EvenBaseOddPowerSelfConjugateCMP
