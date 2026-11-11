/- GID: D5/S3/Combinatorics/Partitions/OddPowerSelfConjugateCMP
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/OddPowerSelfConjugateCMP
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Dietz–Flowers–Lockard Question 5.14 has a kernel-verified negative answer. -/

/- Public result uses the literal source definitions in `claim`; proof helpers use existing YoungDiagram
   operations and Mathlib divisibility lemmas directly.
   IsMAry: proof_shape: definition; escape_witness: none.
   multiplicity: proof_shape: definition; escape_witness: none.
   IsCMP: proof_shape: definition; escape_witness: none.
   claim: proof_shape: definition; escape_witness: none.
   result: proof_shape: bind-only; escape_witness: none.
   admission_basis: open-problem-resolution (#21691; Proved) for IsMAry, multiplicity, IsCMP, claim and result.
   Direct frozen dependencies: D5/S1/Words/Compositions/StrictFirstSumsGapfreeOddParts.height_bounds,
   published from the frozen private declaration with statement_id
   sha256:8295b06a8088d81ef0282ad721103950ba5f24a0e8e0b7d1d630a50986c6c891.
   D5/S1/Words/Compositions/StrictFirstSumsGapfreeOddParts.rowLen_zero is published
   from the frozen private declaration with statement_id
   sha256:efaaa12164c1db0e709c1a0104797eb3bf77e2e3e1442c2b671f377ce75a429f.
   row_fiber: proof_shape: bind-only; consumer: row_count; escape_witness: none.
   row_count: proof_shape: bind-only; consumer: square_modulus; escape_witness: none.
   part_power: proof_shape: bind-only; consumer: square_modulus; escape_witness: none.
   square_modulus: proof_shape: bind-only; consumer: odd_modulus; escape_witness: none.
   odd_modulus: proof_shape: bind-only; consumer: result; escape_witness: none.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/26781.
-/

import Mathlib.Algebra.Ring.Int.Parity
import D5.S1.Words.Compositions.StrictFirstSumsGapfreeOddParts

/-! Binding conventions for Dietz–Flowers–Lockard, arXiv:2609.08799v1,
Question 5.14. `YoungDiagram` is the finite Ferrers diagram, `transpose` is
reflection in its main diagonal, and `card` is the partitioned integer.
Only positive row lengths are parts; absent rows have length zero. -/

namespace D5.S3.Combinatorics.Partitions.OddPowerSelfConjugateCMP

/-- Definition 1.1(2): every part is a nonnegative integral power of m. -/
def IsMAry (m : ℕ) (μ : YoungDiagram) : Prop :=
  ∀ (i : ℕ), 0 < μ.rowLen i → ∃ (j : ℕ), μ.rowLen i = m ^ j

/-- Definition 1.1(2): a_j is the number of occurrences of the part m^j. -/
def multiplicity (m : ℕ) (μ : YoungDiagram) (j : ℕ) : ℕ :=
  μ.rowLens.count (m ^ j)

/-- Definition 1.1(3): both the partition and its conjugate are m-ary. -/
def IsCMP (m : ℕ) (μ : YoungDiagram) : Prop :=
  IsMAry m μ ∧ IsMAry m μ.transpose

/-- Question 5.14, negative answer: no self-conjugate CMP of an odd power
of any odd base m >= 2 exists. Self-conjugacy is literal diagram equality. -/
def claim : Prop :=
  ∀ (m : ℕ), 2 ≤ m → Odd m →
    ∀ (s : ℕ), ∀ (μ : YoungDiagram),
      μ.card = m ^ (2 * s + 1) → IsCMP m μ → μ.transpose ≠ μ

end D5.S3.Combinatorics.Partitions.OddPowerSelfConjugateCMP

open scoped BigOperators
namespace D5.S3.Combinatorics.Partitions.OddPowerSelfConjugateCMP

private theorem row_fiber (μ : YoungDiagram) {w : ℕ} (hw : 0 < w) :
    {i ∈ Finset.range (μ.colLen 0) | μ.rowLen i = w} =
      Finset.range (μ.colLen (w - 1)) \ Finset.range (μ.colLen w) := by
  ext i
  have h₀ : i < μ.colLen 0 ↔ 0 < μ.rowLen i :=
    YoungDiagram.mem_iff_lt_colLen.symm.trans YoungDiagram.mem_iff_lt_rowLen
  have h₁ : i < μ.colLen (w - 1) ↔ w - 1 < μ.rowLen i :=
    YoungDiagram.mem_iff_lt_colLen.symm.trans YoungDiagram.mem_iff_lt_rowLen
  have h₂ : i < μ.colLen w ↔ w < μ.rowLen i :=
    YoungDiagram.mem_iff_lt_colLen.symm.trans YoungDiagram.mem_iff_lt_rowLen
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff, h₀, h₁, h₂]
  omega

private theorem row_count (μ : YoungDiagram) {w : ℕ} (hw : 0 < w) :
    ({i ∈ Finset.range (μ.colLen 0) | μ.rowLen i = w}.card : ℤ) =
      (μ.colLen (w - 1) : ℤ) - μ.colLen w := by
  rw [row_fiber μ hw, Finset.card_sdiff_of_subset]
  · simp only [Finset.card_range]
    exact Int.ofNat_sub (μ.colLen_anti (w - 1) w (by omega))
  · exact Finset.range_mono (μ.colLen_anti (w - 1) w (by omega))

private theorem part_power (m : ℕ) (μ : YoungDiagram) (hmary : IsMAry m μ)
    {w : ℕ} (hw : w ∈ μ.rowLens) : ∃ j : ℕ, w = m ^ j := by
  rw [YoungDiagram.rowLens] at hw
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  exact hmary i ((YoungDiagram.mem_iff_lt_rowLen.mp
    (YoungDiagram.mem_iff_lt_colLen.mpr (List.mem_range.mp hi))))


private theorem square_modulus (m : ℕ) (μ : YoungDiagram)
    (hcmp : IsCMP m μ) (hne : 0 < μ.rowLen 0) (hself : μ.transpose = μ) :
    ((m : ℤ) - 1) ^ 2 ∣ (μ.card : ℤ) - (2 * (μ.rowLen 0 : ℤ) - 1) := by
  classical
  let S := μ.rowLens.toFinset
  let C (w : ℕ) := {i ∈ Finset.range (μ.colLen 0) | μ.rowLen i = w}.card
  have hs (i : ℕ) (hi : i ∈ Finset.range (μ.colLen 0)) : μ.rowLen i ∈ S := by
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨i, by simpa using hi, rfl⟩
  have hcount : (∑ w ∈ S, C w) = μ.colLen 0 := by
    simpa only [Finset.card_range] using
      (Finset.card_eq_sum_card_fiberwise hs).symm
  have harea : (∑ w ∈ S, C w * w) = μ.card := by
    have hh := Finset.sum_fiberwise_of_maps_to hs μ.rowLen
    have hf : ∀ w ∈ S, (∑ i ∈ Finset.range (μ.colLen 0) with μ.rowLen i = w,
        μ.rowLen i) = C w * w := by
      intro w hw
      calc
        _ = ∑ i ∈ Finset.range (μ.colLen 0) with μ.rowLen i = w, w := by
          apply Finset.sum_congr rfl
          intro i hi
          exact (Finset.mem_filter.mp hi).2
        _ = C w * w := by simp [C]
    rw [Finset.sum_congr rfl hf] at hh
    rw [hh, ← μ.sum_rowLens_eq_card, YoungDiagram.rowLens,
      ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  have hheight : μ.colLen 0 = μ.rowLen 0 := by
    rw [← YoungDiagram.rowLen_transpose, hself]
  have hL : μ.rowLen 0 ∈ S := hs 0 (by simpa [hheight] using hne)
  have hparts (w : ℕ) (hw : w ∈ S) : 0 < w ∧ w ≤ μ.rowLen 0 := by
    simpa only [YoungDiagram.colLen_transpose] using
      D5.S1.Words.Compositions.StrictFirstSumsGapfreeOddParts.height_bounds μ.transpose w
        (by simpa only [YoungDiagram.transpose_transpose] using List.mem_toFinset.mp hw)
  have hpow (w : ℕ) (hw : w ∈ S) : (m : ℤ) - 1 ∣ (w : ℤ) - 1 := by
    obtain ⟨j, hj⟩ := part_power m μ hcmp.1 (List.mem_toFinset.mp hw)
    rw [hj, Nat.cast_pow]
    exact sub_one_dvd_pow_sub_one (m : ℤ) j
  have hcol (j : ℕ) (hj : 0 < μ.colLen j) :
      (m : ℤ) - 1 ∣ (μ.colLen j : ℤ) - 1 := by
    obtain ⟨k, hk⟩ := hcmp.2 j (by simpa using hj)
    rw [YoungDiagram.rowLen_transpose] at hk
    rw [hk, Nat.cast_pow]
    exact sub_one_dvd_pow_sub_one (m : ℤ) k
  have hmult (w : ℕ) (hw : w ∈ S) :
      (m : ℤ) - 1 ∣ (C w : ℤ) - (if w = μ.rowLen 0 then 1 else 0) := by
    have hwp := (hparts w hw).1
    have hbound := (hparts w hw).2
    have ha : 0 < μ.colLen (w - 1) := YoungDiagram.mem_iff_lt_colLen.mp
      (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
    have hca := hcol (w - 1) ha
    have hcard := row_count μ hwp
    change (C w : ℤ) = _ at hcard
    rw [hcard]
    by_cases heq : w = μ.rowLen 0
    · have hz : μ.colLen w = 0 := by
        simpa only [YoungDiagram.rowLen_transpose] using
          D5.S1.Words.Compositions.StrictFirstSumsGapfreeOddParts.rowLen_zero
            μ.transpose w (by simp [heq])
      rw [hz]
      simpa [heq] using hca
    · have hb : 0 < μ.colLen w := YoungDiagram.mem_iff_lt_colLen.mp
        (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      have hcb := hcol w hb
      have hd := dvd_sub hca hcb
      simpa [heq] using hd
  have hprod (w : ℕ) (hw : w ∈ S) : ((m : ℤ) - 1) ^ 2 ∣
      ((C w : ℤ) - (if w = μ.rowLen 0 then 1 else 0)) * ((w : ℤ) - 1) := by
    simpa [pow_two] using mul_dvd_mul (hmult w hw) (hpow w hw)
  have hsum := Finset.dvd_sum hprod
  have hc : ∑ w ∈ S, (C w : ℤ) = μ.rowLen 0 := by
    exact_mod_cast hcount.trans hheight
  have hn : ∑ w ∈ S, (C w : ℤ) * (w : ℤ) = μ.card := by
    exact_mod_cast harea
  have hid : (∑ w ∈ S,
      ((C w : ℤ) - (if w = μ.rowLen 0 then 1 else 0)) * ((w : ℤ) - 1)) =
      (μ.card : ℤ) - (2 * (μ.rowLen 0 : ℤ) - 1) := by
    simp_rw [sub_mul, mul_sub, mul_one, Finset.sum_sub_distrib]
    simp only [hn, hc, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', hL,
      ite_true]
    ring
  rwa [hid] at hsum


private theorem odd_modulus (m : ℕ) (μ : YoungDiagram)
    (hodd : Odd m) (hcmp : IsCMP m μ) (hne : 0 < μ.rowLen 0)
    (hself : μ.transpose = μ) :
    2 * ((m : ℤ) - 1) ∣ (μ.card : ℤ) - 1 := by
  have hs := square_modulus m μ hcmp hne hself
  have heven : (2 : ℤ) ∣ (m : ℤ) - 1 := by
    exact even_iff_two_dvd.mp (((Int.odd_coe_nat m).mpr hodd).sub_odd odd_one)
  have hd : 2 * ((m : ℤ) - 1) ∣ ((m : ℤ) - 1) ^ 2 := by
    simpa [pow_two] using mul_dvd_mul heven (dvd_refl ((m : ℤ) - 1))
  obtain ⟨K, hK⟩ := hcmp.1 0 hne
  have hL : (m : ℤ) - 1 ∣ (μ.rowLen 0 : ℤ) - 1 := by
    rw [hK, Nat.cast_pow]
    exact sub_one_dvd_pow_sub_one (m : ℤ) K
  have htwice := mul_dvd_mul (dvd_refl (2 : ℤ)) hL
  have hh := dvd_add (dvd_trans hd hs) htwice
  convert hh using 1; ring

theorem result : claim := by
  intro m hm hodd s μ hcard hcmp hself
  have hpositive : 0 < μ.cells.card := by
    change 0 < μ.card
    rw [hcard]
    exact pow_pos (by omega) _
  obtain ⟨⟨i, j⟩, hij⟩ := Finset.card_pos.mp hpositive
  have hne : 0 < μ.rowLen 0 := YoungDiagram.mem_iff_lt_rowLen.mp
    (μ.up_left_mem (Nat.zero_le i) (Nat.zero_le j) hij)
  have hN := odd_modulus m μ hodd hcmp hne hself
  have heven : (2 : ℤ) ∣ (m : ℤ) + 1 := by
    exact even_iff_two_dvd.mp (((Int.odd_coe_nat m).mpr hodd).add_odd odd_one)
  have hsq : 2 * ((m : ℤ) - 1) ∣ (m : ℤ) ^ 2 - 1 := by
    convert mul_dvd_mul (dvd_refl ((m : ℤ) - 1)) heven using 1 <;> ring
  have hpower : 2 * ((m : ℤ) - 1) ∣ (m : ℤ) ^ (2 * s + 1) - m := by
    have hh := dvd_trans hsq (sub_one_dvd_pow_sub_one ((m : ℤ) ^ 2) s)
    have hmul := dvd_mul_of_dvd_right hh (m : ℤ)
    have hh' : (m : ℤ) * (((m : ℤ) ^ 2) ^ s - 1) =
        (m : ℤ) ^ (2 * s + 1) - m := by
      rw [pow_add, pow_one, pow_mul]
      ring
    rw [hh'] at hmul
    exact hmul
  rw [hcard, Nat.cast_pow] at hN
  have hbad : 2 * ((m : ℤ) - 1) ∣ (m : ℤ) - 1 := by
    convert dvd_sub hN hpower using 1; ring
  have hpos : 0 < (m : ℤ) - 1 := by omega
  have hle := Int.le_of_dvd hpos hbad
  omega

end D5.S3.Combinatorics.Partitions.OddPowerSelfConjugateCMP
