/- GID: D5/S3/Combinatorics/Partitions/EvenBaseOddPowerSelfConjugateCMP
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/EvenBaseOddPowerSelfConjugateCMP
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The least odd exponent admitting a self-conjugate CMP at an even base. -/

import D5.S3.Combinatorics.Partitions.OddPowerSelfConjugateCMP
import Mathlib.NumberTheory.Multiplicity

/-! Question 5.12 of Dietz, Flowers and Lockard. The square congruence gives the
lower bound, and the diagram of Flowers and Lockard, Lemma 4.2, attains it. -/

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
private theorem lower_bound (m : ℕ) (hm : 2 ≤ m)
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
    convert dvd_sub (dvd_sub heRem (dvd_add hKRem hKRem)) hgeom using 1
    ring
  have hdiv : d ∣ 2 * (K : ℤ) - (e : ℤ) :=
    Int.dvd_of_mul_dvd_mul_left hdPos.ne' (by simpa only [pow_two] using hmultiple)
  have hgapCast : ((2 * K - e : ℕ) : ℤ) = 2 * (K : ℤ) - (e : ℤ) := by
    rw [Nat.cast_sub heK, Nat.cast_mul, Nat.cast_ofNat]
  rw [← hgapCast] at hdiv
  have hle : d ≤ ((2 * K - e : ℕ) : ℤ) :=
    Int.le_of_dvd (by exact_mod_cast hgap.1) hdiv
  dsimp [d] at hle
  omega

private def rectangles (m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (m + 1)).biUnion fun j =>
    Finset.range (m ^ j) ×ˢ Finset.range (m ^ (m - j))

private theorem mem_rectangles (m r c : ℕ) :
    (r, c) ∈ rectangles m ↔ ∃ j ≤ m, r < m ^ j ∧ c < m ^ (m - j) := by
  simp [rectangles]

/-- The diagram of Flowers and Lockard, with row-band boundaries at powers of the base. -/
def publishedDiagram (m : ℕ) : YoungDiagram where
  cells := rectangles m
  isLowerSet := by
    intro b a hab hb
    obtain ⟨j, hj, hr, hc⟩ := (mem_rectangles m b.1 b.2).mp hb
    exact (mem_rectangles m a.1 a.2).mpr
      ⟨j, hj, hab.1.trans_lt hr, hab.2.trans_lt hc⟩

private theorem published_transpose (m : ℕ) :
    (publishedDiagram m).transpose = publishedDiagram m := by
  have swap_mem (r c : ℕ) (h : (r, c) ∈ rectangles m) : (c, r) ∈ rectangles m := by
    obtain ⟨j, hj, hr, hc⟩ := (mem_rectangles m r c).mp h
    apply (mem_rectangles m c r).mpr
    refine ⟨m - j, Nat.sub_le .., hc, ?_⟩
    rwa [show m - (m - j) = j by omega]
  apply SetLike.ext
  intro ⟨r, c⟩
  rw [YoungDiagram.mem_transpose]
  exact ⟨swap_mem c r, swap_mem r c⟩

private theorem mem_first_rectangle {m r c j : ℕ} (hm : 2 ≤ m) (hj : j ≤ m)
    (hr : r < m ^ j) (hfirst : ∀ k < j, m ^ k ≤ r) :
    (r, c) ∈ rectangles m ↔ c < m ^ (m - j) := by
  constructor
  · intro h
    obtain ⟨k, _, hrk, hck⟩ := (mem_rectangles m r c).mp h
    have hjk : j ≤ k := by
      by_contra! hkj
      exact (not_lt_of_ge (hfirst k hkj)) hrk
    have hpow : Monotone (fun n : ℕ => m ^ n) := (pow_right_strictMono₀ hm).monotone
    exact hck.trans_le (hpow (by omega))
  · intro hc
    exact (mem_rectangles m r c).mpr ⟨j, hj, hr, hc⟩

private theorem first_eligible (m r c : ℕ) (h : (r, c) ∈ rectangles m) :
    ∃ j ≤ m, r < m ^ j ∧ ∀ k < j, m ^ k ≤ r := by
  obtain ⟨k, hk, hr, _⟩ := (mem_rectangles m r c).mp h
  have hex : ∃ j, r < m ^ j := ⟨k, hr⟩
  exact ⟨Nat.find hex, (Nat.find_min' hex hr).trans hk, Nat.find_spec hex,
    fun i hi => Nat.le_of_not_gt (Nat.find_min hex hi)⟩

private theorem published_mary (m : ℕ) (hm : 2 ≤ m) : IsMAry m (publishedDiagram m) := by
  intro r hpos
  have hcell : (r, 0) ∈ publishedDiagram m := YoungDiagram.mem_iff_lt_rowLen.mpr hpos
  obtain ⟨j, hj, hr, hfirst⟩ := first_eligible m r 0 hcell
  exact ⟨m - j, eq_of_forall_lt_iff fun c =>
    YoungDiagram.mem_iff_lt_rowLen.symm.trans (mem_first_rectangle hm hj hr hfirst)⟩

private def rowBand (m k : ℕ) : Finset (ℕ × ℕ) :=
  Finset.Ico (m ^ k) (m ^ (k + 1)) ×ˢ Finset.range (m ^ (m - (k + 1)))

private theorem rectangles_eq_bands (m : ℕ) (hm : 2 ≤ m) :
    rectangles m = ({0} ×ˢ Finset.range (m ^ m)) ∪
      (Finset.range m).biUnion (rowBand m) := by
  ext ⟨r, c⟩
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_product,
    Finset.mem_singleton, Finset.mem_range, rowBand, Finset.mem_Ico]
  constructor
  · intro h
    obtain ⟨j, hj, hr, hfirst⟩ := first_eligible m r c h
    have hc := (mem_first_rectangle hm hj hr hfirst).mp h
    cases j with
    | zero =>
      rw [pow_zero] at hr
      exact Or.inl ⟨by omega, by simpa only [Nat.sub_zero] using hc⟩
    | succ j =>
      exact Or.inr ⟨j, by omega, ⟨hfirst j (Nat.lt_succ_self j), hr⟩, hc⟩
  · rintro (⟨rfl, hc⟩ | ⟨j, hj, ⟨_, hr⟩, hc⟩)
    · exact (mem_rectangles m 0 c).mpr ⟨0, Nat.zero_le m, by simp, by simpa using hc⟩
    · exact (mem_rectangles m r c).mpr ⟨j + 1, by omega, hr, hc⟩

private theorem published_card (m : ℕ) (hm : 2 ≤ m) :
    (publishedDiagram m).card = m ^ (m + 1) := by
  have hmono : Monotone (fun n : ℕ => m ^ n) := (pow_right_strictMono₀ hm).monotone
  have hdisj : (↑(Finset.range m) : Set ℕ).PairwiseDisjoint (rowBand m) := by
    intro i _ j _ hij
    have band_disjoint (a b : ℕ) (hab : a < b) :
        Disjoint (rowBand m a) (rowBand m b) := by
      rw [Finset.disjoint_left]
      intro ⟨r, c⟩ ha hb
      simp only [rowBand, Finset.mem_product, Finset.mem_Ico] at ha hb
      exact (not_lt_of_ge ((hmono hab).trans hb.1.1)) ha.1.2
    rcases lt_or_gt_of_ne hij with h | h
    · exact band_disjoint i j h
    · exact (band_disjoint j i h).symm
  have htop : Disjoint ({0} ×ˢ Finset.range (m ^ m))
      ((Finset.range m).biUnion (rowBand m)) := by
    rw [Finset.disjoint_left]
    intro ⟨r, c⟩ hr hband
    simp only [Finset.mem_product, Finset.mem_singleton] at hr
    obtain ⟨rfl, _⟩ := hr
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hband
    simp only [rowBand, Finset.mem_product, Finset.mem_Ico] at hj
    exact (Nat.not_le_of_gt (pow_pos (by omega : 0 < m) j)) hj.1.1
  have hband (j : ℕ) (hj : j ∈ Finset.range m) :
      (rowBand m j).card = m ^ m - m ^ (m - 1) := by
    have hjm := Finset.mem_range.mp hj
    rw [rowBand, Finset.card_product, Nat.card_Ico, Finset.card_range,
      Nat.sub_mul, ← pow_add, ← pow_add]
    rw [show j + 1 + (m - (j + 1)) = m by omega,
      show j + (m - (j + 1)) = m - 1 by omega]
  change (rectangles m).card = _
  rw [rectangles_eq_bands m hm, Finset.card_union_of_disjoint htop, Finset.card_biUnion hdisj,
    Finset.card_product, Finset.card_singleton, Finset.card_range, one_mul,
    Finset.sum_congr rfl hband, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  change m ^ m + m * (m ^ m - m ^ (m - 1)) = _
  rw [Nat.mul_sub_left_distrib, ← pow_succ', ← pow_succ', show (m - 1) + 1 = m by omega]
  exact Nat.add_sub_of_le (hmono (Nat.le_succ m))

/-- For each even base at least two, Question 5.12 has minimum exponent `m + 1`. -/
theorem result (m : ℕ) (hm : 2 ≤ m) (hmEven : Even m) :
    IsLeast {e : ℕ | Odd e ∧ ∃ μ : YoungDiagram,
      μ.card = m ^ e ∧ IsCMP m μ ∧ μ.transpose = μ} (m + 1) := by
  have hself := published_transpose m
  have hmary := published_mary m hm
  refine ⟨⟨hmEven.add_odd odd_one, publishedDiagram m, published_card m hm, ⟨hmary, ?_⟩, hself⟩, ?_⟩
  · simpa only [hself] using hmary
  · rintro e ⟨he, μ, hcard, hcmp, htranspose⟩
    exact lower_bound m hm e he μ hcard hcmp htranspose

end D5.S3.Combinatorics.Partitions.EvenBaseOddPowerSelfConjugateCMP
