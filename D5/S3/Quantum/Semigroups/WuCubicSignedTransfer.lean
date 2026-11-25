/- GID: D5/S3/Quantum/Semigroups/WuCubicSignedTransfer
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicSignedTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Wu's signed cubic transfer and two physical squares for a raised middle level. -/

import D5.S3.Quantum.Semigroups.WuOneModeCubic
import D5.S3.Quantum.Semigroups.WuPhysicalHighHigh
import Batteries.Tactic.OpenPrivate

/-! The signed cubic transfer for Wu v1, Remark 3.15 (3.54).
The spectra `(m, n, n, 1)` and `(m, n, q, 1)` use the same frame.
Rows are targets and columns are sources. -/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators Matrix

namespace D5.S3.Quantum.Semigroups.WuCubicSignedTransfer

open WuRepeatedMiddleCubic (Frame alpha imbalance weight sourceDeficit
  holder21 holder12 frameRemainder repeated_middle_lower_bound)
open private gamma h c e bias beta gibbsLow gibbsHigh kernel total levels
  energyKernel energy_centering gibbsLogColumn gibbs_log_column row_weight col_weight from
  D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic

private def levelsAt (m n z : ℝ) : Fin 4 → ℝ := ![m, n, z, 1]
private def totalAt (m n z : ℝ) : ℝ := m^3 + n^3 + z^3 + 1

/-- The normalized source deficit, with the third level set to `z`. -/
def sourceDeficitAt (r : ℝ) (U : Frame) (m n z : ℝ) : ℝ :=
  (∑ i, ∑ j, weight U i j * energyKernel r (levelsAt m n z i) (levelsAt m n z j)) -
    alpha r * (m^3 * Real.log (m^3) + n^3 * Real.log (n^3) + z^3 * Real.log (z^3) -
      totalAt m n z * Real.log (totalAt m n z) -
        ∑ i, gibbsLogColumn r U i * levelsAt m n z i ^ 3)

private def cubic (C E v w : ℝ) : ℝ :=
  C * (v - w)^2 * (v + w) + E * (v - w)^3

/-- Exact scalar change, including the signed marginal bias at column 2. -/
def scalarIncrement (r : ℝ) (U : Frame) (m n q : ℝ) : ℝ :=
  (h r + bias r * imbalance U 2) * (q^3 - n^3) +
    alpha r * (totalAt m n q * Real.log (totalAt m n q / 4) -
      totalAt m n n * Real.log (totalAt m n n / 4) -
        (q^3 * Real.log (q^3) - n^3 * Real.log (n^3)))

/-- Four cubic gains between the raised column and columns 0 and 1. -/
def lowerIncrement (r : ℝ) (U : Frame) (m n q : ℝ) : ℝ :=
  weight U 2 0 * (cubic (c r) (e r) q m - cubic (c r) (e r) n m) +
  weight U 0 2 * (cubic (c r) (e r) m q - cubic (c r) (e r) m n) +
  weight U 2 1 * (cubic (c r) (e r) q n - cubic (c r) (e r) n n) +
  weight U 1 2 * (cubic (c r) (e r) n q - cubic (c r) (e r) n n)

/-- The coefficient of the loss on the top target row and raised source column. -/
def lossPlus (r n q : ℝ) : ℝ := cubic (c r) (e r) 1 n - cubic (c r) (e r) 1 q

/-- The coefficient of the loss on the raised target row and top source column. -/
def lossMinus (r n q : ℝ) : ℝ := cubic (c r) (e r) n 1 - cubic (c r) (e r) q 1

private theorem cubic_swap (C E v w : ℝ) : cubic C E v w = cubic C (-E) w v := by
  unfold cubic
  ring

private theorem cubic_raise_upper {C E x n q : ℝ}
    (hC : 0 ≤ C) (hCE : 0 ≤ C + E)
    (hx : 0 ≤ x) (hxn : x ≤ n) (hnq : n ≤ q) :
    0 ≤ cubic C E q x - cubic C E n x := by
  have hn := sub_nonneg.mpr hxn
  have hq := sub_nonneg.mpr (hxn.trans hnq)
  have hd := sub_nonneg.mpr hnq
  calc
    0 ≤ (q - n) * (2 * C * x * ((q - x) + (n - x)) +
        (C + E) * ((q - x)^2 + (q - x) * (n - x) + (n - x)^2)) := by positivity
    _ = _ := by unfold cubic; ring

private theorem cubic_raise_lower {C E n q t : ℝ}
    (hC : 0 ≤ C) (hCE : 0 ≤ C + E) (hC3E : 0 ≤ C + 3 * E)
    (hn : 0 ≤ n) (hnq : n ≤ q) (hqt : q ≤ t) :
    0 ≤ cubic C E t n - cubic C E t q := by
  have ha := sub_nonneg.mpr hqt
  have hd := sub_nonneg.mpr hnq
  calc
    0 ≤ (q - n) * ((C + 3 * E) * (t - q)^2 +
        (C + E) * (q - n) * (3 * (t - q) + (q - n)) +
        2 * C * n * (2 * (t - q) + (q - n))) := by positivity
    _ = _ := by unfold cubic; ring

private theorem energy_entry {r : ℝ} (hr : 1 ≤ r) (W v w : ℝ) :
    W * energyKernel r v w =
      W * cubic (c r) (e r) v w +
      (gamma r * (r - 1)^2 * (r + 1) + alpha r * beta r + bias r) / 2 * (W * v^3) +
      (gamma r * (r - 1)^2 * (r + 1) - alpha r * beta r - bias r) / 2 * (W * w^3) := by
  have hentry := energy_centering hr v w W
  unfold kernel at hentry
  unfold cubic
  linear_combination hentry

private theorem source_centered_at {r : ℝ} (hr : 1 ≤ r)
    (U : Frame) (hU : Uᴴ * U = 1) (hUU : U * Uᴴ = 1)
    {m n z : ℝ} (hm : 0 ≤ m) (hn : 0 ≤ n) (hz : 0 ≤ z) :
    sourceDeficitAt r U m n z =
      h r * totalAt m n z +
      alpha r * (totalAt m n z * Real.log (totalAt m n z / 4) -
        m^3 * Real.log (m^3) - n^3 * Real.log (n^3) - z^3 * Real.log (z^3)) +
      (∑ i, ∑ j, weight U i j * cubic (c r) (e r) (levelsAt m n z i) (levelsAt m n z j)) +
      bias r * (imbalance U 0 * m^3 + imbalance U 1 * n^3 +
        imbalance U 2 * z^3 + imbalance U 3) := by
  have hrow : (∑ i, ∑ j, weight U i j * levelsAt m n z i ^ 3) =
      ∑ i, (1 + imbalance U i) * levelsAt m n z i ^ 3 := by
    simp_rw [← Finset.sum_mul, row_weight U hU hUU]
  have hcol : (∑ i, ∑ j, weight U i j * levelsAt m n z j ^ 3) =
      ∑ j, (1 - imbalance U j) * levelsAt m n z j ^ 3 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, col_weight U hU hUU]
  have ht : totalAt m n z ≠ 0 := by unfold totalAt; positivity
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hab : gibbsLow r * gibbsHigh r ≠ 0 := by unfold gibbsHigh gibbsLow; positivity
  have hlog : Real.log (4 * gibbsLow r * gibbsHigh r) =
      Real.log 4 + Real.log (gibbsLow r * gibbsHigh r) := by
    rw [mul_assoc, Real.log_mul (by norm_num) hab]
  unfold sourceDeficitAt
  simp_rw [energy_entry hr, Finset.sum_add_distrib, ← Finset.mul_sum, hrow, hcol,
    gibbs_log_column hr U hU]
  rw [h, hlog, Real.log_div ht (by norm_num)]
  simp [Fin.sum_univ_four, levelsAt, totalAt]
  ring

/-- The exact signed transfer, with both physical directions kept as literal weights. -/
theorem signed_increment {r : ℝ} (hr : 1 ≤ r)
    (U : Frame) (hU : Uᴴ * U = 1) (hUU : U * Uᴴ = 1)
    {m n q : ℝ} (hm : 0 ≤ m) (hmn : m ≤ n) (hnq : n ≤ q) (hq1 : q ≤ 1) :
    (sourceDeficitAt r U m n q - sourceDeficit r U m n =
      scalarIncrement r U m n q + lowerIncrement r U m n q -
        (lossPlus r n q * weight U 3 2 + lossMinus r n q * weight U 2 3)) ∧
      0 ≤ lowerIncrement r U m n q ∧ 0 ≤ lossPlus r n q ∧ 0 ≤ lossMinus r n q := by
  have hn := hm.trans hmn
  have hq := hn.trans hnq
  refine ⟨?_, ?_⟩
  · have hbase : sourceDeficitAt r U m n n = sourceDeficit r U m n := by
      simp only [sourceDeficitAt, sourceDeficit, levelsAt, levels, totalAt, total]
      ring
    have hdiag (x : ℝ) : cubic (c r) (e r) x x = 0 := by simp [cubic]
    rw [← hbase, source_centered_at hr U hU hUU hm hn hq,
      source_centered_at hr U hU hUU hm hn hn]
    simp [Fin.sum_univ_four, levelsAt, hdiag, scalarIncrement, lowerIncrement,
      lossPlus, lossMinus, totalAt]
    ring
  · have hr0 : 0 ≤ r := zero_le_one.trans hr
    have hrt : 0 ≤ r - 1 := sub_nonneg.mpr hr
    have hc : 0 ≤ c r := by unfold c gamma; positivity
    have he : 0 ≤ e r := by unfold e gamma; positivity
    have hp3 : 0 ≤ c r + 3 * e r := by positivity
    have hm3 : 0 ≤ c r + 3 * (-e r) := by
      rw [show c r + 3 * (-e r) = gamma r * r by unfold c e; ring]
      unfold gamma
      positivity
    have hp : 0 ≤ c r + e r := add_nonneg hc he
    have hm' : 0 ≤ c r + (-e r) := by linarith only [hc, hm3]
    have hW (i j : Fin 4) : 0 ≤ weight U i j :=
      Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
    have hrev (x : ℝ) (hx : 0 ≤ x) (hxn : x ≤ n) :
        0 ≤ cubic (c r) (e r) x q - cubic (c r) (e r) x n := by
      rw [cubic_swap (c r) (e r) x q, cubic_swap (c r) (e r) x n]
      exact cubic_raise_upper hc hm' hx hxn hnq
    refine ⟨?_, cubic_raise_lower hc hp hp3 hn hnq hq1, ?_⟩
    · unfold lowerIncrement
      exact add_nonneg (add_nonneg (add_nonneg
        (mul_nonneg (hW 2 0) (cubic_raise_upper hc hp hm hmn hnq))
        (mul_nonneg (hW 0 2) (hrev m hm hmn)))
        (mul_nonneg (hW 2 1) (cubic_raise_upper hc hp hn le_rfl hnq)))
        (mul_nonneg (hW 1 2) (hrev n hn le_rfl))
    · rw [lossMinus, cubic_swap (c r) (e r) n 1, cubic_swap (c r) (e r) q 1]
      exact cubic_raise_lower hc hm' hm3 hn hnq hq1

private theorem column_pairing (U : Frame) (i j : Fin 4) :
    WuPhysicalHighHigh.pairing (U.col i) (U.col j) = (Uᴴ * U) i j := by
  simp only [WuPhysicalHighHigh.pairing, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.col_def, Matrix.transpose_apply, Pi.star_apply]

private theorem column_weight (U : Frame) (i j : Fin 4) :
    weight U i j = WuPhysicalHighHigh.weight (U.col i) (U.col j) := by
  unfold weight WuPhysicalHighHigh.weight
  apply Finset.sum_congr rfl
  intro k _
  rw [WuPhysicalHighHigh.pairing, Matrix.mul_assoc]
  rfl

/-- The measured repeated-middle bound transferred to `q`, keeping both physical squares. -/
theorem raised_lower_bound {r : ℝ} (hr : 1 ≤ r)
    (U : Frame) (hU : Uᴴ * U = 1) (hUU : U * Uᴴ = 1)
    {m n q : ℝ} (hm : 0 ≤ m) (hmn : m ≤ n) (hnq : n ≤ q) (hq1 : q ≤ 1) :
    let u := U.col 3
    let v := U.col 2
    let dp := lossPlus r n q
    let dm := lossMinus r n q
    let A := (dp + dm) / 2
    let rho := (dp - dm) / (dp + dm)
    gamma r * r * holder21 m n + gamma r * r^2 * holder12 m n + frameRemainder r U m n +
      scalarIncrement r U m n q + lowerIncrement r U m n q -
      A * (1 + rho * WuPhysicalHighHigh.imbalance u) * (1 - rho * WuPhysicalHighHigh.imbalance v) +
      A * ((2 - rho^2) / 4) * Complex.normSq (WuPhysicalHighHigh.eta u v) +
      A * Complex.normSq (WuPhysicalHighHigh.sigma u v + (rho : ℂ) * WuPhysicalHighHigh.tau u v) ≤
        sourceDeficitAt r U m n q := by
  dsimp only
  obtain ⟨hinc, _, hdp, hdm⟩ := signed_increment hr U hU hUU hm hmn hnq hq1
  have hrep := (repeated_middle_lower_bound hr (WuOneModeCubic.one_mode_bound hr)
    U hU hUU hm hmn (hnq.trans hq1)).2.2
  have hu : WuPhysicalHighHigh.pairing (U.col 3) (U.col 3) = 1 := by
    rw [column_pairing, hU, Matrix.one_apply_eq]
  have hv : WuPhysicalHighHigh.pairing (U.col 2) (U.col 2) = 1 := by
    rw [column_pairing, hU, Matrix.one_apply_eq]
  have huv : WuPhysicalHighHigh.pairing (U.col 3) (U.col 2) = 0 := by
    rw [column_pairing, hU, Matrix.one_apply_ne (by decide : (3 : Fin 4) ≠ 2)]
  have hp := (WuPhysicalHighHigh.weighted_high_high _ _ hu hv huv _ _ hdp hdm).1
  rw [column_weight U 3 2, column_weight U 2 3, hp] at hinc
  linear_combination hrep - hinc

open WuRepeatedMiddleCubic (blockRoot)
open private blockRoot_cube holder_gaps from
  D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic

private theorem le_gap_of_cube_gap {x y b k : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x)
    (hxb : x ≤ b) (hb : 0 < b) (hcube : 3 * b ^ 2 * k ≤ x ^ 3 - y ^ 3) :
    k ≤ x - y := by
  have hx := hy.trans hyx
  have hyb := hyx.trans hxb
  have hsum : x ^ 2 + x * y + y ^ 2 ≤ 3 * b ^ 2 := calc
    _ ≤ b ^ 2 + b * b + b ^ 2 :=
      add_le_add (add_le_add (pow_le_pow_left₀ hx hxb 2)
        (mul_le_mul hxb hyb hy (hx.trans hxb))) (pow_le_pow_left₀ hy hyb 2)
    _ = _ := by ring
  apply (mul_le_mul_iff_right₀ (show 0 < 3 * b ^ 2 by positivity)).mp
  calc
    3 * b ^ 2 * k ≤ x ^ 3 - y ^ 3 := hcube
    _ = (x ^ 2 + x * y + y ^ 2) * (x - y) := by ring
    _ ≤ 3 * b ^ 2 * (x - y) := mul_le_mul_of_nonneg_right hsum (sub_nonneg.mpr hyx)

private theorem holder_gaps_quantitative {m n : ℝ}
    (hmlo : 23 / 50 ≤ m) (hmhi : m ≤ 1 / 2)
    (hnlo : 9 / 10 ≤ n) (hnhi : n ≤ 23 / 25) :
    (40 / 81 : ℝ) * (m - n ^ 2) ^ 2 ≤ holder21 m n ∧
    (35 / 108 : ℝ) * (m - n ^ 2) ^ 2 ≤ holder12 m n := by
  have hm : 0 ≤ m := (by norm_num : (0 : ℝ) ≤ 23 / 50).trans hmlo
  have hn : 0 ≤ n := (by norm_num : (0 : ℝ) ≤ 9 / 10).trans hnlo
  let A := blockRoot m n
  let B := blockRoot n 1
  have hA : A ^ 3 = m ^ 3 + n ^ 3 := blockRoot_cube hm hn
  have hB : B ^ 3 = n ^ 3 + 1 := by simpa only [one_pow] using blockRoot_cube hn zero_le_one
  have hc21 : (A * B ^ 2) ^ 3 = (m ^ 3 + n ^ 3) * (n ^ 3 + 1) ^ 2 := by
    rw [mul_pow, pow_right_comm B 2 3, hA, hB]
  have hc12 : (A ^ 2 * B) ^ 3 = (m ^ 3 + n ^ 3) ^ 2 * (n ^ 3 + 1) := by
    rw [mul_pow, pow_right_comm A 2 3, hA, hB]
  obtain ⟨hg21, hg12⟩ := holder_gaps hm hn
  have hy21 : 0 ≤ m * n ^ 2 + n := by positivity
  have hy12 : 0 ≤ m ^ 2 * n + n ^ 2 := by positivity
  have hyx21 : m * n ^ 2 + n ≤ A * B ^ 2 := sub_nonneg.mp hg21
  have hyx12 : m ^ 2 * n + n ^ 2 ≤ A ^ 2 * B := sub_nonneg.mp hg12
  have hb21 : A * B ^ 2 ≤ (3 / 2 : ℝ) := by
    apply (pow_le_pow_iff_left₀ (hy21.trans hyx21) (by norm_num) (by decide : 3 ≠ (0 : ℕ))).mp
    rw [hc21]
    calc
      _ ≤ ((1 / 2 : ℝ) ^ 3 + (23 / 25 : ℝ) ^ 3) * ((23 / 25 : ℝ) ^ 3 + 1) ^ 2 := by gcongr
      _ ≤ _ := by norm_num
  have hb12 : A ^ 2 * B ≤ (6 / 5 : ℝ) := by
    apply (pow_le_pow_iff_left₀ (hy12.trans hyx12) (by norm_num) (by decide : 3 ≠ (0 : ℕ))).mp
    rw [hc12]
    calc
      _ ≤ ((1 / 2 : ℝ) ^ 3 + (23 / 25 : ℝ) ^ 3) ^ 2 * ((23 / 25 : ℝ) ^ 3 + 1) := by gcongr
      _ ≤ _ := by norm_num
  have hF21 : (10 / 3 : ℝ) ≤ 2 * m * n ^ 3 + m + n ^ 5 + 2 * n ^ 2 := calc
    _ ≤ 2 * (23 / 50 : ℝ) * (9 / 10 : ℝ) ^ 3 + 23 / 50 + (9 / 10 : ℝ) ^ 5 +
        2 * (9 / 10 : ℝ) ^ 2 := by norm_num
    _ ≤ _ := by gcongr
  have hF12 : (7 / 5 : ℝ) ≤ m ^ 4 + 2 * m ^ 3 * n ^ 2 + 2 * m * n ^ 3 + n ^ 5 := calc
    _ ≤ (23 / 50 : ℝ) ^ 4 + 2 * (23 / 50 : ℝ) ^ 3 * (9 / 10 : ℝ) ^ 2 +
        2 * (23 / 50 : ℝ) * (9 / 10 : ℝ) ^ 3 + (9 / 10 : ℝ) ^ 5 := by norm_num
    _ ≤ _ := by gcongr
  unfold holder21 holder12
  constructor
  · apply le_gap_of_cube_gap hy21 hyx21 hb21 (by norm_num)
    calc
      _ = (m - n ^ 2) ^ 2 * (10 / 3 : ℝ) := by ring
      _ ≤ (m - n ^ 2) ^ 2 * (2 * m * n ^ 3 + m + n ^ 5 + 2 * n ^ 2) :=
        mul_le_mul_of_nonneg_left hF21 (sq_nonneg _)
      _ = _ := by rw [hc21]; ring
  · apply le_gap_of_cube_gap hy12 hyx12 hb12 (by norm_num)
    calc
      _ = (m - n ^ 2) ^ 2 * (7 / 5 : ℝ) := by ring
      _ ≤ (m - n ^ 2) ^ 2 * (m ^ 4 + 2 * m ^ 3 * n ^ 2 + 2 * m * n ^ 3 + n ^ 5) :=
        mul_le_mul_of_nonneg_left hF12 (sq_nonneg _)
      _ = _ := by rw [hc12]; ring

private theorem weighted_holder_gaps_quantitative {r m n : ℝ}
    (hrlo : 6 / 5 ≤ r) (hrhi : r ≤ 5 / 4)
    (hmlo : 23 / 50 ≤ m) (hmhi : m ≤ 1 / 2)
    (hnlo : 9 / 10 ≤ n) (hnhi : n ≤ 23 / 25) :
    (79763 / 1080000 : ℝ) ≤ gamma r * r * holder21 m n + gamma r * r ^ 2 * holder12 m n := by
  have hr : 0 ≤ r := (by norm_num : (0 : ℝ) ≤ 6 / 5).trans hrlo
  have hden : 0 < 4 * (1 + r ^ 3) := by positivity
  have hdenle : 4 * (1 + r ^ 3) ≤ 4 * (1 + (5 / 4 : ℝ) ^ 3) := by gcongr
  have hgr : (9 / 10 : ℝ) ≤ gamma r * r := by
    rw [gamma, div_mul_eq_mul_div, le_div_iff₀ hden]
    linarith only [hdenle, hrlo]
  have hgr2 : 1 ≤ gamma r * r ^ 2 := by
    rw [gamma, div_mul_eq_mul_div, le_div_iff₀ hden]
    have hrsq := pow_le_pow_left₀ (show (0 : ℝ) ≤ 6 / 5 by norm_num) hrlo 2
    linarith only [hdenle, hrsq]
  have hn2 := pow_le_pow_left₀ (show (0 : ℝ) ≤ 9 / 10 by norm_num) hnlo 2
  have hd : (31 / 100 : ℝ) ≤ n ^ 2 - m := by linarith only [hn2, hmhi]
  have hds : (31 / 100 : ℝ) ^ 2 ≤ (m - n ^ 2) ^ 2 := calc
    _ ≤ (n ^ 2 - m) ^ 2 := pow_le_pow_left₀ (by norm_num) hd 2
    _ = _ := by ring
  obtain ⟨hg21, hg12⟩ := holder_gaps_quantitative hmlo hmhi hnlo hnhi
  calc
    _ = (83 / 108 : ℝ) * (31 / 100) ^ 2 := by norm_num
    _ ≤ (83 / 108 : ℝ) * (m - n ^ 2) ^ 2 := mul_le_mul_of_nonneg_left hds (by norm_num)
    _ = (9 / 10 : ℝ) * ((40 / 81) * (m - n ^ 2) ^ 2) + 1 * ((35 / 108) * (m - n ^ 2) ^ 2) := by ring
    _ ≤ _ := add_le_add
      (mul_le_mul hgr hg21 (by positivity) ((by norm_num : (0 : ℝ) ≤ 9 / 10).trans hgr))
      (mul_le_mul hgr2 hg12 (by positivity) (zero_le_one.trans hgr2))

private theorem log_lower {r : ℝ} (hr : 1 ≤ r) :
    2 * (r - 1) / (r + 1) ≤ Real.log r := by
  let f (x : ℝ) := Real.log x - 2 * (x - 1) / (x + 1)
  have hd (x : ℝ) (hx : x ∈ Set.Ici (1 : ℝ)) :
      HasDerivAt f ((x - 1) ^ 2 / (x * (x + 1) ^ 2)) x := by
    have hx0 : 0 < x := zero_lt_one.trans_le hx
    have hx1 : 0 < x + 1 := by positivity
    have hid := hasDerivAt_id x
    have hquot := ((hid.sub_const 1).const_mul 2).div (hid.add_const 1) hx1.ne'
    convert (Real.hasDerivAt_log hx0.ne').sub hquot using 1
    · rfl
    · simp only [id_eq]
      field_simp [hx0.ne', hx1.ne']
      ring
  have hmono : MonotoneOn f (Set.Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Set.Ici (1 : ℝ) := interior_subset hx
      have hx0 : 0 < x := zero_lt_one.trans_le hx'
      rw [(hd x hx').deriv]
      positivity
  have h1 : f 1 = 0 := by norm_num [f]
  have hfr := hmono (Set.mem_Ici.mpr (le_refl (1 : ℝ))) (Set.mem_Ici.mpr hr) hr
  rw [h1] at hfr
  exact sub_nonneg.mp hfr

private theorem alpha_bounds {r : ℝ} (hr : 1 < r) : 0 ≤ alpha r ∧ alpha r ≤ 1 / 2 := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  have ht : 0 < r - 1 := sub_pos.mpr hr
  have hlog : 0 < Real.log r := Real.log_pos hr
  have hlogLower := log_lower hr.le
  have hquad : 3 * (r + 1) ^ 2 ≤ 4 * (r ^ 2 + r + 1) := by
    nlinarith only [sq_nonneg (r - 1)]
  simp only [alpha, hr.ne', ↓reduceIte]
  have hden : 0 < 4 * (r ^ 2 + r + 1) * Real.log r := by positivity
  constructor
  · apply div_nonneg _ hden.le
    nlinarith only [mul_nonneg ht.le (show 0 ≤ r + 1 by positivity)]
  · apply (div_le_iff₀ hden).2
    calc
      _ = (3 * (r + 1) ^ 2) * (2 * (r - 1) / (r + 1)) / 2 := by
        field_simp
        ring
      _ ≤ (4 * (r ^ 2 + r + 1)) * Real.log r / 2 :=
        div_le_div_of_nonneg_right (mul_le_mul hquad hlogLower (by positivity) (by positivity))
          (by norm_num)
      _ = _ := by ring

private theorem h_nonneg_on_rectangle {r : ℝ} (hrlo : 6 / 5 ≤ r) (hrhi : r ≤ 5 / 4)
    (ha0 : 0 ≤ alpha r) (ha : alpha r ≤ 1 / 2) : 0 ≤ h r := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hrlo
  have hden : 0 < 1 + r ^ 3 := by positivity
  let g := 4 * gibbsLow r * gibbsHigh r
  have hg : 0 < g := by dsimp [g, gibbsLow, gibbsHigh]; positivity
  have hinv : g⁻¹ - 1 = (r - 1) ^ 2 * ((r ^ 2 + r + 1) ^ 2 / (4 * r ^ 3)) := by
    dsimp [g, gibbsLow, gibbsHigh]
    field_simp [hr0.ne', hden.ne']
    ring
  have hlog : -(g⁻¹ - 1) ≤ Real.log g := by
    have hlogInv := Real.log_le_sub_one_of_pos (inv_pos.mpr hg)
    rw [Real.log_inv] at hlogInv
    linarith only [hlogInv]
  have hneg : -(g⁻¹ - 1) ≤ 0 := by rw [hinv]; exact neg_nonpos.mpr (by positivity)
  have hγ : (16 / 21 : ℝ) ≤ gamma r := by
    rw [gamma, le_div_iff₀ (show 0 < 4 * (1 + r ^ 3) by positivity)]
    have hcub := pow_le_pow_left₀ hr0.le hrhi 3
    linarith only [hcub]
  have hγr : (16 / 21 : ℝ) * (11 / 5) ≤ gamma r * (r + 1) :=
    mul_le_mul hγ (by linarith only [hrlo]) (by norm_num) (by unfold gamma; positivity)
  have hquot : (r ^ 2 + r + 1) ^ 2 / (8 * r ^ 3) ≤
      (61 / 16 : ℝ) ^ 2 / (8 * (6 / 5 : ℝ) ^ 3) := by
    have hquad : r ^ 2 + r + 1 ≤ (61 / 16 : ℝ) := by
      have hr2 := pow_le_pow_left₀ hr0.le hrhi 2
      linarith only [hrhi, hr2]
    calc
      _ ≤ (61 / 16 : ℝ) ^ 2 / (8 * r ^ 3) :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hquad 2) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by norm_num) (by gcongr)
  have hbracket : 0 ≤ gamma r * (r + 1) - (r ^ 2 + r + 1) ^ 2 / (8 * r ^ 3) := by
    linarith only [hγr, hquot]
  change 0 ≤ gamma r * (r - 1) ^ 2 * (r + 1) + alpha r * Real.log g
  calc
    _ ≤ (r - 1) ^ 2 * (gamma r * (r + 1) - (r ^ 2 + r + 1) ^ 2 / (8 * r ^ 3)) :=
      mul_nonneg (sq_nonneg _) hbracket
    _ = gamma r * (r - 1) ^ 2 * (r + 1) + (1 / 2 : ℝ) * (-(g⁻¹ - 1)) := by
      rw [hinv]
      ring
    _ ≤ _ := add_le_add_right
      ((mul_le_mul_of_nonpos_right ha hneg).trans (mul_le_mul_of_nonneg_left hlog ha0)) _

private theorem bias_bounds {r : ℝ} (hr : 1 ≤ r) (hrhi : r ≤ 5 / 4) :
    0 ≤ bias r ∧ bias r ≤ 3 / 8 := by
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have ht : 0 ≤ r - 1 := sub_nonneg.mpr hr
  have hden : 0 < 1 + r ^ 3 := by positivity
  have hpoly : 0 ≤ r ^ 5 + r ^ 4 - 3 * r ^ 2 + 1 := by
    rw [show r ^ 5 + r ^ 4 - 3 * r ^ 2 + 1 =
      (r - 1) * ((r - 1) ^ 4 + 6 * (r - 1) ^ 3 + 14 * (r - 1) ^ 2 + 13 * (r - 1) + 3) by ring]
    positivity
  refine ⟨by unfold bias gamma; positivity, ?_⟩
  have hb : bias r ≤ 3 * (r - 1) / 2 := by
    rw [bias, div_le_iff₀ (show 0 < 3 * (r ^ 2 + r + 1) by positivity)]
    apply sub_nonneg.mp
    rw [show (3 * (r - 1) / 2) * (3 * (r ^ 2 + r + 1)) -
      2 * gamma r * r * (r - 1) * (r ^ 2 + 4 * r + 1) =
      9 * (r - 1) * (r ^ 5 + r ^ 4 - 3 * r ^ 2 + 1) / (2 * (1 + r ^ 3)) by
        unfold gamma
        field_simp [hden.ne']
        ring]
    positivity
  linarith only [hb, hrhi]

private theorem cubic_coefficient_bounds {r : ℝ} (hr : 1 ≤ r) (hrhi : r ≤ 5 / 4) :
    0 ≤ c r ∧ c r ≤ 9 / 8 ∧ 0 ≤ e r ∧ e r ≤ 3 / 64 := by
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have ht : 0 ≤ r - 1 := sub_nonneg.mpr hr
  have hden : 0 < 1 + r ^ 3 := by positivity
  have hcr : r * (r + 1) ≤ 1 + r ^ 3 := by
    nlinarith only [mul_nonneg (sq_nonneg (r - 1)) (show 0 ≤ r + 1 by positivity)]
  have her : 2 * r ≤ 1 + r ^ 3 := by
    have hr2 := pow_le_pow_left₀ zero_le_one hr 2
    nlinarith only [mul_nonneg ht (show 0 ≤ r ^ 2 + r - 1 by linarith only [hr2, hr])]
  refine ⟨by unfold c gamma; positivity, ?_, by unfold e gamma; positivity, ?_⟩
  · have hc : c r = (9 / 8 : ℝ) * (r * (r + 1) / (1 + r ^ 3)) := by
      unfold c gamma
      field_simp [hden.ne']
      ring
    rw [hc]
    have hc' := (div_le_one hden).2 hcr
    linarith only [hc']
  · have he : e r = (3 / 8 : ℝ) * (r / (1 + r ^ 3)) * (r - 1) := by
      unfold e gamma
      field_simp [hden.ne']
      ring
    rw [he]
    have he' : r / (1 + r ^ 3) ≤ 1 / 2 := (div_le_iff₀ hden).2 (by linarith only [her])
    calc
      _ ≤ (3 / 8 : ℝ) * (1 / 2) * (r - 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he' (by norm_num)) ht
      _ ≤ _ := by linarith only [hrhi]

private theorem entropy_mass_gain {S x y : ℝ} (hS : 1 ≤ S) (hx : 0 < x)
    (hxy : x ≤ y) (hy : y ≤ 1) :
    -(3 / 4 : ℝ) * (y - x) ≤
      ((S + y) * Real.log ((S + y) / 4) - y * Real.log y) -
        ((S + x) * Real.log ((S + x) / 4) - x * Real.log x) := by
  let F (z : ℝ) := (S + z) * Real.log ((S + z) / 4) - z * Real.log z
  change -(3 / 4 : ℝ) * (y - x) ≤ F y - F x
  have hS0 : 0 < S := zero_lt_one.trans_le hS
  have hd (z : ℝ) (hz : 0 < z) :
      HasDerivAt F (Real.log ((S + z) / (4 * z))) z := by
    have hSz : 0 < S + z := by positivity
    have hSz4 : 0 < (S + z) / 4 := by positivity
    have hA := (hasDerivAt_id z).const_add S
    have hL := (hA.div_const 4).log hSz4.ne'
    rw [show (S + z) / (4 * z) = ((S + z) / 4) / z by rw [div_div],
      Real.log_div hSz4.ne' hz.ne']
    convert (hA.mul hL).sub ((hasDerivAt_id z).mul (Real.hasDerivAt_log hz.ne')) using 1
    · rfl
    · simp only [id_eq, one_mul]
      field_simp [hSz.ne', hz.ne']
      ring
  have hlog2 : Real.log 2 ≤ (3 / 4 : ℝ) := calc
    _ ≤ Real.log ((9 / 8 : ℝ) ^ 6) :=
      (Real.log_le_log_iff (by norm_num) (by norm_num)).2 (by norm_num)
    _ = 6 * Real.log (9 / 8) := by rw [Real.log_pow]; norm_num
    _ ≤ _ := by linarith only [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 9 / 8 by norm_num)]
  have hdLower (z : ℝ) (hz : z ∈ Set.Icc x y) : -(3 / 4 : ℝ) ≤ deriv F z := by
    have hz0 : 0 < z := hx.trans_le hz.1
    have hratio : (1 / 2 : ℝ) ≤ (S + z) / (4 * z) :=
      (le_div_iff₀ (by positivity)).2 (by linarith only [hS, hz.2, hy])
    rw [(hd z hz0).deriv]
    calc
      _ ≤ Real.log (1 / 2) := by rw [one_div, Real.log_inv]; linarith only [hlog2]
      _ ≤ _ := (Real.log_le_log_iff (by norm_num)
        ((by norm_num : (0 : ℝ) < 1 / 2).trans_le hratio)).2 hratio
  exact (convex_Icc x y).mul_sub_le_image_sub_of_le_deriv
    (fun z hz => (hd z (hx.trans_le hz.1)).continuousAt.continuousWithinAt)
    (fun z hz => by
      have hz' : z ∈ Set.Icc x y := interior_subset hz
      exact (hd z (hx.trans_le hz'.1)).differentiableAt.differentiableWithinAt)
    (fun z hz => hdLower z (interior_subset hz))
    x ⟨le_rfl, hxy⟩ y ⟨hxy, le_rfl⟩ hxy

private theorem scalar_increment_lower {r : ℝ} (U : Frame) {m n q : ℝ}
    (hm : 0 ≤ m) (hn : 0 < n) (hnq : n ≤ q) (hq1 : q ≤ 1)
    (hR : -1 ≤ imbalance U 2) (hh : 0 ≤ h r) (hb0 : 0 ≤ bias r) (hb : bias r ≤ 3 / 8)
    (ha0 : 0 ≤ alpha r) (ha : alpha r ≤ 1 / 2) :
    -(9 / 4 : ℝ) * (q - n) ≤ scalarIncrement r U m n q := by
  have hq : 0 < q := hn.trans_le hnq
  have hn1 := hnq.trans hq1
  have hm3 : 0 ≤ m ^ 3 := by positivity
  have hn3 : 0 < n ^ 3 := by positivity
  have hmass := pow_le_pow_left₀ hn.le hnq 3
  have hmass1 : q ^ 3 ≤ 1 := by simpa using pow_le_pow_left₀ hq.le hq1 3
  have hmassDiff : 0 ≤ q ^ 3 - n ^ 3 := sub_nonneg.mpr hmass
  have hmassCap : q ^ 3 - n ^ 3 ≤ 3 * (q - n) := by
    have hsum : q ^ 2 + q * n + n ^ 2 ≤ 3 := by
      have hq2 : q ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hq.le hq1 2
      have hn2 : n ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hn.le hn1 2
      have hqn : q * n ≤ 1 := by
        simpa using mul_le_mul hq1 hn1 hn.le (show (0 : ℝ) ≤ 1 by norm_num)
      linarith only [hq2, hn2, hqn]
    calc
      _ = (q ^ 2 + q * n + n ^ 2) * (q - n) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hsum (sub_nonneg.mpr hnq)
  have hent := entropy_mass_gain (S := m ^ 3 + n ^ 3 + 1)
    (by linarith only [hm3, hn3]) hn3 hmass hmass1
  have htotal (z : ℝ) : m ^ 3 + n ^ 3 + 1 + z = m ^ 3 + n ^ 3 + z + 1 := by ring
  rw [htotal (q ^ 3), htotal (n ^ 3)] at hent
  have hblog : -(3 / 8 : ℝ) ≤ h r + bias r * imbalance U 2 := by
    have hbR := mul_le_mul_of_nonneg_left hR hb0
    linarith only [hh, hb, hbR]
  have hterm := mul_le_mul_of_nonneg_right hblog hmassDiff
  have hent' := (mul_le_mul_of_nonpos_right ha
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num : -(3 / 4 : ℝ) ≤ 0) hmassDiff)).trans
    (mul_le_mul_of_nonneg_left hent ha0)
  unfold scalarIncrement totalAt
  linarith only [hterm, hent', hmassCap]

private theorem cubic_loss_upper {C E n q : ℝ} (hc0 : 0 ≤ C) (hc : C ≤ 9 / 8)
    (he : E ≤ 3 / 64) (hn : 9 / 10 ≤ n) (hnq : n ≤ q) (hq : q ≤ 1) :
    cubic C E 1 n - cubic C E 1 q ≤ (189 / 400 : ℝ) * (q - n) := by
  have ha : 0 ≤ 1 - n := sub_nonneg.mpr (hnq.trans hq)
  have hb : 0 ≤ 1 - q := sub_nonneg.mpr hq
  have hal : 1 - n ≤ (1 / 10 : ℝ) := by linarith only [hn]
  have hbl : 1 - q ≤ (1 / 10 : ℝ) := by linarith only [hal, hnq]
  have hsum : (1 - n) + (1 - q) ≤ (1 / 5 : ℝ) := by linarith only [hal, hbl]
  have hquad : (1 - n) ^ 2 + (1 - n) * (1 - q) + (1 - q) ^ 2 ≤ (3 / 100 : ℝ) := by
    have h1 := pow_le_pow_left₀ ha hal 2
    have h2 := pow_le_pow_left₀ hb hbl 2
    have h3 := mul_le_mul hal hbl hb (by norm_num : (0 : ℝ) ≤ 1 / 10)
    linarith only [h1, h2, h3]
  have hsym : ((1 - n) + (1 - q)) * (1 + n) - (1 - q) ^ 2 ≤ (2 / 5 : ℝ) := by
    have h1 : 1 + n ≤ 2 := by linarith only [ha]
    have h2 := mul_le_mul hsum h1 (by linarith only [hn] : 0 ≤ 1 + n)
      (by norm_num : (0 : ℝ) ≤ 1 / 5)
    linarith only [h2, sq_nonneg (1 - q)]
  have hC := (mul_le_mul_of_nonneg_left hsym hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num : (0 : ℝ) ≤ 2 / 5))
  have hE := (mul_le_mul_of_nonneg_right he
      (show 0 ≤ (1 - n) ^ 2 + (1 - n) * (1 - q) + (1 - q) ^ 2 by positivity)).trans
    (mul_le_mul_of_nonneg_left hquad (by norm_num : (0 : ℝ) ≤ 3 / 64))
  calc
    _ = (C * (((1 - n) + (1 - q)) * (1 + n) - (1 - q) ^ 2) +
        E * ((1 - n) ^ 2 + (1 - n) * (1 - q) + (1 - q) ^ 2)) * (q - n) := by unfold cubic; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hC, hE]) (sub_nonneg.mpr hnq)

/-- A strict uniform lower bound for the normalized deficit on the raised-middle rectangle. -/
theorem source_deficit_rectangle {r m n q : ℝ}
    (U : Frame) (hU : Uᴴ * U = 1) (hUU : U * Uᴴ = 1)
    (hrlo : 6 / 5 ≤ r) (hrhi : r ≤ 5 / 4)
    (hmlo : 23 / 50 ≤ m) (hmhi : m ≤ 1 / 2)
    (hnlo : 9 / 10 ≤ n) (hnhi : n ≤ 23 / 25)
    (hdlo : 0 ≤ q - n) (hdhi : q - n ≤ 1 / 40) :
    1 / 200 < sourceDeficitAt r U m n q := by
  have hr : 1 < r := lt_of_lt_of_le (by norm_num) hrlo
  have hm : 0 ≤ m := by linarith only [hmlo]
  have hn : 0 < n := by linarith only [hnlo]
  have hmn : m ≤ n := by linarith only [hmhi, hnlo]
  have hnq := sub_nonneg.mp hdlo
  have hq1 : q ≤ 1 := by linarith only [hnhi, hdhi]
  obtain ⟨hinc, hgain, _, _⟩ := signed_increment hr.le U hU hUU hm hmn hnq hq1
  obtain ⟨_, hframe, hrep⟩ := repeated_middle_lower_bound hr.le
    (WuOneModeCubic.one_mode_bound hr.le) U hU hUU hm hmn (hnq.trans hq1)
  have hgap := weighted_holder_gaps_quantitative hrlo hrhi hmlo hmhi hnlo hnhi
  have hW (i j : Fin 4) : 0 ≤ weight U i j :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hR : -1 ≤ imbalance U 2 := by
    have hrow := Finset.sum_nonneg (s := Finset.univ) (fun j _ => hW 2 j)
    rw [row_weight U hU hUU] at hrow
    linarith only [hrow]
  obtain ⟨ha0, ha⟩ := alpha_bounds hr
  obtain ⟨hb0, hb⟩ := bias_bounds hr.le hrhi
  have hscalar := scalar_increment_lower U hm hn hnq hq1 hR
    (h_nonneg_on_rectangle hrlo hrhi ha0 ha) hb0 hb ha0 ha
  obtain ⟨hc0, hc, he0, he⟩ := cubic_coefficient_bounds hr.le hrhi
  have hpBound : lossPlus r n q ≤ (189 / 400 : ℝ) * (q - n) :=
    cubic_loss_upper hc0 hc he hnlo hnq hq1
  have hmBound : lossMinus r n q ≤ (189 / 400 : ℝ) * (q - n) := by
    rw [lossMinus, cubic_swap (c r) (e r) n 1, cubic_swap (c r) (e r) q 1]
    exact cubic_loss_upper hc0 hc (by linarith only [he0]) hnlo hnq hq1
  have hu : WuPhysicalHighHigh.pairing (U.col 3) (U.col 3) = 1 := by
    rw [column_pairing, hU, Matrix.one_apply_eq]
  have hv : WuPhysicalHighHigh.pairing (U.col 2) (U.col 2) = 1 := by
    rw [column_pairing, hU, Matrix.one_apply_eq]
  have huv : WuPhysicalHighHigh.pairing (U.col 3) (U.col 2) = 0 := by
    rw [column_pairing, hU, Matrix.one_apply_ne (by decide : (3 : Fin 4) ≠ 2)]
  have hsum : weight U 3 2 + weight U 2 3 ≤ 1 := by
    have hphys := (WuPhysicalHighHigh.weighted_high_high _ _ hu hv huv 1 1
      zero_le_one zero_le_one).1
    rw [column_weight U 3 2, column_weight U 2 3]
    norm_num at hphys
    linarith only [hphys, Complex.normSq_nonneg (WuPhysicalHighHigh.eta (U.col 3) (U.col 2)),
      Complex.normSq_nonneg (WuPhysicalHighHigh.sigma (U.col 3) (U.col 2))]
  have hcap0 : 0 ≤ (189 / 400 : ℝ) * (q - n) := by positivity
  have hloss : lossPlus r n q * weight U 3 2 + lossMinus r n q * weight U 2 3 ≤
      (189 / 400 : ℝ) * (q - n) := calc
    _ ≤ ((189 / 400 : ℝ) * (q - n)) * weight U 3 2 +
        ((189 / 400 : ℝ) * (q - n)) * weight U 2 3 :=
      add_le_add (mul_le_mul_of_nonneg_right hpBound (hW 3 2))
        (mul_le_mul_of_nonneg_right hmBound (hW 2 3))
    _ = ((189 / 400 : ℝ) * (q - n)) * (weight U 3 2 + weight U 2 3) := by ring
    _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hsum hcap0
  linarith only [hinc, hgain, hframe, hrep, hgap, hscalar, hloss, hdhi]

end D5.S3.Quantum.Semigroups.WuCubicSignedTransfer
