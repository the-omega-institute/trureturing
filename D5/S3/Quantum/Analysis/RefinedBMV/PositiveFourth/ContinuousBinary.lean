/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/ContinuousBinary
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict conditioning of the cleared binary four-copy deficits at real exponents. -/

import D5.S3.Quantum.Analysis.RefinedBMV.BinaryGramConditioning

/-! Confluent power differences and strict conditioning for real degrees. -/

noncomputable section

namespace RefinedBMV.ThreeBlockGram

open RefinedBMV.ThreeBlockGram.ZeroSpectrum (fNum jNum gNum N)
open RefinedBMV.ZeroSpectrum (nonneg_of_checks)

open private groups lowerTerm eval_groups static_checked masks_checked
  from D5.S3.Quantum.Analysis.RefinedBMV.BinaryGramConditioning

/-- The exact binary certificate applies for real degrees because its
annihilating-chain initial values are polynomials in the degree minus one. -/
theorem cleared_binary_conditioning_real {p r : ℝ} (hp : 1 ≤ p)
    (hr : 0 < r) (hr₁ : r < 1) :
    let y := r ^ (p / 8)
    (gNum p r y)^2 < 2 * fNum p r y * jNum p r y := by
  let t : ℝ := -Real.log r / 8
  have ht : 0 < t := by
    dsimp [t]
    linarith only [Real.log_neg hr hr₁]
  have hbase : Real.exp (-8 * t) = r := by
    rw [show -8 * t = Real.log r by dsimp [t]; ring, Real.exp_log hr]
  have hy : Real.exp (-p * t) = r ^ (p / 8) := by
    rw [Real.rpow_def_of_pos hr]
    congr 1
    dsimp [t]
    ring
  let y := r ^ (p / 8)
  have hy₀ : 0 < y := by
    change 0 < r ^ (p / 8)
    rw [← hy]
    exact Real.exp_pos _
  have hy₁ : y < 1 := by
    change r ^ (p / 8) < 1
    rw [← hy, Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (by linarith) ht
  have hsq : y^2 < 1 := pow_lt_one₀ hy₀.le hy₁ (by decide)
  have hrsq : r * y^2 < 1 :=
    (mul_lt_mul_of_pos_left hsq hr).trans (by simpa only [mul_one] using hr₁)
  have hmargin : 0 < lowerTerm r y :=
    mul_pos (mul_pos (pow_pos (sub_pos.mpr hr₁) _) (pow_pos (sub_pos.mpr hsq) _))
      (pow_pos (sub_pos.mpr hrsq) _)
  have h := nonneg_of_checks groups 6 80 320 52 static_checked masks_checked p t hp ht.le
  rw [hbase, hy, eval_groups] at h
  exact sub_pos.mp ((mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 36)).mp
    (hmargin.trans_le (sub_nonneg.mp h)))

private def powerJet (p x : ℝ) (n : ℕ) : ℝ :=
  (∏ j ∈ Finset.range n, (p + 3 - (j : ℝ))) * x ^ (p + 3 - (n : ℝ)) /
    (n.factorial : ℝ)

/-- The confluent divided difference of (x^{p+3}) with copies of (r) and (1). -/
private def confluentDifference (p r : ℝ) : ℕ → ℕ → ℝ
  | 0, n => powerJet p 1 (n - 1)
  | m + 1, 0 => powerJet p r m
  | m + 1, n + 1 =>
    (confluentDifference p r m (n + 1) - confluentDifference p r (m + 1) n) / (1 - r)
termination_by m n => m + n

/-- The four-node scalar defect with (k) copies of (r) and (4-k) copies of (1). -/
def confluentBinaryDefect (p r : ℝ) (k : ℕ) : ℝ :=
  confluentDifference p r k (4 - k) - N p * r ^ ((p / 4) * (k : ℝ))

private theorem confluentBinaryDefect_clear (p : ℝ) {r : ℝ} (hr : 0 < r) (hr₁ : r < 1) :
    let y := r ^ (p / 8)
    (1 - r)^3 * confluentBinaryDefect p r 3 = fNum p r y ∧
    (1 - r)^3 * confluentBinaryDefect p r 1 = jNum p r y ∧
    (1 - r)^3 * confluentBinaryDefect p r 2 = gNum p r y := by
  let y := r ^ (p / 8)
  have h8 : y^8 = r^p := by
    rw [← Real.rpow_natCast y 8]
    change (r ^ (p / 8)) ^ (8 : ℝ) = r ^ p
    rw [← Real.rpow_mul hr.le]
    congr 1
    ring
  have hshift (j : ℕ) : r ^ (p + (j : ℝ)) = r^j * y^8 := by
    rw [Real.rpow_add hr, Real.rpow_natCast, h8, mul_comm]
  have hcenter (j : ℕ) : r ^ ((p / 4) * (j : ℝ)) = y^(2*j) := by
    rw [← Real.rpow_natCast y, Nat.cast_mul]
    change r ^ ((p / 4) * (j : ℝ)) = (r ^ (p / 8)) ^ ((2 : ℝ) * (j : ℝ))
    rw [← Real.rpow_mul hr.le]
    congr 1
    ring
  have hsub1 : r ^ (p + 3 - 1 : ℝ) = r^2 * y^8 := by
    rw [show p + 3 - 1 = p + ((2 : ℕ) : ℝ) by norm_num <;> ring, hshift]
  have hsub2 : r ^ (p + 3 - 2 : ℝ) = r * y^8 := by
    rw [show p + 3 - 2 = p + ((1 : ℕ) : ℝ) by norm_num <;> ring, hshift, pow_one]
  have htop : r ^ (p + 3 : ℝ) = r^3 * y^8 := by exact hshift 3
  have hden : 1 - r ≠ 0 := (sub_pos.mpr hr₁).ne'
  change _ = fNum p r y ∧ _ = jNum p r y ∧ _ = gNum p r y
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [confluentBinaryDefect, hcenter 3, hcenter 1, hcenter 2] <;>
    norm_num [confluentDifference, powerJet, Finset.prod_range_succ,
      hsub1, hsub2, htop, fNum, jNum, gNum, N, ZeroSpectrum.q, ZeroSpectrum.C,
      ZeroSpectrum.w] <;>
    field_simp [hden] <;> ring

/-- Strict binary Gram conditioning at the real degree (p). -/
theorem confluent_binary_conditioning {p r : ℝ}
    (hp : 1 ≤ p) (hr : 0 < r) (hr₁ : r < 1) :
    (confluentBinaryDefect p r 2)^2 <
      2 * confluentBinaryDefect p r 3 * confluentBinaryDefect p r 1 := by
  obtain ⟨h3, h1, h2⟩ := confluentBinaryDefect_clear p hr hr₁
  have h := cleared_binary_conditioning_real hp hr hr₁
  dsimp only at h
  rw [← h3, ← h1, ← h2] at h
  apply lt_of_mul_lt_mul_left _ (pow_nonneg (sub_nonneg.mpr hr₁.le) 6)
  convert h using 1 <;> ring

#print axioms cleared_binary_conditioning_real
#print axioms confluent_binary_conditioning

end RefinedBMV.ThreeBlockGram
