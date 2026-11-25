/- GID: D5/S3/Fourier/Asymptotics/CyclicSupportCertificate
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/CyclicSupportCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The outer activation variation and finite sign certificate for cyclic support. -/

import D5.S3.Fourier.Asymptotics.CyclicParityCorrection

/-! The sign of the outer variation follows from the pair formula for the
quadratic orthogonal to constants and linear functions. Exact cosine deficits
and the sign of a convex quadratic give a finite optimizer certificate. -/

open Finset
open D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison
open D5.S3.Fourier.Asymptotics.CyclicParityCorrection

noncomputable section

namespace D5.S3.Fourier.Asymptotics.CyclicSupportCertificate

set_option autoImplicit false

private theorem pair_moment {ι : Type*} [Fintype ι] (a x : ι → ℝ) :
    (∑ i, ∑ j, a i * a j * (x i - x j) ^ 2) =
      2 * ((∑ i, a i) * (∑ i, a i * x i ^ 2) - (∑ i, a i * x i) ^ 2) := by
  have key (i j : ι) : a i * a j * (x i - x j) ^ 2 =
      (a i * x i ^ 2) * a j + a i * (a j * x j ^ 2) -
        (2 * (a i * x i)) * (a j * x j) := by ring
  simp_rw [key, sum_sub_distrib, sum_add_distrib, ← mul_sum, ← sum_mul, ← mul_sum]
  ring

private theorem moment_det_nonneg {ι : Type*} [Fintype ι] (a x : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    0 ≤ (∑ i, a i) * (∑ i, a i * x i ^ 2) - (∑ i, a i * x i) ^ 2 := by
  have hn : 0 ≤ ∑ i, ∑ j, a i * a j * (x i - x j) ^ 2 :=
    sum_nonneg fun i _ => sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (ha i) (ha j)) (sq_nonneg _)
  linarith only [hn, pair_moment a x]

/-- A quadratic with nonnegative leading coefficient, zero total variation, and positive
first-moment variation is strictly positive at the largest sampled level. -/
theorem boundary_variation_pos {ι : Type*} [Fintype ι] (x : ι → ℝ) (j : ι)
    (hmax : ∀ i, x i ≤ x j)
    (a b g : ℝ) (hg : 0 ≤ g)
    (hmass : ∑ i, (a + b * x i + g * x i ^ 2) = 0)
    (hmoment : 0 < ∑ i, x i * (a + b * x i + g * x i ^ 2)) :
    let clip := fun y : ℝ => max 0 y
    0 < clip (a + b * x j + g * x j ^ 2) := by
  simp only [lt_max_iff, lt_irrefl, false_or]
  have hbelow : ∃ i, x i < x j := by
    by_contra! h
    have heq (i : ι) : x i = x j := le_antisymm (hmax i) (h i)
    have hz : (∑ i, x i * (a + b * x i + g * x i ^ 2)) = 0 := by
      calc
        _ = ∑ i, x j * (a + b * x i + g * x i ^ 2) :=
          sum_congr rfl fun i _ => by nth_rw 1 [heq i]
        _ = 0 := by rw [← mul_sum, hmass, mul_zero]
    exact (ne_of_gt hmoment) hz
  let count : ℝ := ∑ _ : ι, (1 : ℝ)
  let s₁ : ℝ := ∑ i, x i
  let s₂ : ℝ := ∑ i, x i ^ 2
  let s₃ : ℝ := ∑ i, x i ^ 3
  let T := x j
  let K := ∑ i, x i * (a + b * x i + g * x i ^ 2)
  have h0 : count * a + s₁ * b + s₂ * g = 0 := by
    simpa [count, s₁, s₂, sum_add_distrib, ← mul_sum, mul_comm] using hmass
  have h1 : s₁ * a + s₂ * b + s₃ * g = K := by
    have key (i : ι) : x i * (a + b * x i + g * x i ^ 2) =
        x i * a + x i ^ 2 * b + x i ^ 3 * g := by ring
    simp [K, key, sum_add_distrib, ← sum_mul, s₁, s₂, s₃]
  have he₀ : (∑ i, (T - x i)) = count * T - s₁ := by
    rw [sum_sub_distrib]
    congr 1
    simp [count]
  have he₁ : (∑ i, (T - x i) * x i) = s₁ * T - s₂ := by
    simp_rw [sub_mul, ← pow_two, sum_sub_distrib, ← mul_sum]
    exact congrArg (· - s₂) (mul_comm _ _)
  have he₂ : (∑ i, (T - x i) * x i ^ 2) = s₂ * T - s₃ := by
    have key (i : ι) : (T - x i) * x i ^ 2 = T * x i ^ 2 - x i ^ 3 := by ring
    simp_rw [key, sum_sub_distrib, ← mul_sum]
    exact congrArg (· - s₃) (mul_comm _ _)
  have hpair := moment_det_nonneg (fun i => T - x i) x (fun i => sub_nonneg.mpr (hmax i))
  rw [he₀, he₁, he₂] at hpair
  have hdet := moment_det_nonneg (fun _ : ι => 1) x (fun _ => zero_le_one)
  simp only [one_mul] at hdet
  change 0 ≤ count * s₂ - s₁ ^ 2 at hdet
  have hgap : 0 < count * T - s₁ := by
    rw [← he₀]
    obtain ⟨i, hi⟩ := hbelow
    exact sum_pos' (fun k _ => sub_nonneg.mpr (hmax k)) ⟨i, mem_univ _, sub_pos.mpr hi⟩
  have hidentity :
      (count * s₂ - s₁ ^ 2) * (a + b * T + g * T ^ 2) =
        (count * T - s₁) * K + g * ((count * T - s₁) * (s₂ * T - s₃) - (s₁ * T - s₂) ^ 2) := by
    rw [← h1]
    linear_combination (s₂ - s₁ * T) * h0
  change 0 < K at hmoment
  by_contra! h
  have hl := mul_nonpos_of_nonneg_of_nonpos hdet h
  have hr := add_pos_of_pos_of_nonneg (mul_pos hgap hmoment) (mul_nonneg hg hpair)
  exact (not_lt_of_ge (hidentity ▸ hl)) hr

private def dualValue (s a b g c : ℝ) : ℝ := a + b * (1 - c) + g * ((1 - c ^ 2) / s)

private theorem dualValue_convex (s a b g : ℝ) (hs : 0 < s) (hg : g ≤ 0) :
    ConvexOn ℝ Set.univ (dualValue s a b g) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ u v hu hv huv
  simp only [smul_eq_mul, dualValue]
  field_simp [hs.ne']
  have hcoef : 0 ≤ -g := neg_nonneg.mpr hg
  have hsq : 0 ≤ (-g) * (u * v * (x - y) ^ 2) :=
    mul_nonneg hcoef (mul_nonneg (mul_nonneg hu hv) (sq_nonneg _))
  nlinarith only [hsq, congrArg (fun z : ℝ => g * (u * x ^ 2 + v * y ^ 2) * z) huv,
    congrArg (fun z : ℝ => (a * s + b * s + g) * z) huv]

theorem dualValue_nonpos_of_between {s a b g lo hi c : ℝ} (hs : 0 < s)
    (hg : g ≤ 0) (hlo : lo ≤ c) (hhi : c ≤ hi)
    (hl : dualValue s a b g lo ≤ 0) (hh : dualValue s a b g hi ≤ 0) :
    dualValue s a b g c ≤ 0 := by
  rcases eq_or_lt_of_le (hlo.trans hhi) with he | hlt
  · rw [le_antisymm hhi (he ▸ hlo), ← he]
    exact hl
  let u := (hi - c) / (hi - lo)
  let v := (c - lo) / (hi - lo)
  have hden := sub_pos.mpr hlt
  have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr hhi) hden.le
  have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr hlo) hden.le
  have huv : u + v = 1 := by dsimp [u, v]; field_simp; ring
  have hc : u * lo + v * hi = c := by dsimp [u, v]; field_simp; ring
  have h := (dualValue_convex s a b g hs hg).2
    (Set.mem_univ lo) (Set.mem_univ hi) hu hv huv
  simp only [smul_eq_mul, hc] at h
  exact h.trans (add_nonpos (mul_nonpos_of_nonneg_of_nonpos hu hl)
    (mul_nonpos_of_nonneg_of_nonpos hv hh))

/-- Exact moments and the signs of a quadratic dual certify the unique optimizer.
A zero dual value off the support is allowed at a support transition. -/
theorem exact_support_of_dual_nonpos {q : ℕ} [NeZero q] {threshold s a b g : ℝ}
    {sites : Finset (ZMod q)} (hs : 0 < s) (hb : b ≤ 0) (hg : g ≤ 0) :
    let clip := fun y : ℝ => max 0 y
    let p := fun i : ZMod q => a + b * (1 - sample i) + g * ((1 - sample i ^ 2) / s)
    let v := fun i : ZMod q => if i ∈ sites then p i else 0
    (∀ i ∈ sites, 0 < p i) →
    (∀ i ∉ sites, p i ≤ 0) →
    (∑ i, v i) = 1 →
    cosineMoment 1 v = threshold →
    cosineMoment 2 v = threshold →
    v ∈ feasible q threshold ∧
      (∀ w ∈ feasible q threshold, w ≠ v → energy v < energy w) ∧
      (∀ w ∈ feasible q threshold, energy v + (∑ i, (w i - v i) ^ 2) ≤ energy w) ∧
      ∀ w ∈ feasible q threshold, IsMinOn energy (feasible q threshold) w →
        ∀ i, 0 < clip (w i) ↔ i ∈ sites := by
  intro clip p v hpos hoff hmass hM₁ hM₂
  have hv (i) : v i = max 0 (p i) := by
    by_cases hi : i ∈ sites
    · simp [v, hi, max_eq_right (hpos i hi).le]
    · simp [v, hi, max_eq_left (hoff i hi)]
  have hvf : v ∈ feasible q threshold :=
    ⟨fun i => hv i ▸ le_max_left _ _, hmass, hM₁.ge, hM₂.ge⟩
  have hdot (w : ZMod q → ℝ) (hw : ∑ i, w i = 1) :
      (∑ i, w i * p i) = a + b * (1 - cosineMoment 1 w) +
        (g / s) * ((1 - cosineMoment 2 w) / 2) := by
    have key (i) : w i * p i = a * w i + b * (w i * (1 - sample i)) +
        (g / s) * (w i * (1 - sample i ^ 2)) := by dsimp [p]; ring
    simp_rw [key, sum_add_distrib, ← mul_sum, hw, mul_one,
      (sum_sample_deficits hw).1, (sum_sample_deficits hw).2]
  have hstability (w) (hw : w ∈ feasible q threshold) :
      energy v + (∑ i, (w i - v i) ^ 2) ≤ energy w := by
    have hdotDiff : (∑ i, v i * p i) ≤ ∑ i, w i * p i := by
      rw [hdot v hmass, hdot w hw.2.1, hM₁, hM₂]
      have h₁ : 1 - cosineMoment 1 w ≤ 1 - threshold := by linarith only [hw.2.2.1]
      have h₂ : (1 - cosineMoment 2 w) / 2 ≤ (1 - threshold) / 2 := by linarith only [hw.2.2.2]
      exact add_le_add (add_le_add_right (mul_le_mul_of_nonpos_left h₁ hb) a)
        (mul_le_mul_of_nonpos_left h₂ (div_nonpos_of_nonpos_of_nonneg hg hs.le))
    have hclip : 0 ≤ ∑ i, w i * (v i - p i) :=
      sum_nonneg fun i _ => mul_nonneg (hw.1 i) (sub_nonneg.mpr ((hv i).symm ▸ le_max_right _ _))
    have he (i) : v i * p i = v i ^ 2 := by
      rw [hv]
      rcases le_total 0 (p i) with h | h
      · rw [max_eq_right h, pow_two]
      · simp [max_eq_left h]
    have hex : energy w = energy v + (∑ i, (w i - v i) ^ 2) +
        2 * (∑ i, w i * (v i - p i)) + 2 * ((∑ i, w i * p i) - ∑ i, v i * p i) := by
      have key (i) : w i ^ 2 = v i ^ 2 + (w i - v i) ^ 2 +
          2 * (w i * (v i - p i)) + 2 * (w i * p i - v i * p i) := by rw [he]; ring
      unfold energy
      conv_lhs => arg 2; ext i; rw [key]
      simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum]
    linarith only [hex, hclip, hdotDiff]
  have hstrict (w) (hw : w ∈ feasible q threshold) (hne : w ≠ v) :
      energy v < energy w := by
    have hd : 0 < ∑ i, (w i - v i) ^ 2 := by
      obtain ⟨i, hi⟩ : ∃ i, w i ≠ v i := by
        by_contra! h
        exact hne (funext h)
      exact sum_pos' (fun _ _ => sq_nonneg _) ⟨i, mem_univ _, sq_pos_of_ne_zero (sub_ne_zero.mpr hi)⟩
    linarith only [hd, hstability w hw]
  refine ⟨hvf, hstrict, hstability, fun w hw hmin i => ?_⟩
  have he : w = v := by
    by_contra h
    exact (not_lt_of_ge (hmin hvf)) (hstrict w hw h)
  rw [he]
  by_cases hi' : i ∈ sites <;> simp [clip, v, hi', hpos, lt_max_iff]

/-- The clipped quadratic with exact moment constraints uniquely minimizes squared mass.
Nonpositive readings at the two bounding excluded levels imply nonpositive readings
throughout the intervening interval. -/
theorem exact_support_of_dual {q : ℕ} [NeZero q] {threshold s a b g lo hi : ℝ}
    {sites : Finset (ZMod q)} (hs : 0 < s) (hb : b ≤ 0) (hg : g ≤ 0)
    (hlo : a + b * (1 - lo) + g * ((1 - lo ^ 2) / s) ≤ 0)
    (hhi : a + b * (1 - hi) + g * ((1 - hi ^ 2) / s) ≤ 0)
    (hbetween : ∀ i ∉ sites, lo ≤ sample i ∧ sample i ≤ hi) :
    let clip := fun y : ℝ => max 0 y
    let p := fun i : ZMod q => a + b * (1 - sample i) + g * ((1 - sample i ^ 2) / s)
    let v := fun i : ZMod q => if i ∈ sites then p i else 0
    (∀ i ∈ sites, 0 < p i) →
    (∑ i, v i) = 1 →
    cosineMoment 1 v = threshold →
    cosineMoment 2 v = threshold →
    v ∈ feasible q threshold ∧
      (∀ w ∈ feasible q threshold, w ≠ v → energy v < energy w) ∧
      (∀ w ∈ feasible q threshold, energy v + (∑ i, (w i - v i) ^ 2) ≤ energy w) ∧
      ∀ w ∈ feasible q threshold, IsMinOn energy (feasible q threshold) w →
        ∀ i, 0 < clip (w i) ↔ i ∈ sites := by
  intro clip p v hpos hmass hM₁ hM₂
  refine exact_support_of_dual_nonpos hs hb hg hpos ?_ hmass hM₁ hM₂
  intro i hi
  obtain ⟨hl, hh⟩ := hbetween i hi
  exact dualValue_nonpos_of_between hs hg hl hh hlo hhi

end D5.S3.Fourier.Asymptotics.CyclicSupportCertificate
