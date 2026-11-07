/- GID: D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice
   mirror-E: none(waiver:general-real-analysis)
   anchors: []
   utility: none
   digest: Boundary-one real price maximization, Bernoulli loss and integer rounding. -/

/- UNCOMPILED SOURCE CANDIDATE. No kernel or axiom-closure acceptance claimed.
The exponent domain is [1,infinity); no excluded-prime relaxation is used.
The derivative and decreasing slope are reused from ContinuousPrimeMaximum.
All auxiliary declarations below are consumed by the loss or rounding results. -/

import D5.S3.Arith.GoldenResource.ContinuousPrimeMaximum
import D5.S0.Diagonal.MarginBound
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.BoundaryPrimePrice

open Real Set
open D5.S0.Diagonal.MarginBound (bernoulliKL)

def benefit (p t : ℝ) : ℝ :=
  log ((1 - p ^ (-(t + 1))) / (1 - p ^ (-1 : ℝ)))

def priceObjective (p lam t : ℝ) : ℝ := benefit p t - lam * t * log p

def cutoff (lam : ℝ) : ℝ := 1 + lam⁻¹

def critical (p lam : ℝ) : ℝ := log (cutoff lam) / log p - 1

def boundary (p lam : ℝ) : ℝ := max 1 (critical p lam)

def probability (p t : ℝ) : ℝ := p ^ (-(t + 1))

def priceLoss (p lam t : ℝ) : ℝ :=
  priceObjective p lam (boundary p lam) - priceObjective p lam t

/-- This finite formula includes coincident floor/ceiling candidates and all ties. -/
def integerGap (p lam : ℝ) : ℝ :=
  min (priceLoss p lam (⌊boundary p lam⌋ : ℤ))
    (priceLoss p lam (⌈boundary p lam⌉ : ℤ))

private lemma cutoff_gt_one {lam : ℝ} (hlam : 0 < lam) : 1 < cutoff lam := by
  dsimp [cutoff]
  linarith [inv_pos.mpr hlam]

lemma probability_mem {p t : ℝ} (hp : 1 < p) (ht : 1 ≤ t) :
    0 < probability p t ∧ probability p t < 1 := by
  have hp0 : 0 < p := by linarith
  refine ⟨rpow_pos_of_pos hp0 _, ?_⟩
  dsimp [probability]
  rw [rpow_neg hp0.le]
  exact (inv_lt_one₀ (rpow_pos_of_pos hp0 _)).mpr
    (one_lt_rpow hp (by linarith))

lemma benefit_log {p t : ℝ} (hp : 1 < p) (ht : 1 ≤ t) :
    benefit p t = log (1 - probability p t) - log (1 - p ^ (-1 : ℝ)) := by
  have hu := probability_mem hp ht
  have hd : 0 < 1 - p ^ (-1 : ℝ) := by
    rw [rpow_neg_one]
    exact sub_pos.mpr ((inv_lt_one₀ (by linarith : 0 < p)).mpr hp)
  change log ((1 - probability p t) / (1 - p ^ (-1 : ℝ))) = _
  exact log_div (sub_pos.mpr hu.2).ne' hd.ne'

private lemma critical_power {p lam : ℝ} (hp : 1 < p) (hlam : 0 < lam) :
    p ^ (critical p lam + 1) = cutoff lam := by
  have hp0 : 0 < p := by linarith
  have hc0 : 0 < cutoff lam := by linarith [cutoff_gt_one hlam]
  rw [critical, sub_add_cancel, rpow_def_of_pos hp0]
  rw [show log p * (log (cutoff lam) / log p) = log (cutoff lam) by
    field_simp [(log_pos hp).ne'] <;> ring]
  exact exp_log hc0

private lemma critical_gt_one_iff {p lam : ℝ} (hp : 1 < p) (hlam : 0 < lam) :
    1 < critical p lam ↔ p ^ (2 : ℕ) < cutoff lam := by
  have hp0 : 0 < p := by linarith
  have hc0 : 0 < cutoff lam := by linarith [cutoff_gt_one hlam]
  have hlog : log (p ^ (2 : ℕ)) < log (cutoff lam) ↔
      p ^ (2 : ℕ) < cutoff lam := log_lt_log_iff (pow_pos hp0 _) hc0
  rw [log_pow] at hlog
  dsimp [critical]
  constructor
  · intro h
    apply hlog.mp
    have := (lt_div_iff₀ (log_pos hp)).mp (show 2 < log (cutoff lam) / log p by linarith)
    linarith
  · intro h
    have := (lt_div_iff₀ (log_pos hp)).mpr (hlog.mpr h)
    linarith

private lemma price_hasDerivAt {p lam t : ℝ} (hp : 1 < p) (ht : 1 ≤ t) :
    HasDerivAt (priceObjective p lam)
      (log p / (p ^ (t + 1) - 1) - lam * log p) t := by
  have h := D5.S3.Arith.GoldenResource.ContinuousPrimeMaximum.continuous_prime_hasDerivAt
    hp (by linarith : 0 ≤ t)
  convert h.sub ((((hasDerivAt_id t).const_mul lam).mul_const (log p))) using 1 <;>
    simp [priceObjective, benefit]

private lemma critical_slope {p lam : ℝ} (hp : 1 < p) (hlam : 0 < lam) :
    log p / (p ^ (critical p lam + 1) - 1) = lam * log p := by
  rw [critical_power hp hlam]
  dsimp [cutoff]
  field_simp [hlam.ne'] <;> ring

private lemma boundary_slope_le {p lam : ℝ} (hp : 1 < p) (hlam : 0 < lam) :
    log p / (p ^ (boundary p lam + 1) - 1) ≤ lam * log p := by
  by_cases hc : 1 < critical p lam
  · rw [boundary, max_eq_right hc.le, critical_slope hp hlam]
  · have hcp : cutoff lam ≤ p ^ (2 : ℕ) :=
      le_of_not_gt (fun h => hc ((critical_gt_one_iff hp hlam).mpr h))
    have hden : 0 < p ^ (2 : ℕ) - 1 := by nlinarith [sq_nonneg (p - 1)]
    have hinv : lam⁻¹ ≤ p ^ (2 : ℕ) - 1 := by dsimp [cutoff] at hcp; linarith
    have hmul := mul_le_mul_of_nonneg_left hinv hlam.le
    rw [mul_inv_cancel₀ hlam.ne'] at hmul
    rw [boundary, max_eq_left (le_of_not_gt hc)]
    norm_num only [one_add_one_eq_two, rpow_two]
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_le_mul_of_nonneg_left hmul (log_pos hp).le]

private lemma price_monotonicity {p lam : ℝ} (hp : 1 < p) (hlam : 0 < lam) :
    MonotoneOn (priceObjective p lam) (Icc 1 (boundary p lam)) ∧
      AntitoneOn (priceObjective p lam) (Ici (boundary p lam)) := by
  have hb : 1 ≤ boundary p lam := le_max_left _ _
  have hd := fun t ht => price_hasDerivAt (lam := lam) hp ht
  have hq := D5.S3.Arith.GoldenResource.ContinuousPrimeMaximum.continuous_prime_slope_strictAntiOn hp
  constructor
  · apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun t ht => (hd t ht.1).continuousAt.continuousWithinAt)
    · intro t ht
      rw [interior_Icc] at ht
      exact (hd t ht.1.le).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have hbc : boundary p lam = critical p lam := by
        dsimp [boundary] at ht ⊢
        apply max_eq_right
        rcases lt_max_iff.mp (lt_trans ht.1 ht.2) with h | h
        · exact (lt_irrefl _ h).elim
        · exact h.le
      rw [(hd t ht.1.le).deriv, ← critical_slope hp hlam, ← hbc]
      exact sub_nonneg.mpr (hq (by linarith) (by linarith) ht.2).le
  · apply antitoneOn_of_deriv_nonpos (convex_Ici _)
      (fun t ht => (hd t (hb.trans ht)).continuousAt.continuousWithinAt)
    · intro t ht
      rw [interior_Ici] at ht
      exact (hd t (hb.trans ht.le)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hd t (hb.trans ht.le)).deriv]
      exact sub_nonpos.mpr
        ((hq (by linarith) (by linarith) ht).le.trans (boundary_slope_le hp hlam))

/-- The boundary-one real optimizer is derived from the actual decreasing slope. -/
theorem boundary_maximum {p lam t : ℝ} (hp : 1 < p) (hlam : 0 < lam) (ht : 1 ≤ t) :
    priceObjective p lam t ≤ priceObjective p lam (boundary p lam) := by
  have hb : 1 ≤ boundary p lam := le_max_left _ _
  have hm := price_monotonicity hp hlam
  rcases le_total t (boundary p lam) with h | h
  · exact hm.1 ⟨ht, h⟩ ⟨hb, le_rfl⟩ h
  · exact hm.2 (by exact le_rfl) h h

/-- Every integer is dominated by one of the two adjacent integer candidates. -/
theorem integer_candidates {p lam : ℝ} (hp : 1 < p) (hlam : 0 < lam)
    (k : ℤ) (hk : 1 ≤ k) :
    priceObjective p lam k ≤
      max (priceObjective p lam (⌊boundary p lam⌋ : ℤ))
        (priceObjective p lam (⌈boundary p lam⌉ : ℤ)) := by
  have hb : 1 ≤ boundary p lam := le_max_left _ _
  have hfloor : (1 : ℤ) ≤ ⌊boundary p lam⌋ := Int.le_floor.mpr (by simpa using hb)
  have hfloorR : (1 : ℝ) ≤ (⌊boundary p lam⌋ : ℤ) := by exact_mod_cast hfloor
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hm := price_monotonicity hp hlam
  rcases le_total (k : ℝ) (boundary p lam) with h | h
  · have hkf : k ≤ ⌊boundary p lam⌋ := Int.le_floor.mpr h
    have hkfR : (k : ℝ) ≤ (⌊boundary p lam⌋ : ℤ) := by exact_mod_cast hkf
    exact (hm.1 ⟨hkR, h⟩ ⟨hfloorR, Int.floor_le _⟩ hkfR).trans (le_max_left _ _)
  · have hck : ⌈boundary p lam⌉ ≤ k := Int.ceil_le.mpr h
    have hckR : ((⌈boundary p lam⌉ : ℤ) : ℝ) ≤ k := by exact_mod_cast hck
    exact (hm.2 (Int.le_ceil _) h hckR).trans (le_max_right _ _)

/-- Nonnegative finite rounding loss, bounded by the loss at EVERY integer. -/
theorem integer_gap_bounds {p lam : ℝ} (hp : 1 < p) (hlam : 0 < lam)
    (k : ℤ) (hk : 1 ≤ k) :
    0 ≤ integerGap p lam ∧ integerGap p lam ≤ priceLoss p lam k := by
  have hb : 1 ≤ boundary p lam := le_max_left _ _
  have hf : (1 : ℤ) ≤ ⌊boundary p lam⌋ := Int.le_floor.mpr (by simpa using hb)
  have hfR : (1 : ℝ) ≤ (⌊boundary p lam⌋ : ℤ) := by exact_mod_cast hf
  have hcR : (1 : ℝ) ≤ (⌈boundary p lam⌉ : ℤ) := hb.trans (Int.le_ceil _)
  constructor
  · exact le_min (sub_nonneg.mpr (boundary_maximum hp hlam hfR))
      (sub_nonneg.mpr (boundary_maximum hp hlam hcR))
  · have hi := integer_candidates hp hlam k hk
    rcases le_total (priceObjective p lam (⌊boundary p lam⌋ : ℤ))
        (priceObjective p lam (⌈boundary p lam⌉ : ℤ)) with h | h
    · rw [max_eq_right h] at hi
      exact (min_le_right _ _).trans (sub_le_sub_left hi _)
    · rw [max_eq_left h] at hi
      exact (min_le_left _ _).trans (sub_le_sub_left hi _)

/-- The finite expression is attained by an admissible integer, including ties. -/
theorem integer_gap_attained {p lam : ℝ} (hp : 1 < p) (hlam : 0 < lam) :
    ∃ k : ℤ, 1 ≤ k ∧ integerGap p lam = priceLoss p lam k ∧
      ∀ j : ℤ, 1 ≤ j → priceObjective p lam j ≤ priceObjective p lam k := by
  have hb : 1 ≤ boundary p lam := le_max_left _ _
  have hf : (1 : ℤ) ≤ ⌊boundary p lam⌋ := Int.le_floor.mpr (by simpa using hb)
  have hc : (1 : ℤ) ≤ ⌈boundary p lam⌉ := by
    exact_mod_cast (hb.trans (Int.le_ceil (boundary p lam)))
  rcases le_total (priceLoss p lam (⌊boundary p lam⌋ : ℤ))
      (priceLoss p lam (⌈boundary p lam⌉ : ℤ)) with h | h
  · refine ⟨⌊boundary p lam⌋, hf, min_eq_left h, ?_⟩
    intro j hj
    have hh := (integer_gap_bounds hp hlam j hj).2
    rw [integerGap, min_eq_left h] at hh
    dsimp [priceLoss] at hh
    linarith
  · refine ⟨⌈boundary p lam⌉, hc, min_eq_right h, ?_⟩
    intro j hj
    have hh := (integer_gap_bounds hp hlam j hj).2
    rw [integerGap, min_eq_right h] at hh
    dsimp [priceLoss] at hh
    linarith

private lemma bernoulli_scaled {v u : ℝ} (hv : 0 < v) (hv1 : v < 1)
    (hu : 0 < u) (hu1 : u < 1) :
    bernoulliKL v u / (1 - v) =
      log (1 - v) - log (1 - u) + v / (1 - v) * (log v - log u) := by
  dsimp [bernoulliKL]
  rw [log_div hv.ne' hu.ne', log_div (by linarith) (by linarith)]
  field_simp [show 1 - v ≠ 0 by linarith]
  <;> ring

private lemma probability_odds {p x : ℝ} (hp : 1 < p) (hx : 1 ≤ x) :
    probability p x / (1 - probability p x) = 1 / (p ^ (x + 1) - 1) := by
  have hp0 : 0 < p := by linarith
  have hpow : 1 < p ^ (x + 1) := one_lt_rpow hp (by linarith)
  dsimp [probability]
  rw [rpow_neg hp0.le]
  field_simp [(rpow_pos_of_pos hp0 (x + 1)).ne', show p ^ (x + 1) - 1 ≠ 0 by linarith]
  <;> ring

/-- The exact KL remainder at ANY real reference exponent; its linear term
vanishes at an interior critical point and survives at the boundary. -/
theorem price_difference_kl {p lam x t : ℝ} (hp : 1 < p) (hx : 1 ≤ x) (ht : 1 ≤ t) :
    priceObjective p lam x - priceObjective p lam t =
      bernoulliKL (probability p x) (probability p t) / (1 - probability p x) +
        (lam - 1 / (p ^ (x + 1) - 1)) * (t - x) * log p := by
  have hv := probability_mem hp hx
  have hu := probability_mem hp ht
  rw [bernoulli_scaled hv.1 hv.2 hu.1 hu.2, probability_odds hp hx]
  have hlogs : log (probability p x) - log (probability p t) = (t - x) * log p := by
    dsimp [probability]
    rw [log_rpow (by linarith : 0 < p), log_rpow (by linarith : 0 < p)]
    ring
  rw [hlogs]
  dsimp only [priceObjective]
  rw [benefit_log hp hx, benefit_log hp ht]
  ring

/-- Interior losses have the Bernoulli orientation C^-1 || p^(-t-1). -/
theorem active_loss {p lam t : ℝ} (hp : 1 < p) (hlam : 0 < lam)
    (hactive : p ^ (2 : ℕ) < cutoff lam) (ht : 1 ≤ t) :
    priceLoss p lam t =
      bernoulliKL (cutoff lam)⁻¹ (probability p t) / (1 - (cutoff lam)⁻¹) ∧
    priceLoss p lam t =
      log ((1 - (cutoff lam)⁻¹) / (1 - probability p t)) -
        lam * log (cutoff lam / p ^ (t + 1)) := by
  have hc : 1 < critical p lam := (critical_gt_one_iff hp hlam).mpr hactive
  have hb : boundary p lam = critical p lam := max_eq_right hc.le
  have hp0 : 0 < p := by linarith
  have hC0 : 0 < cutoff lam := by linarith [cutoff_gt_one hlam]
  have hv : probability p (critical p lam) = (cutoff lam)⁻¹ := by
    dsimp [probability]
    rw [rpow_neg hp0.le, critical_power hp hlam]
  have hvmem := probability_mem hp hc.le
  rw [hv] at hvmem
  have hprice : 1 / (p ^ (critical p lam + 1) - 1) = lam := by
    rw [critical_power hp hlam]
    simp [cutoff, hlam.ne']
  have hlogc : log (cutoff lam) = (critical p lam + 1) * log p := by
    rw [← critical_power hp hlam, log_rpow hp0]
  have hu := probability_mem hp ht
  constructor
  · dsimp only [priceLoss]
    rw [hb, price_difference_kl hp hc.le ht, hv, hprice]
    ring
  · dsimp only [priceLoss, priceObjective]
    rw [hb, benefit_log hp hc.le, benefit_log hp ht, hv,
      log_div (sub_pos.mpr hvmem.2).ne' (sub_pos.mpr hu.2).ne',
      log_div hC0.ne' (rpow_pos_of_pos hp0 _).ne', log_rpow hp0, hlogc]
    ring

/-- Inactive supported primes retain the boundary KL AND the nonnegative
linear excess price. The case p^2=C is included. -/
theorem inactive_loss {p lam t : ℝ} (hp : 1 < p) (hlam : 0 < lam)
    (hinactive : cutoff lam ≤ p ^ (2 : ℕ)) (ht : 1 ≤ t) :
    boundary p lam = 1 ∧ integerGap p lam = 0 ∧
      0 ≤ lam - 1 / (p ^ (2 : ℕ) - 1) ∧
      0 ≤ bernoulliKL (p ^ (-2 : ℝ)) (probability p t) / (1 - p ^ (-2 : ℝ)) ∧
      priceLoss p lam t =
        bernoulliKL (p ^ (-2 : ℝ)) (probability p t) / (1 - p ^ (-2 : ℝ)) +
          (lam - 1 / (p ^ (2 : ℕ) - 1)) * (t - 1) * log p := by
  have hc : critical p lam ≤ 1 := by
    by_contra h
    exact (not_lt_of_ge hinactive) ((critical_gt_one_iff hp hlam).mp (lt_of_not_ge h))
  have hb : boundary p lam = 1 := max_eq_left hc
  have hden : 0 < p ^ (2 : ℕ) - 1 := by nlinarith [sq_nonneg (p - 1)]
  have hinv : lam⁻¹ ≤ p ^ (2 : ℕ) - 1 := by dsimp [cutoff] at hinactive; linarith
  have hmul := mul_le_mul_of_nonneg_left hinv hlam.le
  rw [mul_inv_cancel₀ hlam.ne'] at hmul
  have hprice : 0 ≤ lam - 1 / (p ^ (2 : ℕ) - 1) := by
    apply sub_nonneg.mpr
    exact (div_le_iff₀ hden).mpr (by nlinarith)
  have hv : 0 < p ^ (-2 : ℝ) ∧ p ^ (-2 : ℝ) < 1 := by
    simpa [probability] using probability_mem hp (le_refl (1 : ℝ))
  have hu := probability_mem hp ht
  refine ⟨hb, ?_, hprice, ?_, ?_⟩
  · simp [integerGap, priceLoss, hb]
  · exact div_nonneg
      (D5.S0.Diagonal.MarginBound.bernoulliKL_nonneg hv.1 hv.2 hu.1 hu.2)
      (by linarith)
  · dsimp only [priceLoss]
    rw [hb, price_difference_kl hp (le_refl 1) ht]
    norm_num [probability, rpow_two]

/-- The explicit active formula requires only the two integers floor c and ceil c. -/
theorem active_integer_gap {p lam : ℝ} (hp : 1 < p) (hlam : 0 < lam)
    (hactive : p ^ (2 : ℕ) < cutoff lam) :
    integerGap p lam =
      min (bernoulliKL (cutoff lam)⁻¹ (probability p (⌊critical p lam⌋ : ℤ)) /
          (1 - (cutoff lam)⁻¹))
        (bernoulliKL (cutoff lam)⁻¹ (probability p (⌈critical p lam⌉ : ℤ)) /
          (1 - (cutoff lam)⁻¹)) := by
  have hc : 1 < critical p lam := (critical_gt_one_iff hp hlam).mpr hactive
  have hb : boundary p lam = critical p lam := max_eq_right hc.le
  have hf : (1 : ℤ) ≤ ⌊critical p lam⌋ := Int.le_floor.mpr (by simpa using hc.le)
  have hfR : (1 : ℝ) ≤ (⌊critical p lam⌋ : ℤ) := by exact_mod_cast hf
  have hcR : (1 : ℝ) ≤ (⌈critical p lam⌉ : ℤ) := hc.le.trans (Int.le_ceil _)
  rw [integerGap, hb, (active_loss hp hlam hactive hfR).1,
    (active_loss hp hlam hactive hcR).1]

end D5.S3.Arith.Robin.PriceRecord.BoundaryPrimePrice
