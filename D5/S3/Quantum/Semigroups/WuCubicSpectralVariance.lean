/- GID: D5/S3/Quantum/Semigroups/WuCubicSpectralVariance
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicSpectralVariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Entropy variance, thermal bounds, and directional cuts for Wu's cubic deficit. -/

import D5.S3.Entropy.EntropyDivergenceIdentity
import D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap
import D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import OmegaBuild.Commands

/-! The entropy gap in Wu's cubic deficit is the KL divergence from the uniform
law times the cubic mass. A spectral box bounds it by pairwise variance. The
thermal correction multiplies this gap by the positive part of an upper bound
on the signed coefficient. The directional cubic term is bounded using the
signed weight and combined marginal mass across each spectral cut. -/

compile_only_with_mathlib

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace D5.S3.Quantum.Semigroups.WuCubicSpectralVariance

open D5.S3.Divergence.ClassicalDPI (klDivergence)
open D5.S3.Entropy.EntropyDivergenceIdentity (kl_divergence_uniform_eq)
open D5.S3.Entropy.MaxEntropy (entropy_le_log_card shannonEntropy)
open WuRepeatedMiddleCubic (alpha)

/-- The unnormalized entropy gap from the uniform law. Zero masses contribute zero. -/
def entropyGap {ι : Type*} [Fintype ι] (m : ι → ℝ) : ℝ :=
  ∑ i, m i * Real.log ((Fintype.card ι : ℝ) * m i / ∑ j, m j)

/-- The half double sum of squared differences equals the quadratic mass defect. -/
theorem half_sum_pairwise_sq {ι : Type*} [Fintype ι] (m : ι → ℝ) :
    (∑ i, ∑ j, (m i - m j)^2) / 2 =
      (Fintype.card ι : ℝ) * (∑ i, (m i)^2) - (∑ i, m i)^2 := by
  classical
  simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
  rw [← Finset.sum_mul]
  rw [← Finset.mul_sum]
  ring

/-- The entropy gap is at most pairwise variance divided by the total mass. -/
theorem entropyGap_le_pairwise_sq {ι : Type*} [Fintype ι] (m : ι → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hM : 0 < ∑ i, m i) :
    entropyGap m ≤ ((∑ i, ∑ j, (m i - m j)^2) / 2) / (∑ i, m i) := by
  classical
  let M := ∑ i, m i
  have hcard : (0 : ℝ) < Fintype.card ι := by
    rcases isEmpty_or_nonempty ι with he | hn
    · let := he
      simp at hM
    · let := hn
      exact_mod_cast Fintype.card_pos (α := ι)
  rw [half_sum_pairwise_sq, entropyGap]
  change (∑ i, m i * Real.log ((Fintype.card ι : ℝ) * m i / M)) ≤ _
  calc
    _ ≤ ∑ i, ((Fintype.card ι : ℝ) * (m i)^2 / M - m i) := by
      apply Finset.sum_le_sum
      intro i _
      rcases (hm i).eq_or_lt with hz | hp
      · simp [← hz]
      have hlog := Real.log_le_sub_one_of_pos (div_pos (mul_pos hcard hp) hM)
      calc
        _ ≤ m i * ((Fintype.card ι : ℝ) * m i / M - 1) :=
          mul_le_mul_of_nonneg_left hlog (hm i)
        _ = _ := by ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum]
      change (Fintype.card ι : ℝ) * (∑ i, (m i)^2) / M - M = _
      change _ = ((Fintype.card ι : ℝ) * (∑ i, (m i)^2) - M^2) / M
      field_simp

/-- The gap scales the normalized Shannon entropy deficit by the total mass. -/
theorem entropyGap_eq_mass_mul_shannon_deficit {ι : Type*} [Fintype ι] [Nonempty ι]
    (m : ι → ℝ) (hm : ∀ i, 0 ≤ m i) (hM : 0 < ∑ i, m i) :
    let M := ∑ i, m i
    entropyGap m = M * (Real.log (Fintype.card ι) - shannonEntropy (fun i => m i / M)) := by
  intro M
  let p : ι → ℝ := fun i => m i / M
  have hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 := by
    refine ⟨fun i => div_nonneg (hm i) hM.le, ?_⟩
    simp only [p, ← Finset.sum_div]
    exact div_self hM.ne'
  change entropyGap m = M * (Real.log (Fintype.card ι) - shannonEntropy p)
  rw [← kl_divergence_uniform_eq p hp, klDivergence, entropyGap, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hscale : M * p i = m i := by
    dsimp [p]
    field_simp [show M ≠ 0 from hM.ne']
  have harg : p i / (Fintype.card ι : ℝ)⁻¹ = (Fintype.card ι : ℝ) * m i / M := by
    rw [div_inv_eq_mul]
    dsimp [p]
    ring
  rw [← mul_assoc, hscale, harg]

/-- The gap lies between zero and the total mass times the logarithm of the cardinality. -/
theorem entropyGap_bounds {ι : Type*} [Fintype ι] [Nonempty ι] (m : ι → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hM : 0 < ∑ i, m i) :
    0 ≤ entropyGap m ∧ entropyGap m ≤ (∑ i, m i) * Real.log (Fintype.card ι) := by
  classical
  let M := ∑ i, m i
  let p : ι → ℝ := fun i => m i / M
  have hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 := by
    refine ⟨fun i => div_nonneg (hm i) hM.le, ?_⟩
    simp only [p, ← Finset.sum_div]
    exact div_self hM.ne'
  have hentropy : 0 ≤ shannonEntropy p := by
    apply Finset.sum_nonneg
    intro i _
    have hpi : p i ≤ 1 := hp.2 ▸ Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)
    exact Real.negMulLog_nonneg (hp.1 i) hpi
  rw [entropyGap_eq_mass_mul_shannon_deficit m hm hM]
  change 0 ≤ M * (Real.log (Fintype.card ι) - shannonEntropy p) ∧
    M * (Real.log (Fintype.card ι) - shannonEntropy p) ≤ M * Real.log (Fintype.card ι)
  exact ⟨mul_nonneg hM.le (sub_nonneg.mpr (entropy_le_log_card p hp)),
    mul_le_mul_of_nonneg_left (sub_le_self _ hentropy) hM.le⟩

private theorem half_sum_pairwise_sq_eq_sum_lt {ι : Type*} [Fintype ι] [LinearOrder ι]
    (m : ι → ℝ) :
    (∑ i, ∑ j, (m i - m j)^2) / 2 = ∑ i, ∑ j with i < j, (m i - m j)^2 := by
  classical
  simp only [Finset.sum_filter]
  have hswap : (∑ i, ∑ j, if j < i then (m i - m j)^2 else 0) =
      ∑ i, ∑ j, if i < j then (m i - m j)^2 else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split <;> ring
  have hsplit : (∑ i, ∑ j, (m i - m j)^2) =
      (∑ i, ∑ j, if i < j then (m i - m j)^2 else 0) +
      (∑ i, ∑ j, if j < i then (m i - m j)^2 else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp [hij, hij.not_gt]
    · simp
    · simp [hji, hji.not_gt]
  rw [hsplit, hswap]
  ring

/-- A normalized variance bound for increasing masses in a coordinatewise interval box. -/
def boxVarianceUpper {ι : Type*} [Fintype ι] [LinearOrder ι]
    (lower upper : ι → ℝ) : ℝ :=
  (∑ i, ∑ j with i < j, (upper j - lower i)^2) / (∑ i, lower i)^2

theorem entropyGap_div_mass_le_box {ι : Type*} [Fintype ι] [LinearOrder ι]
    {m lower upper : ι → ℝ} (hm : ∀ i, 0 ≤ m i) (hmono : Monotone m)
    (hlo : ∀ i, lower i ≤ m i) (hhi : ∀ i, m i ≤ upper i)
    (hL : 0 < ∑ i, lower i) :
    entropyGap m / (∑ i, m i) ≤ boxVarianceUpper lower upper := by
  have hLM : (∑ i, lower i) ≤ ∑ i, m i := Finset.sum_le_sum fun i _ => hlo i
  have hM := hL.trans_le hLM
  have hgap := entropyGap_le_pairwise_sq m hm hM
  rw [half_sum_pairwise_sq_eq_sum_lt] at hgap
  have hsum : (∑ i, ∑ j with i < j, (m i - m j)^2) ≤
      ∑ i, ∑ j with i < j, (upper j - lower i)^2 := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j hj
    have hij := (Finset.mem_filter.mp hj).2
    rw [← neg_sq (m i - m j), neg_sub]
    exact pow_le_pow_left₀ (sub_nonneg.mpr (hmono hij.le)) (sub_le_sub (hhi j) (hlo i)) 2
  unfold boxVarianceUpper
  calc
    _ ≤ ((∑ i, ∑ j with i < j, (m i - m j)^2) / (∑ i, m i)) / (∑ i, m i) :=
      div_le_div_of_nonneg_right hgap hM.le
    _ ≤ ((∑ i, ∑ j with i < j, (upper j - lower i)^2) / (∑ i, m i)) / (∑ i, m i) :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hsum hM.le) hM.le
    _ ≤ _ := by
      rw [div_div, ← sq]
      exact div_le_div_of_nonneg_left (Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ => sq_nonneg _) (by positivity)
        (pow_le_pow_left₀ hL.le hLM 2)

/-- The ratio of the thermal symmetric coefficient to its tracial value. -/
def thermalLambda (t : ℝ) : ℝ := 1 / (1 + t^2 / (1 + t))

/-- The rational lower bound on the loss of the Wu entropy coefficient per `t^2`. -/
def alphaLossFactor (t : ℝ) : ℝ :=
  let w := t / (2 + t)
  (1 - w^2) / ((2 + t)^2 * (3 + w^2))

/-- The mass coefficient in the centered thermal identity at `r = 1 + t`. -/
def thermalMassCoefficient (t : ℝ) : ℝ :=
  let r := 1 + t
  9 / (4 * (1 + t + t^2)) * t^2 + alpha r * Real.log (4 * r^3 / (1 + r^3)^2)

private theorem alpha_nonneg_and_loss {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ alpha (1 + t) ∧ alpha (1 + t) ≤ 1 / 2 ∧
      t^2 * alphaLossFactor t ≤ 1 / 2 - alpha (1 + t) := by
  rcases ht.eq_or_lt with rfl | ht
  · norm_num [alpha, alphaLossFactor]
  let r := 1 + t
  let w := t / (2 + t)
  have hr : 1 < r := by dsimp [r]; linarith
  have hw : 0 < w := by dsimp [w]; positivity
  have hw1 : w < 1 := (div_lt_one (by positivity)).2 (by linarith)
  have hwden : 0 < 1 - w^2 := by
    nlinarith only [mul_pos (sub_pos.mpr hw1) (show 0 < 1 + w by positivity)]
  have h3w : 0 < 3 + w^2 := by positivity
  have hlog : 0 < Real.log r := Real.log_pos hr
  have hratio : (1 + w) / (1 - w) = r := by
    apply (div_eq_iff (sub_pos.mpr hw1).ne').2
    dsimp [w, r]
    field_simp [show 2 + t ≠ 0 by positivity]
    ring
  have hlow := Real.sum_range_le_log_div hw.le hw1 2
  have hhigh := Real.log_div_le_sum_range_add hw.le hw1 0
  rw [hratio] at hlow hhigh
  norm_num [Finset.sum_range_succ] at hlow hhigh
  have ha : alpha r = (3 * w / (3 + w^2)) / Real.log r := by
    simp only [alpha, hr.ne', ite_false]
    have hd : 0 < r^2 + r + 1 := by positivity
    field_simp [hlog.ne', h3w.ne', hd.ne']
    dsimp [w, r]
    field_simp [show 2 + t ≠ 0 by positivity]
    ring
  have hratioLoss : t^2 * alphaLossFactor t = w^2 * (1 - w^2) / (3 + w^2) := by
    change t^2 * ((1 - w^2) / ((2 + t)^2 * (3 + w^2))) = _
    calc
      _ = (t^2 / (2 + t)^2) * (1 - w^2) / (3 + w^2) := by rw [← div_div]; ring
      _ = _ := by rw [← div_pow]
  change 0 ≤ alpha r ∧ alpha r ≤ 1 / 2 ∧ t^2 * alphaLossFactor t ≤ 1 / 2 - alpha r
  rw [ha, hratioLoss]
  have hn : 0 ≤ w^2 * (1 - w^2) / (3 + w^2) := by positivity
  have hLoss : w^2 * (1 - w^2) / (3 + w^2) ≤
      1 / 2 - (3 * w / (3 + w^2)) / Real.log r := by
    rw [sub_div' hlog.ne', le_div_iff₀ hlog]
    calc
      _ ≤ (w^2 * (1 - w^2) / (3 + w^2)) * (2 * (w / (1 - w^2))) :=
        mul_le_mul_of_nonneg_left (by linarith only [hhigh]) hn
      _ = 2 * w^3 / (3 + w^2) := by field_simp [hwden.ne']
      _ ≤ 1 / 2 * Real.log r - 3 * w / (3 + w^2) := by
        have hl := mul_le_mul_of_nonneg_right hlow h3w.le
        apply (div_le_iff₀ h3w).2
        have hid : (3 * w / (3 + w^2)) * (3 + w^2) = 3 * w := div_mul_cancel₀ _ h3w.ne'
        rw [sub_mul, hid]
        nlinarith only [hl, pow_nonneg hw.le 5]
  exact ⟨by positivity, by linarith only [hn, hLoss], hLoss⟩

theorem alpha_loss_ge {t : ℝ} (ht : 0 ≤ t) :
    t^2 * alphaLossFactor t ≤ 1 / 2 - alpha (1 + t) :=
  (alpha_nonneg_and_loss ht).2.2

private theorem thermalDen_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    1 + a + a^2 ≤ 1 + b + b^2 := by
  linarith only [hab, pow_le_pow_left₀ ha hab 2]

private theorem alphaLossFactor_antitone {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    alphaLossFactor b ≤ alphaLossFactor a := by
  have hb := ha.trans hab
  let u := a / (2 + a)
  let v := b / (2 + b)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have huv : u ≤ v := by
    dsimp [u, v]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith only [hab]
  have hv : v < 1 := (div_lt_one (by positivity)).2 (by linarith)
  have hv2 : v^2 ≤ 1 := by
    simpa using pow_le_pow_left₀ (hu.trans huv) hv.le 2
  have huv2 := pow_le_pow_left₀ hu huv 2
  have hden : (2 + a)^2 * (3 + u^2) ≤ (2 + b)^2 * (3 + v^2) :=
    mul_le_mul
      (pow_le_pow_left₀ (by positivity) (add_le_add_right hab 2) 2)
      (add_le_add_right huv2 3) (by positivity) (by positivity)
  change (1 - v^2) / ((2 + b)^2 * (3 + v^2)) ≤ (1 - u^2) / ((2 + a)^2 * (3 + u^2))
  exact (div_le_div_of_nonneg_left (sub_nonneg.mpr hv2) (by positivity) hden).trans
    (div_le_div_of_nonneg_right (sub_le_sub_left huv2 1) (by positivity))

/-- The largest entropy penalty allowed by the thermal endpoint bounds, with zero as a floor. -/
def thermalEntropyPenalty (lo hi : ℝ) : ℝ :=
  max 0 (1 / (2 * (1 + lo + lo^2)) - alphaLossFactor hi)

theorem alpha_sub_thermalLambda_half_le {t lo hi : ℝ}
    (hlo : 0 ≤ lo) (hlt : lo ≤ t) (hth : t ≤ hi) :
    alpha (1 + t) - thermalLambda t / 2 ≤ t^2 * thermalEntropyPenalty lo hi := by
  have ht := hlo.trans hlt
  have hLambda : 1 / 2 - thermalLambda t / 2 = t^2 * (1 / (2 * (1 + t + t^2))) := by
    have hd : 0 < 1 + t^2 / (1 + t) := by positivity
    have he : 0 < 1 + t + t^2 := by positivity
    unfold thermalLambda
    field_simp [hd.ne', he.ne', show 1 + t ≠ 0 by positivity] <;> ring
  have hrecip : 1 / (2 * (1 + t + t^2)) ≤ 1 / (2 * (1 + lo + lo^2)) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left (thermalDen_mono hlo hlt) (by norm_num))
  have hcoeff : 1 / (2 * (1 + t + t^2)) - alphaLossFactor t ≤
      thermalEntropyPenalty lo hi :=
    (sub_le_sub hrecip (alphaLossFactor_antitone ht hth)).trans (le_max_right _ _)
  calc
    _ ≤ (1 / 2 - thermalLambda t / 2) - t^2 * alphaLossFactor t := by
      linarith only [alpha_loss_ge ht]
    _ = t^2 * (1 / (2 * (1 + t + t^2)) - alphaLossFactor t) := by rw [hLambda, mul_sub]
    _ ≤ _ := mul_le_mul_of_nonneg_left hcoeff (sq_nonneg t)

theorem thermalMassCoefficient_ge {t : ℝ} (ht : 0 ≤ t) :
    t^2 * (9 / (4 * (1 + t + t^2)) - 9 / 8) ≤ thermalMassCoefficient t := by
  let r := 1 + t
  let z := 3 * Real.log r / 2
  have hr : 1 ≤ r := by dsimp [r]; linarith
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hz0 : 0 ≤ z := by
    dsimp [z]
    exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hr)) (by norm_num)
  have hzt : z ≤ 3 * t / 2 := by
    have hl := Real.log_le_sub_one_of_pos hr0
    dsimp [z, r] at hl ⊢
    linarith only [hl]
  have hcosh : Real.cosh z = ((Real.exp z)^2 + 1) / (2 * Real.exp z) := by
    rw [Real.cosh_eq, Real.exp_neg]
    field_simp [(Real.exp_pos z).ne'] <;> ring
  have hexp : (Real.exp z)^2 = r^3 := by
    rw [← Real.exp_nat_mul, show (↑(2 : ℕ) : ℝ) * z = (↑(3 : ℕ) : ℝ) * Real.log r by
      push_cast
      dsimp [z]
      ring, Real.exp_nat_mul, Real.exp_log hr0]
  have hratio : 4 * r^3 / (1 + r^3)^2 = ((Real.cosh z)^2)⁻¹ := by
    rw [hcosh, ← hexp]
    have hd : 0 < (Real.exp z)^2 + 1 := by positivity
    field_simp [(Real.exp_pos z).ne', hd.ne'] <;> ring
  have hlog : -(z^2) ≤ Real.log (4 * r^3 / (1 + r^3)^2) := by
    rw [hratio, Real.log_inv, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    have h := Real.log_le_log (Real.cosh_pos z) (Real.cosh_le_exp_half_sq z)
    rw [Real.log_exp] at h
    linarith only [h]
  obtain ⟨ha0, ha, _⟩ := alpha_nonneg_and_loss ht
  have hterm : -(9 / 8) * t^2 ≤ alpha r * Real.log (4 * r^3 / (1 + r^3)^2) := calc
    _ ≤ (1 / 2) * (-(z^2)) := by
      nlinarith only [pow_le_pow_left₀ hz0 hzt 2]
    _ ≤ alpha r * (-(z^2)) := mul_le_mul_of_nonpos_right ha (neg_nonpos.mpr (sq_nonneg z))
    _ ≤ _ := mul_le_mul_of_nonneg_left hlog ha0
  change _ ≤ 9 / (4 * (1 + t + t^2)) * t^2 + alpha r * Real.log (4 * r^3 / (1 + r^3)^2)
  nlinarith only [hterm]

private theorem log_four_le : Real.log 4 ≤ 7 / 5 := by
  have h := Real.log_div_le_sum_range_add (x := 1 / 3) (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h
  rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
  linarith only [h]

/-! ## Directional spectral cuts -/

open WuCubicOccupationEnvelope (sym)
open WuCubicDirectedOccupationCap (Mat frameWeight rowImbalance frameWeight_rowImbalance
  frameVector emptyProbability fullProbability)
open private frameWeight_marginals from D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap

/-- Sum of weights with the target below the cut and the source above it. -/
def spectralCutWeight (W : Fin 4 → Fin 4 → ℝ) (k : Fin 3) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, if i ≤ k.castSucc ∧ k.castSucc < j then W i j else 0

/-- Half the signed crossing mass, positive for excess weight directed to higher roots. -/
def spectralCutImbalance (W : Fin 4 → Fin 4 → ℝ) (k : Fin 3) : ℝ :=
  (spectralCutWeight (fun i j => W j i) k - spectralCutWeight W k) / 2

/-- The successive gap at the cut. -/
def spectralGap (x : Fin 4 → ℝ) (k : Fin 3) : ℝ :=
  x k.succ - x k.castSucc

/-- Half the combined marginal mass of the smaller side of each cut. -/
def spectralCutCap (k : Fin 3) : ℝ := ![1, 2, 1] k

private theorem spectralGap_bounds {x : Fin 4 → ℝ} (hx : Monotone x) (k : Fin 3) :
    0 ≤ spectralGap x k ∧ spectralGap x k ≤ x 3 - x 0 :=
  ⟨sub_nonneg.mpr (hx Fin.castSucc_lt_succ.le),
    sub_le_sub (hx (Fin.le_last k.succ)) (hx (Fin.zero_le k.castSucc))⟩

private theorem cubic_eq_sum_spectral_cuts (W : Fin 4 → Fin 4 → ℝ) (x : Fin 4 → ℝ) :
    (∑ i, ∑ j, W i j * (x i - x j) ^ 3) =
      ∑ k : Fin 3, spectralGap x k *
        spectralCutWeight (fun i j => (W j i - W i j) * (x j - x i) ^ 2) k := by
  rw [Fin.sum_univ_three]
  simp (config := { decide := true }) only [spectralGap, spectralCutWeight, Fin.sum_univ_four,
    ite_true, ite_false, zero_add, add_zero,
    show (0 : Fin 3).castSucc = (0 : Fin 4) from rfl,
    show (1 : Fin 3).castSucc = (1 : Fin 4) from rfl,
    show (2 : Fin 3).castSucc = (2 : Fin 4) from rfl,
    show (0 : Fin 3).succ = (1 : Fin 4) from rfl,
    show (1 : Fin 3).succ = (2 : Fin 4) from rfl,
    show (2 : Fin 3).succ = (3 : Fin 4) from rfl]
  ring

private theorem spectralCut_square_lower {W : Fin 4 → Fin 4 → ℝ}
    {x : Fin 4 → ℝ} (hW : ∀ i j, 0 ≤ W i j) (hx : Monotone x) (k : Fin 3) :
    spectralGap x k ^ 2 * spectralCutWeight (fun i j => W j i) k -
        (x 3 - x 0) ^ 2 * spectralCutWeight W k ≤
      spectralCutWeight (fun i j => (W j i - W i j) * (x j - x i) ^ 2) k := by
  simp_rw [spectralCutWeight, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases hij : i ≤ k.castSucc ∧ k.castSucc < j
  · simp only [hij]
    have hsmall : spectralGap x k ≤ x j - x i :=
      sub_le_sub (hx (Fin.castSucc_lt_iff_succ_le.mp hij.2)) (hx hij.1)
    have hlarge : x j - x i ≤ x 3 - x 0 :=
      sub_le_sub (hx (Fin.le_last j)) (hx (Fin.zero_le i))
    have hgap := (spectralGap_bounds hx k).1
    have hpos := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hgap hsmall 2) (hW j i)
    have hneg := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (hgap.trans hsmall) hlarge 2) (hW i j)
    rw [sub_mul, mul_comm (W j i), mul_comm (W i j)]
    exact sub_le_sub hpos hneg
  · simp [hij]

/-- The signed cubic sum is bounded below cut by cut with the actual crossing mass. -/
theorem directional_spectral_cut_cubic_precursor {W : Fin 4 → Fin 4 → ℝ}
    {x : Fin 4 → ℝ} (hW : ∀ i j, 0 ≤ W i j) (hx : Monotone x) :
    (∑ k : Fin 3, spectralGap x k *
      ((spectralGap x k ^ 2 + (x 3 - x 0) ^ 2) * spectralCutImbalance W k -
        ((x 3 - x 0) ^ 2 - spectralGap x k ^ 2) * (spectralCutWeight (sym W) k / 2))) ≤
      ∑ i, ∑ j, W i j * (x i - x j) ^ 3 := by
  rw [cubic_eq_sum_spectral_cuts]
  apply Finset.sum_le_sum
  intro k _
  apply mul_le_mul_of_nonneg_left _ (spectralGap_bounds hx k).1
  have hsum : spectralCutWeight (sym W) k =
      spectralCutWeight (fun i j => W j i) k + spectralCutWeight W k := by
    simp_rw [spectralCutWeight, sym, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split <;> simp [add_comm]
  calc
    _ = spectralGap x k ^ 2 * spectralCutWeight (fun i j => W j i) k -
        (x 3 - x 0) ^ 2 * spectralCutWeight W k := by
      rw [hsum, spectralCutImbalance]
      ring
    _ ≤ _ := spectralCut_square_lower hW hx k

/-- For a nonnegative table with combined marginal two at each vertex, the
half crossing mass is at most one on each end cut and two on the middle cut. -/
theorem spectralCut_half_sum_le_cap {W : Fin 4 → Fin 4 → ℝ}
    (hW : ∀ i j, 0 ≤ W i j) (hrows : ∀ i, (∑ j, sym W i j) = 2) (k : Fin 3) :
    spectralCutWeight (sym W) k / 2 ≤ spectralCutCap k := by
  have h0 := hrows 0
  have h1 := hrows 1
  have h3 := hrows 3
  simp only [Fin.sum_univ_four, sym] at h0 h1 h3
  fin_cases k <;>
    simp (config := { decide := true }) only [spectralCutWeight, sym, Fin.sum_univ_four,
      ite_true, ite_false, zero_add, add_zero]
  · change _ ≤ (1 : ℝ)
    linarith only [h0, hW 0 0]
  · change _ ≤ (2 : ℝ)
    linarith only [h0, h1, hW 0 0, hW 0 1, hW 1 0, hW 1 1]
  · change _ ≤ (1 : ℝ)
    linarith only [h3, hW 3 3]

/-- Internal weights cancel in the difference of incoming and outgoing mass
over the lower side of any of the three cuts. -/
private theorem spectralCutImbalance_eq_rowImbalance (W : Fin 4 → Fin 4 → ℝ) (k : Fin 3) :
    spectralCutImbalance W k =
      -(∑ i : Fin 4, if i ≤ k.castSucc then rowImbalance W i else 0) / 2 := by
  fin_cases k <;>
    simp (config := { decide := true }) only [spectralCutImbalance, spectralCutWeight,
      rowImbalance, Fin.sum_univ_four, ite_true, ite_false, zero_add, add_zero] <;>
    ring

/-- In the physical frame the signed cut imbalance is the charge on the lower
side, with full occupation positive and empty occupation negative. -/
theorem spectralCutImbalance_frameWeight (U : unitary Mat) (k : Fin 3) :
    spectralCutImbalance (frameWeight U) k =
      ∑ i : Fin 4, if i ≤ k.castSucc then
        fullProbability (frameVector U i) - emptyProbability (frameVector U i) else 0 := by
  rw [spectralCutImbalance_eq_rowImbalance, ← Finset.sum_neg_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ≤ k.castSucc
  · simp only [hi, ite_true, frameWeight_rowImbalance]
    ring
  · simp [hi]

/-- The directional cubic estimate used by the hot-window certificate.
It applies to every complex unitary frame and every sorted tuple, including
repeated and zero cube roots. -/
theorem directional_spectral_cut_cubic_lower_bound (U : unitary Mat) {x : Fin 4 → ℝ}
    (hx : Monotone x) :
    (∑ k : Fin 3, spectralGap x k *
      ((spectralGap x k ^ 2 + (x 3 - x 0) ^ 2) * spectralCutImbalance (frameWeight U) k -
        ((x 3 - x 0) ^ 2 - spectralGap x k ^ 2) * spectralCutCap k)) ≤
      ∑ i, ∑ j, frameWeight U i j * (x i - x j) ^ 3 := by
  have hW (i j : Fin 4) : 0 ≤ frameWeight U i j :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hrows (i : Fin 4) : (∑ j, sym (frameWeight U) i j) = 2 := by
    simp only [sym, Finset.sum_add_distrib, (frameWeight_marginals U i).1,
      (frameWeight_marginals U i).2]
    ring
  refine le_trans ?_ (directional_spectral_cut_cubic_precursor hW hx)
  apply Finset.sum_le_sum
  intro k _
  obtain ⟨hgap, hspan⟩ := spectralGap_bounds hx k
  have hresidual := sub_nonneg.mpr (pow_le_pow_left₀ hgap hspan 2)
  exact mul_le_mul_of_nonneg_left
    (sub_le_sub_left
      (mul_le_mul_of_nonneg_left (spectralCut_half_sum_le_cap hW hrows k) hresidual) _) hgap

#print axioms directional_spectral_cut_cubic_precursor
#print axioms spectralCut_half_sum_le_cap
#print axioms spectralCutImbalance_frameWeight
#print axioms directional_spectral_cut_cubic_lower_bound

/-- The centered thermal estimate on an increasing four-root spectral box.
The normalized entropy bound is the smaller of the variance bound and the
uniform cap. The signed entropy coefficient is retained on the deficit side. -/
theorem cubic_thermal_lower_bound {x lower upper : Fin 4 → ℝ} {t lo hi : ℝ}
    (hx : ∀ i, 0 ≤ x i) (hmono : Monotone x)
    (hxlo : ∀ i, lower i ≤ x i) (hxhi : ∀ i, x i ≤ upper i)
    (hL : 0 < ∑ i, (lower i)^3)
    (hlo : 0 ≤ lo) (hlt : lo ≤ t) (hth : t ≤ hi) :
    let m := fun i => (x i)^3
    let M := ∑ i, m i
    let B := min (7 / 5) (boxVarianceUpper (fun i => (lower i)^3) (fun i => (upper i)^3))
    (9 / (4 * (1 + hi + hi^2)) - 9 / 8 - B * thermalEntropyPenalty lo hi) * t^2 * M ≤
      thermalMassCoefficient t * M - (alpha (1 + t) - thermalLambda t / 2) * entropyGap m := by
  intro m M B
  have ht := hlo.trans hlt
  have hcube : Monotone (fun u : ℝ => u^3) :=
    (show Odd (3 : ℕ) by decide).strictMono_pow.monotone
  have hM : 0 < M := hL.trans_le <| Finset.sum_le_sum fun i _ => hcube (hxlo i)
  have hm : ∀ i, 0 ≤ m i := fun i => pow_nonneg (hx i) _
  obtain ⟨hgap0, hgapLog⟩ := entropyGap_bounds m hm hM
  have hbox := entropyGap_div_mass_le_box hm
    (hcube.comp hmono) (fun i => hcube (hxlo i)) (fun i => hcube (hxhi i)) hL
  have hgap : entropyGap m ≤ B * M := by
    apply (div_le_iff₀ hM).1
    apply le_min _ hbox
    apply (div_le_iff₀ hM).2
    have hlog : Real.log (Fintype.card (Fin 4)) ≤ 7 / 5 := by simpa using log_four_le
    calc
      entropyGap m ≤ M * (7 / 5) := hgapLog.trans (mul_le_mul_of_nonneg_left hlog hM.le)
      _ = _ := mul_comm _ _
  have hPenalty0 : 0 ≤ thermalEntropyPenalty lo hi := le_max_left _ _
  have hpenalty : (alpha (1 + t) - thermalLambda t / 2) * entropyGap m ≤
      (t^2 * thermalEntropyPenalty lo hi) * (B * M) :=
    (mul_le_mul_of_nonneg_right (alpha_sub_thermalLambda_half_le hlo hlt hth) hgap0).trans
      (mul_le_mul_of_nonneg_left hgap (mul_nonneg (sq_nonneg t) hPenalty0))
  have hbase : 9 / (4 * (1 + hi + hi^2)) ≤ 9 / (4 * (1 + t + t^2)) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left (thermalDen_mono ht hth) (by norm_num))
  have hmass := ((mul_le_mul_of_nonneg_left (sub_le_sub_right hbase (9 / 8)) (sq_nonneg t)).trans
      (thermalMassCoefficient_ge ht))
  have hmassM := mul_le_mul_of_nonneg_right hmass hM.le
  nlinarith only [hmassM, hpenalty]

end D5.S3.Quantum.Semigroups.WuCubicSpectralVariance
