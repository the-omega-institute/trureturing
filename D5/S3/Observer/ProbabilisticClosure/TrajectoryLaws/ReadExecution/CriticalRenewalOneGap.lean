/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalOneGap
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalOneGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normalized critical renewal terminal rewards and signed adjacent-grid evidence. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.CriticalRenewalSource
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalTable

/-! Source-normalized terminal phase statistics and their adjacent-grid evidence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Finset
open scoped ENNReal BigOperators NNReal

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalOneGap


def reward (r J : ℕ) (z : Fin (J + 1)) : ℝ :=
  if z.val < J then 1 / (2 : ℝ)^(r*(z.val+1)) else 0

def phase (J : ℕ) (f : PMF ℕ) : PMF (Fin (J + 1)) :=
  f.bind (GeometricPhaseOccupation.finiteCappedLaw J)

def average {J : ℕ} (p : PMF (Fin (J + 1))) (v : Fin (J + 1) → ℝ) : ℝ :=
  ∑ z, (p z).toReal * v z

def grid (r J : ℕ) : ℝ := (J : ℝ)/(2 : ℝ)^(r*J)

private lemma pmf_sum_real {α : Type*} [Fintype α] (p : PMF α) :
    ∑ z, (p z).toReal = 1 := by
  have h := congrArg ENNReal.toReal p.tsum_coe
  rw [ENNReal.tsum_toReal_eq p.apply_ne_top, tsum_fintype, ENNReal.toReal_one] at h
  exact h

private lemma average_nonneg {J : ℕ} (p : PMF (Fin (J + 1)))
    (v : Fin (J + 1) → ℝ) (hv : ∀ z, 0 ≤ v z) : 0 ≤ average p v :=
  sum_nonneg fun z _ => mul_nonneg ENNReal.toReal_nonneg (hv z)

private lemma average_le {J : ℕ} (p : PMF (Fin (J + 1)))
    (v : Fin (J + 1) → ℝ) (C : ℝ) (hv : ∀ z, v z ≤ C) :
    average p v ≤ C := by
  calc
    _ ≤ ∑ z, (p z).toReal * C :=
      sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hv z) ENNReal.toReal_nonneg
    _ = C := by rw [← sum_mul, pmf_sum_real, one_mul]

private lemma reward_bounds (r J : ℕ) (hr : 1 ≤ r) (z : Fin (J + 1)) :
    0 ≤ reward r J z ∧ reward r J z ≤ 1/(2 : ℝ)^r ∧
      reward r J z ≤ 1/2 := by
  have hpow : (2 : ℝ)^r ≤ (2 : ℝ)^(r*(z.val+1)) :=
    pow_le_pow_right₀ (by norm_num) (Nat.le_mul_of_pos_right _ (by omega))
  have htwo : (2 : ℝ) ≤ (2 : ℝ)^r := by
    simpa using pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num) hr
  unfold reward
  split_ifs <;> constructor <;> try positivity
  · constructor
    · exact one_div_le_one_div_of_le (by positivity) hpow
    · exact one_div_le_one_div_of_le (by norm_num) (htwo.trans hpow)
  · constructor <;> positivity

private lemma discounted_real (m : ℕ) (s : ℝ) (k : ℕ) :
    (GeometricPhaseOccupation.discountedWeight m s k).toReal = CriticalRenewalSource.term m s k := by
  by_cases hk : k = 0
  · simp [GeometricPhaseOccupation.discountedWeight, CriticalRenewalSource.term, hk]
  · simp [GeometricPhaseOccupation.discountedWeight, CriticalRenewalSource.term, hk, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal (Real.exp_nonneg _)]

private lemma occupation_series (m J : ℕ) (j : Fin J) (s eta : ℝ)
    (hs : 0 < s) (hscale : s*(2 : ℝ)^J ≤ eta) (heta : eta ≤ 1) :
    Summable (fun k => CriticalRenewalSource.term m s k *
      (GeometricPhaseOccupation.finiteCappedLaw J k j.castSucc).toReal) ∧
    (∑' k, CriticalRenewalSource.term m s k *
      (GeometricPhaseOccupation.finiteCappedLaw J k j.castSucc).toReal) = GeometricPhaseOccupation.occupation m s (j.val+1) ∧
    GeometricPhaseOccupation.lowerConstant m * (2 : ℝ)^((j.val+1)*(m+1)) ≤
      GeometricPhaseOccupation.occupation m s (j.val+1) ∧
    GeometricPhaseOccupation.occupation m s (j.val+1) ≤
      GeometricPhaseOccupation.upperConstant m * (2 : ℝ)^((j.val+1)*(m+1)) := by
  have hj : j.val+1 ≤ J := by omega
  have hsj : s*(2 : ℝ)^(j.val+1) ≤ eta :=
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num) hj) hs.le).trans hscale
  have h := GeometricPhaseOccupation.uniform_discounted_phase_occupation m (j.val+1) (by omega)
    s eta hs hsj heta
  have he := h.2.2.2.2.2.2.2 J hj
  have hcast : (⟨j.val+1-1, by omega⟩ : Fin (J + 1)) = j.castSucc :=
    Fin.ext (by simp)
  rw [hcast] at he
  have hf : (∑' k, GeometricPhaseOccupation.discountedWeight m s k *
      GeometricPhaseOccupation.finiteCappedLaw J k j.castSucc) ≠ ⊤ := by
    exact he.trans_ne h.2.2.2.1
  have hh := ENNReal.hasSum_toReal hf
  simp only [ENNReal.toReal_mul, discounted_real] at hh
  refine ⟨hh.summable, ?_, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩
  change _ = (GeometricPhaseOccupation.actualOccupation
    (GeometricPhaseOccupation.discountedWeight m s) ((j.val+1)-1)).toReal
  rw [← he, ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hf)]
  simp only [ENNReal.toReal_mul, discounted_real]

private lemma phase_live_mass (r J : ℕ) (hr : 1 ≤ r) (c s eta : ℝ)
    (hc : 0 < c) (hs : 0 < s) (hscale : s*(2 : ℝ)^J ≤ eta) (heta : eta ≤ 1)
    (i : Bool) (j : Fin J) :
    (phase J (CriticalRenewalSource.gapLaw r hr c hc i s hs) j.castSucc).toReal =
      (GeometricPhaseOccupation.occupation (2*r-1) s (j.val+1) +
        if i then c*GeometricPhaseOccupation.occupation (r-1) s (j.val+1) else 0) /
        CriticalRenewalSource.normalizer r c i s := by
  have hsrc := (CriticalRenewalSource.source_laws r hr c hc s hs).1.1 i
  have he (k : ℕ) : (CriticalRenewalSource.gapLaw r hr c hc i s hs k).toReal = CriticalRenewalSource.density r c i s k :=
    ENNReal.toReal_ofReal (hsrc.density_nonnegative k)
  have hd := occupation_series (2*r-1) J j s eta hs hscale heta
  have hl := occupation_series (r-1) J j s eta hs hscale heta
  have hb := ENNReal.hasSum_toReal
    (show (∑' k, CriticalRenewalSource.gapLaw r hr c hc i s hs k *
      GeometricPhaseOccupation.finiteCappedLaw J k j.castSucc) ≠ ⊤ from
        by rw [← PMF.bind_apply]; exact (phase J _).apply_ne_top _)
  simp only [ENNReal.toReal_mul, he] at hb
  rw [phase, PMF.bind_apply, ENNReal.tsum_toReal_eq (fun k =>
    ENNReal.mul_ne_top ((CriticalRenewalSource.gapLaw r hr c hc i s hs).apply_ne_top k)
      ((GeometricPhaseOccupation.finiteCappedLaw J k).apply_ne_top j.castSucc))]
  simp only [ENNReal.toReal_mul, he]
  simp only [CriticalRenewalSource.density, CriticalRenewalSource.weight, add_div, mul_add, add_mul, div_mul_eq_mul_div]
  cases i with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero, zero_div, zero_mul]
    rw [tsum_div_const, hd.2.1]
  | true =>
    simp only [↓reduceIte]
    have hs2 := hl.1.mul_left c
    rw [Summable.tsum_add (hd.1.div_const _) (by simpa only [mul_assoc] using hs2.div_const _),
      tsum_div_const, hd.2.1, tsum_div_const]
    simp_rw [mul_assoc, tsum_mul_left, hl.2.1]

open CriticalRenewalSource GeometricPhaseOccupation CriticalRenewalTable

/-- A single terminal reward is powered before it is averaged. -/
def rewardMean (r J : ℕ) (f : PMF ℕ) : ℝ :=
  average (phase J f) (reward r J)

def occupationReward (r m J : ℕ) (s : ℝ) (p : ℕ) : ℝ :=
  ∑ j : Fin J, (1/(2 : ℝ)^(r*(j.val+1)))^p * occupation m s (j.val+1)

private lemma reward_moment_formula (r J : ℕ) (hr : 1 ≤ r) (c s eta : ℝ)
    (hc : 0 < c) (hs : 0 < s) (hscale : s*(2 : ℝ)^J ≤ eta) (heta : eta ≤ 1)
    (i : Bool) (p : ℕ) (hp : p ≠ 0) :
    average (phase J (gapLaw r hr c hc i s hs)) (fun z => (reward r J z)^p) =
      (occupationReward r (2*r-1) J s p +
        if i then c*occupationReward r (r-1) J s p else 0) / normalizer r c i s := by
  rw [average, Fin.sum_univ_castSucc]
  simp only [reward, Fin.val_last, lt_self_iff_false, ↓reduceIte,
    zero_pow hp, mul_zero, add_zero, Fin.val_castSucc]
  simp only [show ∀ j : Fin J, j.val < J from fun j => j.isLt, ↓reduceIte]
  simp_rw [phase_live_mass r J hr c s eta hc hs hscale heta]
  cases i with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
    rw [occupationReward, sum_div]
    apply sum_congr rfl
    intro j _
    ring
  | true =>
    simp only [↓reduceIte]
    simp only [occupationReward, mul_sum, ← sum_add_distrib, sum_div]
    apply sum_congr rfl
    intro j _
    ring

private lemma occupation_mono (r J : ℕ) (j : Fin J) (s eta : ℝ)
    (hs : 0 < s) (hscale : s*(2 : ℝ)^J ≤ eta) (heta : eta ≤ 1) :
    occupation (r-1) s (j.val+1) ≤ occupation (2*r-1) s (j.val+1) := by
  have hl := occupation_series (r-1) J j s eta hs hscale heta
  have hd := occupation_series (2*r-1) J j s eta hs hscale heta
  rw [← hl.2.1, ← hd.2.1]
  apply hl.1.tsum_le_tsum _ hd.1
  intro k
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  by_cases hk : k = 0
  · simp [term, hk]
  · simp only [term, hk, ↓reduceIte]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    exact pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ k by omega))
      (by omega : r-1 ≤ 2*r-1)

private lemma occupation_reward_mono (r J : ℕ) (s eta : ℝ)
    (hs : 0 < s) (hscale : s*(2 : ℝ)^J ≤ eta) (heta : eta ≤ 1) (p : ℕ) :
    occupationReward r (r-1) J s p ≤ occupationReward r (2*r-1) J s p := by
  apply sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (occupation_mono r J j s eta hs hscale heta) (by positivity)

private lemma small_reward_bounds (r J : ℕ) (hr : 1 ≤ r) (s eta : ℝ)
    (hs : 0 < s) (hscale : s*(2 : ℝ)^J ≤ eta) (heta : eta ≤ 1) :
    lowerConstant (r-1)*(J : ℝ) ≤ occupationReward r (r-1) J s 1 ∧
      occupationReward r (r-1) J s 1 ≤ upperConstant (r-1)*(J : ℝ) := by
  have he : r-1+1 = r := by omega
  have hterm (j : Fin J) :
      lowerConstant (r-1) ≤
        (1/(2 : ℝ)^(r*(j.val+1))) * occupation (r-1) s (j.val+1) ∧
      (1/(2 : ℝ)^(r*(j.val+1))) * occupation (r-1) s (j.val+1) ≤
        upperConstant (r-1) := by
    have h := occupation_series (r-1) J j s eta hs hscale heta
    have ht : 0 < (2 : ℝ)^(r*(j.val+1)) := by positivity
    rw [he, Nat.mul_comm (j.val+1) r] at h
    constructor
    · have hh := (le_div_iff₀ ht).2 h.2.2.1
      simpa [div_eq_mul_inv, mul_comm] using hh
    · have hh := (div_le_iff₀ ht).2 h.2.2.2
      simpa [div_eq_mul_inv, mul_comm] using hh
  constructor
  · simpa [occupationReward, mul_comm] using
      (sum_le_sum (s := univ) fun j _ => (hterm j).1)
  · simpa [occupationReward, mul_comm] using
      (sum_le_sum (s := univ) fun j _ => (hterm j).2)

private lemma dyadic_sum (r J : ℕ) (hr : 1 ≤ r) :
    (∑ j : Fin J, (2 : ℝ)^(r*(j.val+1))) ≤
      (2 : ℝ)^(r*J)/(1-1/(2 : ℝ)^r) := by
  let t : ℝ := (2 : ℝ)^r
  have ht : 1 < t := one_lt_pow₀ (by norm_num) (by omega)
  have hid (n : ℕ) :
      (∑ j : Fin n, t^(j.val+1))*(t-1) = t*(t^n-1) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [add_mul, ih, pow_succ]
      ring
  have hden : 0 < 1-1/t := sub_pos.mpr ((div_lt_one (by linarith)).2 ht)
  apply (le_div_iff₀ hden).2
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
  have he : (∑ j : Fin J, t^(j.val+1))*(1-1/t) = t^J-1 := by
    apply (mul_right_inj' ht0).1
    calc
      t*((∑ j : Fin J, t^(j.val+1))*(1-1/t)) =
          (∑ j : Fin J, t^(j.val+1))*(t-1) := by field_simp <;> ring
      _ = t*(t^J-1) := hid J
  have hpow (n : ℕ) : t^n = (2 : ℝ)^(r*n) := (pow_mul _ _ _).symm
  simpa only [← hpow] using (show
    (∑ j : Fin J, t^(j.val+1))*(1-1/t) ≤ t^J by rw [he]; linarith)

private lemma large_reward_bounds (r J : ℕ) (hr : 1 ≤ r) (s eta : ℝ)
    (hs : 0 < s) (hscale : s*(2 : ℝ)^J ≤ eta) (heta : eta ≤ 1) :
    occupationReward r (2*r-1) J s 1 ≤
        (upperConstant (2*r-1)/(1-1/(2 : ℝ)^r))*(2 : ℝ)^(r*J) ∧
      occupationReward r (2*r-1) J s 2 ≤ upperConstant (2*r-1)*(J : ℝ) := by
  have he : 2*r-1+1 = 2*r := by omega
  have hterm (j : Fin J) :
      (1/(2 : ℝ)^(r*(j.val+1))) * occupation (2*r-1) s (j.val+1) ≤
        upperConstant (2*r-1)*(2 : ℝ)^(r*(j.val+1)) ∧
      (1/(2 : ℝ)^(r*(j.val+1)))^2 * occupation (2*r-1) s (j.val+1) ≤
        upperConstant (2*r-1) := by
    have h := (occupation_series (2*r-1) J j s eta hs hscale heta).2.2.2
    have hp : (2 : ℝ)^((j.val+1)*(2*r-1+1)) =
        ((2 : ℝ)^(r*(j.val+1)))^2 := by
      rw [← pow_mul, he]
      congr 1
      ring
    rw [hp] at h
    have ht : 0 < (2 : ℝ)^(r*(j.val+1)) := by positivity
    constructor
    · have hh := (div_le_iff₀ ht).2 (show occupation (2*r-1) s (j.val+1) ≤
        (upperConstant (2*r-1)*(2 : ℝ)^(r*(j.val+1))) *
          (2 : ℝ)^(r*(j.val+1)) by nlinarith)
      simpa [div_eq_mul_inv, mul_comm] using hh
    · have hh := (div_le_iff₀ (sq_pos_of_pos ht)).2 h
      simpa [div_eq_mul_inv, mul_comm, inv_pow] using hh
  constructor
  · calc
      _ ≤ ∑ j : Fin J, upperConstant (2*r-1)*(2 : ℝ)^(r*(j.val+1)) := by
        simpa [occupationReward] using sum_le_sum (s := univ) (fun j _ => (hterm j).1)
      _ ≤ upperConstant (2*r-1) * ((2 : ℝ)^(r*J)/(1-1/(2 : ℝ)^r)) := by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left (dyadic_sum r J hr) (by unfold upperConstant; positivity)
      _ = _ := by ring
  · simpa [occupationReward, mul_comm] using sum_le_sum (s := univ) (fun j _ => (hterm j).2)

def lowerCell (delta x : ℝ) : ℤ := ⌊x/delta⌋
def upperProbability (delta x : ℝ) : ℝ := x/delta - (lowerCell delta x : ℝ)

def roundedTick {J : ℕ} (v : Fin (J+1) → ℝ) (theta delta : ℝ) : Tick J where
  lower z := lowerCell delta (v z-theta)
  prob z := ⟨upperProbability delta (v z-theta), Int.fract_nonneg _⟩
  prob_le_one z := by
    exact_mod_cast (Int.fract_lt_one ((v z-theta)/delta)).le

private lemma signed_rounding (delta x : ℝ) (hd : 0 < delta) :
    let n : ℝ := lowerCell delta x
    let p := upperProbability delta x
    0 ≤ p ∧ p < 1 ∧
    (1-p)*(delta*n)+p*(delta*(n+1)) = x ∧
    (1-p)*(delta*n)^2+p*(delta*(n+1))^2 =
      x^2+delta^2*p*(1-p) ∧
    delta^2*p*(1-p) ≤ delta*|x| ∧
    (∀ b : Bool, |delta*(n+if b then 1 else 0)| ≤ |x|+delta) := by
  intro n p
  have hp0 : 0 ≤ p := Int.fract_nonneg _
  have hp1 : p < 1 := Int.fract_lt_one _
  have ht : delta*(n+p) = x := by
    dsimp [n,p,upperProbability]
    field_simp
    ring
  have hnlo : delta*n ≤ x := by nlinarith
  have hnhi : x ≤ delta*(n+1) := by nlinarith
  have hv : p*(1-p) ≤ |x|/delta := by
    by_cases hx : 0 ≤ x
    · have hn : 0 ≤ n := by
        dsimp [n,lowerCell]
        exact_mod_cast Int.floor_nonneg.2 (div_nonneg hx hd.le)
      rw [abs_of_nonneg hx]
      have hpt : p ≤ x/delta := by
        dsimp [p,upperProbability,n] at *
        linarith
      nlinarith [sq_nonneg p]
    · have hn : n+1 ≤ 0 := by
        have hfl : lowerCell delta x < 0 := Int.floor_lt.2 (by simpa only [Int.cast_zero] using div_neg_of_neg_of_pos (lt_of_not_ge hx) hd)
        have hni : lowerCell delta x + 1 ≤ 0 := by omega
        change (lowerCell delta x : ℝ)+1 ≤ 0
        exact_mod_cast hni
      rw [abs_of_neg (lt_of_not_ge hx)]
      have hpt : 1-p ≤ -x/delta := by
        dsimp [p,upperProbability]
        dsimp [n] at hn
        rw [neg_div]
        linarith
      nlinarith [sq_nonneg (1-p)]
  refine ⟨hp0,hp1,by nlinarith,by rw [← ht]; ring,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_left hv (sq_nonneg delta)
    have he : delta^2*(|x|/delta) = delta*|x| := by field_simp <;> ring
    nlinarith [he]
  · intro b
    have habs := abs_le.mp (le_refl |x|)
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, add_zero, mul_add, mul_one]
    · apply abs_le.2
      constructor <;> nlinarith
    · apply abs_le.2
      constructor <;> nlinarith

private lemma occupation_reward_nonneg (r m J : ℕ) (s : ℝ) (p : ℕ) :
    0 ≤ occupationReward r m J s p := by
  apply sum_nonneg
  intro j _
  exact mul_nonneg (by positivity) ENNReal.toReal_nonneg

private lemma quotient_nonneg (r : ℕ) (s : ℝ) : 0 ≤ quotient r s := by
  apply div_nonneg <;> apply tsum_nonneg <;> intro k <;>
    unfold term <;> split_ifs <;> positivity

private lemma exact_contrast (r J : ℕ) (hr : 1 ≤ r) (c s eta : ℝ)
    (hc : 0 < c) (hs : 0 < s) (hscale : s*(2 : ℝ)^J ≤ eta) (heta : eta ≤ 1) :
    rewardMean r J (gapLaw r hr c hc true s hs) -
      rewardMean r J (gapLaw r hr c hc false s hs) =
      c / normalizer r c true s *
        (occupationReward r (r-1) J s 1 -
          quotient r s * occupationReward r (2*r-1) J s 1) := by
  have h1 := reward_moment_formula r J hr c s eta hc hs hscale heta true 1 one_ne_zero
  have h0 := reward_moment_formula r J hr c s eta hc hs hscale heta false 1 one_ne_zero
  simp only [pow_one, ↓reduceIte, Bool.false_eq_true, add_zero] at h0 h1
  change rewardMean r J _ = _ at h0 h1
  rw [h1,h0]
  have hZ := (source_laws r hr c hc s hs).1.2.1
  have hp0 := ((source_laws r hr c hc s hs).1.1 false).normalizer_positive
  have hp1 := ((source_laws r hr c hc s hs).1.1 true).normalizer_positive
  apply (mul_right_inj' (mul_ne_zero hp0.ne' hp1.ne')).mp
  field_simp
  nlinarith [hZ]

private lemma source_reward_bounds (r : ℕ) (hr : 1 ≤ r) (c : ℝ) (hc : 0 < c) :
    ∃ eta sStar Dlo Dhi Cmean Csecond : ℝ,
      0 < eta ∧ eta < 1 ∧ 0 < sStar ∧ sStar < 1 ∧
      0 < Dlo ∧ 0 < Dhi ∧ 0 < Cmean ∧ 0 < Csecond ∧
      ∀ s : ℝ, 0 < s → s < sStar → ∀ J : ℕ, 1 ≤ J →
        s*(2 : ℝ)^J ≤ eta →
        let m := fun i => rewardMean r J (gapLaw r hr c hc i s ‹0 < s›)
        let I := s^(2*r)*(J : ℝ)
        Dlo*I ≤ m true-m false ∧ m true-m false ≤ Dhi*I ∧
        (∀ i, 0 ≤ m i ∧ m i ≤ Cmean*s^(2*r)*(2 : ℝ)^(r*J) ∧
          average (phase J (gapLaw r hr c hc i s ‹0 < s›)) (fun z => (reward r J z)^2)
            ≤ Csecond*I) := by
  obtain ⟨sStar,zlo,zhi,G,Cmu,Cbeta,hsStar,hsStar1,hzlo,hzhi,hG,hCmu,hCbeta,hscalar⟩ :=
    common_scalar_neighborhood r hr c hc
  let b := lowerConstant (r-1)
  let B := upperConstant (r-1)
  let Cstar := upperConstant (2*r-1)/(1-1/(2 : ℝ)^r)
  have hb : 0 < b := by dsimp [b,lowerConstant]; positivity
  have hB : 0 < B := by dsimp [B,upperConstant]; positivity
  have ht : 1 < (2 : ℝ)^r := one_lt_pow₀ (by norm_num) (by omega)
  have hden : 0 < 1-1/(2 : ℝ)^r := by
    apply sub_pos.2
    exact (div_lt_one (by positivity)).2 ht
  have hCstar : 0 < Cstar := div_pos (by unfold upperConstant; positivity) hden
  let eta := min (1/2 : ℝ) (b/(2*G*Cstar))
  have heta : 0 < eta := lt_min (by norm_num) (div_pos hb (by positivity))
  have heta1 : eta < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hsmall : G*Cstar*eta^r ≤ b/2 := by
    have hp := pow_le_of_le_one heta.le heta1.le (by omega : r ≠ 0)
    have he := (le_div_iff₀ (by positivity : 0 < 2*G*Cstar)).mp (min_le_right (1/2) _)
    have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ G*Cstar by positivity)
    nlinarith
  refine ⟨eta,sStar,c*b/(2*zhi),c*B/zlo,(1+c)*Cstar/zlo,
    (1+c)*upperConstant (2*r-1)/zlo,heta,heta1,hsStar,hsStar1,
    by positivity,by positivity,by positivity,
    by unfold upperConstant; positivity,?_⟩
  intro s hs hss J hJ hscale m I
  have hsc := hscalar s hs hss
  have hp : 0 < s^(2*r) := pow_pos hs _
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hQ := small_reward_bounds r J hr s eta hs hscale heta1.le
  have hR := large_reward_bounds r J hr s eta hs hscale heta1.le
  let Q := occupationReward r (r-1) J s 1
  let R := occupationReward r (2*r-1) J s 1
  have hQlo : b*(J : ℝ) ≤ Q := hQ.1
  have hQhi : Q ≤ B*(J : ℝ) := hQ.2
  have hRhi : R ≤ Cstar*(2 : ℝ)^(r*J) := hR.1
  have hR0 : 0 ≤ R := occupation_reward_nonneg _ _ _ _ _
  have hg0 : 0 ≤ quotient r s := quotient_nonneg _ _
  have hcorr : quotient r s * R ≤ b/2 := by
    calc
      _ ≤ (G*s^r)*(Cstar*(2 : ℝ)^(r*J)) :=
        mul_le_mul hsc.2 hRhi hR0 (by positivity)
      _ = G*Cstar*(s*(2 : ℝ)^J)^r := by rw [mul_pow, ← pow_mul]; ring_nf
      _ ≤ G*Cstar*eta^r := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hscale r) (by positivity)
      _ ≤ b/2 := hsmall
  have hbrace0 : b/2*(J : ℝ) ≤ Q-quotient r s*R := by
    nlinarith [mul_le_mul_of_nonneg_left hJr hb.le]
  have hbrace1 : Q-quotient r s*R ≤ B*(J : ℝ) := by
    nlinarith [mul_nonneg hg0 hR0]
  have hcontrast : m true-m false = c*(1/normalizer r c true s)*
      (Q-quotient r s*R) := by
    simpa only [m,Q,R,div_eq_mul_inv,mul_one_div] using
      exact_contrast r J hr c s eta hc hs hscale heta1.le
  have hinv (i : Bool) :
      s^(2*r)/zhi ≤ 1/normalizer r c i s ∧
        1/normalizer r c i s ≤ s^(2*r)/zlo := by
    have hz := ((source_laws r hr c hc s hs).1.1 i).normalizer_positive
    constructor
    · rw [div_le_div_iff₀ hzhi hz]
      have hh := (le_div_iff₀ hp).1 (hsc.1 i).2.1
      nlinarith
    · rw [div_le_div_iff₀ hz hzlo]
      have hh := (div_le_iff₀ hp).1 (hsc.1 i).1
      nlinarith
  refine ⟨?_,?_,?_⟩
  · rw [hcontrast]
    calc
      _ = (c*(s^(2*r)/zhi))*(b/2*(J : ℝ)) := by dsimp [I]; ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left (hinv true).1 hc.le)
        hbrace0 (by positivity) (by positivity)
  · rw [hcontrast]
    calc
      _ ≤ (c*(s^(2*r)/zlo))*(B*(J : ℝ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hinv true).2 hc.le)
          hbrace1 (by linarith [hbrace0]) (by positivity)
      _ = _ := by dsimp [I]; ring
  · intro i
    have hm := reward_moment_formula r J hr c s eta hc hs hscale heta1.le i 1 one_ne_zero
    have hv := reward_moment_formula r J hr c s eta hc hs hscale heta1.le i 2 (by omega)
    simp only [pow_one] at hm
    change m i = _ at hm
    have hnum (p : ℕ) :
        occupationReward r (2*r-1) J s p +
          (if i then c*occupationReward r (r-1) J s p else 0) ≤
          (1+c)*occupationReward r (2*r-1) J s p := by
      have hmono := occupation_reward_mono r J s eta hs hscale heta1.le p
      have hnon := occupation_reward_nonneg r (2*r-1) J s p
      cases i <;> simp only [Bool.false_eq_true,↓reduceIte,add_zero]
      · nlinarith
      · nlinarith [mul_le_mul_of_nonneg_left hmono hc.le]
    have hmoment (p : ℕ) :
        (occupationReward r (2*r-1) J s p +
          (if i then c*occupationReward r (r-1) J s p else 0))/normalizer r c i s ≤
          ((1+c)*occupationReward r (2*r-1) J s p)*(s^(2*r)/zlo) := by
      have hnon : 0 ≤ occupationReward r (2*r-1) J s p +
          (if i then c*occupationReward r (r-1) J s p else 0) := by
        split_ifs <;> positivity
      calc
        _ ≤ ((1+c)*occupationReward r (2*r-1) J s p)/normalizer r c i s :=
          div_le_div_of_nonneg_right (hnum p) (by
            exact ((source_laws r hr c hc s hs).1.1 i).normalizer_positive.le)
        _ ≤ _ := by
          rw [div_eq_mul_inv, ← one_div]
          exact mul_le_mul_of_nonneg_left (hinv i).2 (by
            exact mul_nonneg (by positivity) (occupation_reward_nonneg _ _ _ _ _))
    refine ⟨average_nonneg _ _ (fun z => (reward_bounds r J hr z).1),?_,?_⟩
    · rw [hm]
      calc
        _ ≤ ((1+c)*R)*(s^(2*r)/zlo) := hmoment 1
        _ ≤ ((1+c)*(Cstar*(2 : ℝ)^(r*J)))*(s^(2*r)/zlo) := by
          gcongr
        _ = _ := by ring
    · rw [hv]
      calc
        _ ≤ ((1+c)*occupationReward r (2*r-1) J s 2)*(s^(2*r)/zlo) := hmoment 2
        _ ≤ ((1+c)*(upperConstant (2*r-1)*(J : ℝ)))*(s^(2*r)/zlo) := by
          gcongr
          exact hR.2
        _ = _ := by dsimp [I]; ring

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalOneGap
