/- GID: D5/S3/Arith/Robin/PriceRecord/FixedSupportIntegerActivationEnvelope
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/FixedSupportIntegerActivationEnvelope
   mirror-E: none(waiver:general-finite-analysis)
   anchors: []
   utility: none
   digest: Two-layer constructive activation bound in the complete integer-image envelope. -/

import D5.S3.Arith.Robin.PriceRecord.OwnClockFixedSupport
import D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure
import D5.S3.Arith.Robin.EulerLayer.EulerLayerRootSecondOrder
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.Real.Sqrt

/-! The integer image retains every supported-admissible natural vector. Only the
constructed trial vector is set to zero off support. No cardinal-three,
prime-prefix, record, minimizing-vector or asymptotic premise occurs here.
The scalar and conditional-infimum steps are paid bindings. The new
content is the uniform ceiling/three/two/one construction, consumed in the
upper half of finite_integer_activation_envelope. The lower half keeps the
literal two activation sums and the public finite cubic correction tail. -/

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.FixedSupportIntegerActivationEnvelope

open Real Set Finset
open OwnClockFixedSupport (primeSupport theta phi baseline)
open BoundaryPrimePrice (benefit probability probability_mem benefit_log)

/-- There is deliberately no condition on a p for p outside S. -/
def supportedAdmissible (S : Finset ℕ) (a : ℕ → ℕ) : Prop :=
  ∀ p ∈ S, 1 ≤ a p

/-- The complete original phi-minus-baseline image, not a trial-family image. -/
def integerValues (S : Finset ℕ) : Set ℝ :=
  {v | ∃ a : ℕ → ℕ, supportedAdmissible S a ∧
    phi S (fun p => (a p : ℝ)) - baseline S = v}

def integerInfimum (S : Finset ℕ) : ℝ := sInf (integerValues S)

def clockIncrement (S : Finset ℕ) (a : ℕ → ℕ) : ℝ :=
  ∑ p ∈ S, ((a p : ℝ) - 1) * log (p : ℝ)

/-- Natural powers are used only as the exact normalization of the real rpow. -/
def eulerTerm (p k : ℕ) : ℝ := -log (1 - 1 / (p : ℝ) ^ (k + 1))

def tailCost (S : Finset ℕ) (a : ℕ → ℕ) : ℝ :=
  ∑ p ∈ S, eulerTerm p (a p)

def linearCost (S : Finset ℕ) (lam : ℝ) (a : ℕ → ℕ) : ℝ :=
  ∑ p ∈ S, (lam * ((a p : ℝ) - 1) * log (p : ℝ) + eulerTerm p (a p))

def activationSum (S : Finset ℕ) (lam : ℝ) : ℝ :=
  ∑ p ∈ S, min (lam * log (p : ℝ)) (1 / (p : ℝ) ^ 2)

def secondActivationSum (S : Finset ℕ) (lam : ℝ) : ℝ :=
  ∑ p ∈ S, min (lam * log (p : ℝ)) (1 / (p : ℝ) ^ 3)

/-- Equality at p=q uses the ceiling. Both activation equalities are active. -/
def trialVector (S : Finset ℕ) (lam q : ℝ) (p : ℕ) : ℕ :=
  if p ∈ S then
    if (p : ℝ) ≤ q then Nat.ceil (log (1 / lam) / log (p : ℝ))
    else if lam * log (p : ℝ) ≤ 1 / (p : ℝ) ^ 3 then 3
    else if lam * log (p : ℝ) ≤ 1 / (p : ℝ) ^ 2 then 2 else 1
  else 0

-- Paid probability/log normalization, consumed by loss_data and the envelope.
private lemma euler_term_data {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    0 < 1 / (p : ℝ) ^ (k + 1) ∧
    1 / (p : ℝ) ^ (k + 1) < 1 ∧ 0 ≤ eulerTerm p k := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hprob := probability_mem hp1 hkR
  have heq : probability (p : ℝ) (k : ℝ) = 1 / (p : ℝ) ^ (k + 1) := by
    dsimp only [probability]
    rw [show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by simp,
      rpow_neg (by positivity : (0 : ℝ) ≤ p), rpow_natCast]
    simp only [one_div]
  rw [heq] at hprob
  refine ⟨hprob.1, hprob.2, ?_⟩
  exact neg_nonneg.mpr (log_nonpos (by linarith [hprob.2])
    (by linarith [hprob.1]))

-- Exact original-objective algebra, not OwnClockFixedSupport.realInfimum.
private lemma loss_data {S : Finset ℕ} (hS : primeSupport S)
    (hH : exp 1 < theta S) {a : ℕ → ℕ} (ha : supportedAdmissible S a) :
    0 ≤ clockIncrement S a ∧ 0 ≤ tailCost S a ∧
    phi S (fun p => (a p : ℝ)) - baseline S =
      log (1 + log (1 + clockIncrement S a / theta S) / log (theta S)) +
        tailCost S a := by
  have hH0 : 0 < theta S := (exp_pos 1).trans hH
  have hL1 : 1 < log (theta S) := by
    simpa only [log_exp] using log_lt_log (exp_pos 1) hH
  have hL0 : 0 < log (theta S) := by linarith
  have hU0 : 0 ≤ clockIncrement S a := by
    apply sum_nonneg
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (hS p hp).one_lt
    have haR : (1 : ℝ) ≤ a p := by exact_mod_cast ha p hp
    exact mul_nonneg (sub_nonneg.mpr haR) (log_pos hp1).le
  have hD0 : 0 ≤ tailCost S a := by
    exact sum_nonneg (fun p hp => (euler_term_data (hS p hp) (ha p hp)).2.2)
  have hclock : OwnClockFixedSupport.clock S (fun p => (a p : ℝ)) =
      theta S + clockIncrement S a := by
    dsimp only [OwnClockFixedSupport.clock, theta, clockIncrement]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    ring
  have hbenefit : (∑ p ∈ S, benefit (p : ℝ) (a p : ℝ)) =
      -tailCost S a - ∑ p ∈ S, log (1 - (p : ℝ) ^ (-1 : ℝ)) := by
    have hterm (p : ℕ) (hp : p ∈ S) :
        benefit (p : ℝ) (a p : ℝ) =
          -eulerTerm p (a p) - log (1 - (p : ℝ) ^ (-1 : ℝ)) := by
      have hp1 : (1 : ℝ) < p := by exact_mod_cast (hS p hp).one_lt
      have haR : (1 : ℝ) ≤ a p := by exact_mod_cast ha p hp
      rw [benefit_log hp1 haR]
      dsimp only [probability, eulerTerm]
      rw [show (a p : ℝ) + 1 = ((a p + 1 : ℕ) : ℝ) by simp,
        rpow_neg (by positivity : (0 : ℝ) ≤ p), rpow_natCast]
      simp only [one_div, neg_neg]
    calc
      _ = ∑ p ∈ S, (-eulerTerm p (a p) - log (1 - (p : ℝ) ^ (-1 : ℝ))) :=
        sum_congr rfl hterm
      _ = _ := by rw [sum_sub_distrib, sum_neg_distrib]; rfl
  have hratio : theta S + clockIncrement S a =
      theta S * (1 + clockIncrement S a / theta S) := by
    field_simp [hH0.ne']
    <;> ring
  have hinner : log (theta S + clockIncrement S a) =
      log (theta S) + log (1 + clockIncrement S a / theta S) := by
    rw [hratio, log_mul hH0.ne' (by positivity)]
  have hs0 : 0 ≤ log (1 + clockIncrement S a / theta S) :=
    log_nonneg (le_add_of_nonneg_right (div_nonneg hU0 hH0.le))
  have houter : log (log (theta S + clockIncrement S a)) - log (log (theta S)) =
      log (1 + log (1 + clockIncrement S a / theta S) / log (theta S)) := by
    rw [hinner]
    have hratioL : log (theta S) + log (1 + clockIncrement S a / theta S) =
        log (theta S) *
          (1 + log (1 + clockIncrement S a / theta S) / log (theta S)) := by
      field_simp [hL0.ne']
      <;> ring
    rw [hratioL, log_mul hL0.ne' (by positivity)]
    ring
  refine ⟨hU0, hD0, ?_⟩
  dsimp only [phi, baseline, OwnClockFixedSupport.terminalCost]
  rw [hclock, hbenefit]
  linarith only [houter]

-- Paid scalar bindings, shared by nonnegativity, the upper transfer and lower
-- confinement. The nested estimate composes
-- the public rational log bound; no private frozen proof is copied.
private lemma loglog_price_bounds {u L : ℝ} (hu : 0 ≤ u) (hL : 1 ≤ L) :
    0 ≤ log (1 + log (1 + u) / L) ∧
    log (1 + log (1 + u) / L) ≤ u / L ∧
    u / L - log (1 + log (1 + u) / L) ≤ u ^ 2 / L := by
  have hL0 : 0 < L := by linarith
  let s := log (1 + u)
  let v := s / L
  let t := log (1 + v)
  have hs0 : 0 ≤ s := log_nonneg (by linarith)
  have hsu : s ≤ u := by
    have hh := log_le_sub_one_of_pos (by linarith : 0 < 1 + u)
    dsimp only [s]
    linarith only [hh]
  have hv0 : 0 ≤ v := div_nonneg hs0 hL0.le
  have ht0 : 0 ≤ t := log_nonneg (by linarith)
  have htv : t ≤ v := by
    have hh := log_le_sub_one_of_pos (by linarith : 0 < 1 + v)
    dsimp only [t]
    linarith only [hh]
  have hvu : v ≤ u / L := div_le_div_of_nonneg_right hsu hL0.le
  have hdivu : u / L ≤ u := by
    apply (div_le_iff₀ hL0).mpr
    nlinarith [mul_nonneg hu (sub_nonneg.mpr hL)]
  -- Compose the existing rational log bounds directly. No private quadratic
  -- helper is copied or promoted from the queued curvature unit.
  let w := (2 * u / (u + 2)) / L
  have hw0 : 0 ≤ w := by dsimp only [w]; positivity
  have hwv : w ≤ v :=
    div_le_div_of_nonneg_right (le_log_one_add_of_nonneg hu) hL0.le
  have htw : 2 * w / (w + 2) ≤ t := by
    apply (le_log_one_add_of_nonneg hw0).trans
    exact log_le_log (by positivity) (by linarith only [hwv])
  let D := L * (u + 2) + u
  have hD0 : 0 < D := by dsimp only [D]; positivity
  have hnorm : 2 * w / (w + 2) = 2 * u / D := by
    dsimp only [w, D]
    field_simp
    <;> ring
  rw [hnorm] at htw
  have hrat : u / L - u ^ 2 / L ≤ 2 * u / D := by
    apply (le_div_iff₀ hD0).mpr
    apply (mul_le_mul_iff_left₀ hL0).mp
    field_simp
    dsimp only [D]
    nlinarith only [mul_nonneg (sq_nonneg u)
      (show 0 ≤ L - 1 + (L + 1) * u by positivity)]
  refine ⟨ht0, htv.trans hvu, ?_⟩
  change u / L - t ≤ u ^ 2 / L
  linarith only [hrat, htw]

/-- Uniform second-layer finite construction, independent of the own clock.
The literal witness uses a ceiling on the head and three/two/one on the tail.
It is consumed below for the complete nonlinear integer image. -/
theorem constructive_trial_vector {S : Finset ℕ} (hS : primeSupport S)
    {lam q : ℝ} (hlam : 0 < lam) (hq : 2 ≤ q) (hquartic : lam * q ^ 4 ≤ 1) :
    ∃ a : ℕ → ℕ, supportedAdmissible S a ∧
      linearCost S lam a ≤ activationSum S lam + secondActivationSum S lam +
        lam * q * (log (1 / lam) + 1) + 4 / q ^ 3 := by
  classical
  let T := log (1 / lam)
  let a := trialVector S lam q
  let K := lam * (T + 1)
  let B := S.filter (fun p : ℕ => (p : ℝ) ≤ q)
  let R := S.filter (fun p : ℕ => ¬ (p : ℝ) ≤ q)
  have hq0 : 0 < q := by linarith
  have hq4 : (16 : ℝ) ≤ q ^ 4 := by
    calc
      (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ q ^ 4 := by gcongr
  have hlam16 : lam ≤ 1 / 16 := by
    nlinarith [mul_le_mul_of_nonneg_left hq4 hlam.le]
  have hT0 : 0 < T := by
    apply log_pos
    exact (lt_div_iff₀ hlam).mpr (by linarith only [hlam16])
  have hTq : 4 * log q ≤ T := by
    have hh : q ^ 4 ≤ 1 / lam :=
      (le_div_iff₀ hlam).mpr (by nlinarith only [hquartic])
    have hhlog := log_le_log (pow_pos hq0 4) hh
    simpa only [log_pow, Nat.cast_ofNat] using hhlog
  have hsmall (p : ℕ) (hp : p ∈ S) (hpq : (p : ℝ) ≤ q) :
      4 ≤ a p ∧
      lam * ((a p : ℝ) - 1) * log (p : ℝ) + eulerTerm p (a p) ≤
        min (lam * log (p : ℝ)) (1 / (p : ℝ) ^ 2) +
          min (lam * log (p : ℝ)) (1 / (p : ℝ) ^ 3) + K := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).two_le
    have hp1 : (1 : ℝ) < p := by linarith
    have hp0 : (0 : ℝ) < p := by linarith
    have hlp : 0 < log (p : ℝ) := log_pos hp1
    have heqa : a p = Nat.ceil (T / log (p : ℝ)) := by
      simp only [a, trialVector, ite_eq_left hp, ite_eq_left hpq, T]
    have hratio : 4 ≤ T / log (p : ℝ) := by
      apply (le_div_iff₀ hlp).mpr
      have hlog := log_le_log hp0 hpq
      linarith only [hTq, hlog]
    have hc4R : (4 : ℝ) ≤ a p := by
      rw [heqa]
      exact hratio.trans (Nat.le_ceil _)
    have hc4 : 4 ≤ a p := by exact_mod_cast hc4R
    have hceilLow : T ≤ (a p : ℝ) * log (p : ℝ) := by
      have hh := Nat.le_ceil (T / log (p : ℝ))
      rw [← heqa] at hh
      exact (div_le_iff₀ hlp).mp hh
    have hceilHigh : ((a p : ℝ) - 1) * log (p : ℝ) ≤ T := by
      have hh := Nat.ceil_lt_add_one (div_nonneg hT0.le hlp.le)
      rw [← heqa] at hh
      have hmul := mul_lt_mul_of_pos_right hh hlp
      rw [show (T / log (p : ℝ) + 1) * log (p : ℝ) = T + log (p : ℝ) by
        field_simp [hlp.ne']<;> ring] at hmul
      linarith only [hmul]
    have hpow : 1 / lam ≤ (p : ℝ) ^ (a p) := by
      apply (log_le_log_iff (by positivity) (pow_pos hp0 _)).mp
      rw [log_pow]
      exact hceilLow
    have hxlam : 1 / (p : ℝ) ^ (a p + 1) ≤ lam / (p : ℝ) := by
      have hh := (div_le_iff₀ hlam).mp hpow
      apply (div_le_div_iff₀ (pow_pos hp0 _) hp0).mpr
      rw [pow_succ]
      nlinarith [mul_le_mul_of_nonneg_right hh hp0.le]
    have hlamhalf : 2 * (lam / (p : ℝ)) ≤ lam := by
      calc
        2 * (lam / (p : ℝ)) = (2 * lam) / (p : ℝ) := by ring
        _ ≤ lam := (div_le_iff₀ hp0).mpr (by
          nlinarith only [mul_le_mul_of_nonneg_left hp2 hlam.le])
    have hxhalf : 1 / (p : ℝ) ^ (a p + 1) ≤ 1 / 2 := by
      have hdiv : lam / (p : ℝ) ≤ lam := by
        apply (div_le_iff₀ hp0).mpr
        nlinarith only [mul_le_mul_of_nonneg_left hp2 hlam.le, hlam]
      exact hxlam.trans (hdiv.trans (by linarith only [hlam16]))
    have hx0 : 0 ≤ 1 / (p : ℝ) ^ (a p + 1) := by positivity
    have hlog := D5.S3.Arith.Lattices.Klartag.neg_log_one_sub_le hx0 hxhalf
    have hsq : (1 / (p : ℝ) ^ (a p + 1)) ^ 2 ≤ 1 / (p : ℝ) ^ (a p + 1) := by
      nlinarith [mul_nonneg hx0 (show 0 ≤ 1 - 1 / (p : ℝ) ^ (a p + 1) by
        linarith only [hxhalf])]
    have hd : eulerTerm p (a p) ≤ lam := by
      dsimp only [eulerTerm]
      linarith only [hlog, hsq, hxlam, hlamhalf]
    have hcl := mul_le_mul_of_nonneg_left hceilHigh hlam.le
    have hmin2 : 0 ≤ min (lam * log (p : ℝ)) (1 / (p : ℝ) ^ 2) :=
      le_min (mul_nonneg hlam.le hlp.le) (by positivity)
    have hmin3 : 0 ≤ min (lam * log (p : ℝ)) (1 / (p : ℝ) ^ 3) :=
      le_min (mul_nonneg hlam.le hlp.le) (by positivity)
    refine ⟨hc4, ?_⟩
    dsimp only [K]
    nlinarith only [hcl, hd, hmin2, hmin3]
  have ha : supportedAdmissible S a := by
    intro p hp
    by_cases hpq : (p : ℝ) ≤ q
    · have hh := (hsmall p hp hpq).1
      omega
    · simp only [a, trialVector, ite_eq_left hp, ite_eq_right hpq]
      split_ifs <;> norm_num
  have hpoint (p : ℕ) (hp : p ∈ S) :
      lam * ((a p : ℝ) - 1) * log (p : ℝ) + eulerTerm p (a p) ≤
        min (lam * log (p : ℝ)) (1 / (p : ℝ) ^ 2) +
          min (lam * log (p : ℝ)) (1 / (p : ℝ) ^ 3) +
            (if (p : ℝ) ≤ q then K else 2 / (p : ℝ) ^ 4) := by
    by_cases hpq : (p : ℝ) ≤ q
    · simpa only [ite_eq_left hpq] using (hsmall p hp hpq).2
    · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).two_le
      have hp0 : (0 : ℝ) < p := by linarith
      let t : ℝ := 1 / (p : ℝ)
      let b : ℝ := lam * log (p : ℝ)
      have ht0 : 0 ≤ t := by positivity
      have htHalf : t ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2
      have ht1 : t ≤ 1 := by linarith
      have hinv (n : ℕ) : 1 / (p : ℝ) ^ n = t ^ n := by
        simp only [t, one_div_pow]
      have h23 : t ^ 3 ≤ t ^ 2 := pow_le_pow_of_le_one ht0 ht1 (by norm_num)
      have h43 : t ^ 4 ≤ t ^ 3 := pow_le_pow_of_le_one ht0 ht1 (by norm_num)
      have h64 : t ^ 6 ≤ t ^ 4 := pow_le_pow_of_le_one ht0 ht1 (by norm_num)
      have h84 : t ^ 8 ≤ t ^ 4 := pow_le_pow_of_le_one ht0 ht1 (by norm_num)
      have hhalf (n : ℕ) (hn : 1 ≤ n) : t ^ n ≤ 1 / 2 := by
        exact (pow_le_pow_of_le_one ht0 ht1 hn).trans (by simpa using htHalf)
      have hJ (k : ℕ) :
          lam * ((k : ℝ) - 1) * log (p : ℝ) + eulerTerm p k =
            ((k : ℝ) - 1) * b - log (1 - t ^ (k + 1)) := by
        dsimp only [eulerTerm, b]
        rw [hinv]
        ring
      rw [ite_eq_right hpq, hinv 2, hinv 3]
      rw [show 2 / (p : ℝ) ^ 4 = 2 * t ^ 4 by rw [← hinv 4]<;> ring]
      change _ ≤ min b (t ^ 2) + min b (t ^ 3) + 2 * t ^ 4
      by_cases h3 : b ≤ t ^ 3
      · have h2 : b ≤ t ^ 2 := h3.trans h23
        have heqa : a p = 3 := by
          simp only [a, trialVector, ite_eq_left hp, ite_eq_right hpq]
          rw [hinv 3]
          exact ite_eq_left h3
        have hlog := D5.S3.Arith.Lattices.Klartag.neg_log_one_sub_le
          (pow_nonneg ht0 4) (hhalf 4 (by norm_num))
        rw [heqa, hJ, min_eq_left h2, min_eq_left h3]
        norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
        rw [show (t ^ 4) ^ 2 = t ^ 8 by ring] at hlog
        linarith only [hlog, h84]
      · by_cases h2 : b ≤ t ^ 2
        · have heqa : a p = 2 := by
            simp only [a, trialVector, ite_eq_left hp, ite_eq_right hpq]
            rw [hinv 3, hinv 2]
            exact (ite_eq_right h3).trans (ite_eq_left h2)
          have hlog := D5.S3.Arith.Lattices.Klartag.neg_log_one_sub_le
            (pow_nonneg ht0 3) (hhalf 3 (by norm_num))
          rw [heqa, hJ, min_eq_left h2, min_eq_right (le_of_not_ge h3)]
          norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
          rw [show (t ^ 3) ^ 2 = t ^ 6 by ring] at hlog
          have hexcess : -log (1 - t ^ 3) - t ^ 3 ≤ t ^ 6 := by
            linarith only [hlog]
          have hpaid : -log (1 - t ^ 3) ≤ t ^ 3 + t ^ 4 := by
            linarith only [hexcess, h64]
          linarith only [hpaid, pow_nonneg ht0 4]
        · have heqa : a p = 1 := by
            simp only [a, trialVector, ite_eq_left hp, ite_eq_right hpq]
            rw [hinv 3, hinv 2]
            exact (ite_eq_right h3).trans (ite_eq_right h2)
          have hlog := D5.S3.Arith.Lattices.Klartag.neg_log_one_sub_le
            (pow_nonneg ht0 2) (hhalf 2 (by norm_num))
          rw [heqa, hJ, min_eq_right (le_of_not_ge h2),
            min_eq_right (le_of_not_ge h3)]
          norm_num only [Nat.cast_one, Nat.reduceAdd, sub_self, zero_mul, zero_sub]
          rw [show (t ^ 2) ^ 2 = t ^ 4 by ring] at hlog
          have hexcess : -log (1 - t ^ 2) - (t ^ 2 + t ^ 3) ≤ t ^ 4 - t ^ 3 := by
            linarith only [hlog]
          have hzero : -log (1 - t ^ 2) ≤ t ^ 2 + t ^ 3 := by
            linarith only [hexcess, h43]
          linarith only [hzero, pow_nonneg ht0 4]
  have hcard : (B.card : ℝ) ≤ q := by
    have hsub : B ⊆ Finset.Icc 1 ⌊q⌋₊ := by
      intro p hp
      rcases mem_filter.mp hp with ⟨hpS, hpq⟩
      exact mem_Icc.mpr ⟨(hS p hpS).one_lt.le, Nat.le_floor hpq⟩
    have hcN : B.card ≤ ⌊q⌋₊ := by simpa using Finset.card_le_card hsub
    have hcR : (B.card : ℝ) ≤ (⌊q⌋₊ : ℝ) := by exact_mod_cast hcN
    exact hcR.trans (Nat.floor_le hq0.le)
  have htail := D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure.finite_cubic_tail
    hq0 R (by
      intro p hp
      exact lt_of_not_ge (mem_filter.mp hp).2)
  have hquarticTail : (∑ p ∈ R, 1 / (p : ℝ) ^ 4) ≤ 2 / q ^ 3 := by
    calc
      _ ≤ (1 / q) * ∑ p ∈ R, 1 / (p : ℝ) ^ 3 := by
        rw [mul_sum]
        apply sum_le_sum
        intro p hp
        have hqp : q < (p : ℝ) := lt_of_not_ge (mem_filter.mp hp).2
        have hp0 : (0 : ℝ) < p := hq0.trans hqp
        have hh := mul_le_mul_of_nonneg_right
          (one_div_le_one_div_of_le hq0 hqp.le)
          (show 0 ≤ 1 / (p : ℝ) ^ 3 by positivity)
        convert hh using 1 <;> field_simp [hp0.ne', hq0.ne'] <;> ring
      _ ≤ (1 / q) * (2 / q ^ 2) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ = 2 / q ^ 3 := by ring
  have hsplit :
      (∑ p ∈ S, (if (p : ℝ) ≤ q then K else 2 / (p : ℝ) ^ 4)) =
        (B.card : ℝ) * K + 2 * (∑ p ∈ R, 1 / (p : ℝ) ^ 4) := by
    rw [sum_ite]
    simp only [sum_const, nsmul_eq_mul]
    change (B.card : ℝ) * K + (∑ p ∈ R, 2 / (p : ℝ) ^ 4) = _
    rw [show (∑ p ∈ R, 2 / (p : ℝ) ^ 4) =
      2 * (∑ p ∈ R, 1 / (p : ℝ) ^ 4) by
        rw [mul_sum]; apply sum_congr rfl; intros<;> ring]
  have hhead : (B.card : ℝ) * K ≤ lam * q * (T + 1) := by
    have hh := mul_le_mul_of_nonneg_right hcard
      (show 0 ≤ K by
        dsimp only [K]
        exact mul_nonneg hlam.le (by linarith only [hT0]))
    dsimp only [K] at hh ⊢
    nlinarith only [hh]
  refine ⟨a, ha, ?_⟩
  have hsum : linearCost S lam a ≤ activationSum S lam + secondActivationSum S lam +
      ∑ p ∈ S, (if (p : ℝ) ≤ q then K else 2 / (p : ℝ) ^ 4) := by
    simpa only [linearCost, activationSum, secondActivationSum, sum_add_distrib] using
      sum_le_sum hpoint
  rw [hsplit] at hsum
  change linearCost S lam a ≤ activationSum S lam + secondActivationSum S lam +
    lam * q * (T + 1) + 4 / q ^ 3
  have htailPaid : 2 * (∑ p ∈ R, 1 / (p : ℝ) ^ 4) ≤ 4 / q ^ 3 := by
    calc
      _ ≤ 2 * (2 / q ^ 3) := mul_le_mul_of_nonneg_left hquarticTail (by norm_num)
      _ = _ := by ring
  calc
    _ ≤ activationSum S lam + secondActivationSum S lam +
        ((B.card : ℝ) * K + 2 * (∑ p ∈ R, 1 / (p : ℝ) ^ 4)) := hsum
    _ ≤ activationSum S lam + secondActivationSum S lam +
        (lam * q * (T + 1) + 4 / q ^ 3) :=
      add_le_add le_rfl (add_le_add hhead htailPaid)
    _ = _ := by ring

/-- The original full integer-image, finite free-q/r second-layer envelope.
No condition is imposed on an arbitrary vector outside S. No minimizer,
prime-prefix, cardinal-three, record, PNT or RH premise occurs. -/
theorem finite_integer_activation_envelope {S : Finset ℕ} (hS : primeSupport S)
    (hH : exp 1 < theta S) {r q : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hrscale : 2 * log (theta S) * r ≤ 1) (hq : 2 ≤ q)
    (hquartic : (1 / (theta S * log (theta S))) * q ^ 4 ≤ 1) :
    let H := theta S
    let L := log H
    let lam := 1 / (H * L)
    let A := activationSum S lam + secondActivationSum S lam
    min r (A - 2 * lam * log (1 / lam) - 16 * L * r ^ 2) ≤ integerInfimum S ∧
      integerInfimum S ≤ A + lam * q * (log (1 / lam) + 1) + 4 / q ^ 3 := by
  classical
  let H := theta S
  let L := log H
  let lam := 1 / (H * L)
  let A := activationSum S lam + secondActivationSum S lam
  change min r (A - 2 * lam * log (1 / lam) - 16 * L * r ^ 2) ≤ integerInfimum S ∧
    integerInfimum S ≤ A + lam * q * (log (1 / lam) + 1) + 4 / q ^ 3
  change 2 * L * r ≤ 1 at hrscale
  change lam * q ^ 4 ≤ 1 at hquartic
  have hH0 : 0 < H := (exp_pos 1).trans hH
  have hL1 : 1 < L := by
    simpa only [L, H, log_exp] using log_lt_log (exp_pos 1) hH
  have hL0 : 0 < L := by linarith
  have hlam : 0 < lam := one_div_pos.mpr (mul_pos hH0 hL0)
  have hlinear (a : ℕ → ℕ) :
      linearCost S lam a = lam * clockIncrement S a + tailCost S a := by
    simp only [linearCost, clockIncrement, tailCost, mul_sum, sum_add_distrib, mul_assoc]
  have hnormalize (a : ℕ → ℕ) :
      lam * clockIncrement S a = (clockIncrement S a / H) / L := by
    dsimp only [lam]
    field_simp [hH0.ne', hL0.ne']
    <;> ring
  -- Paid local price cases and the public cubic correction tail. Kept on the
  -- all-vector path; no independently retained min/cutoff wrapper is added.
  have hfloor (a : ℕ → ℕ) (ha : supportedAdmissible S a) :
      A - 2 * lam * log (1 / lam) ≤ linearCost S lam a := by
    let E := S.filter (fun p : ℕ =>
      1 / (p : ℝ) ^ 2 - 1 / (p : ℝ) ^ 3 < lam * log (p : ℝ))
    have hlocal (p : ℕ) (hp : p ∈ S) :
        min (lam * log (p : ℝ)) (1 / (p : ℝ) ^ 2) +
          min (lam * log (p : ℝ)) (1 / (p : ℝ) ^ 3) ≤
        (lam * ((a p : ℝ) - 1) * log (p : ℝ) + eulerTerm p (a p)) +
          (if 1 / (p : ℝ) ^ 2 - 1 / (p : ℝ) ^ 3 < lam * log (p : ℝ)
            then 1 / (p : ℝ) ^ 3 else 0) := by
      let b := lam * log (p : ℝ)
      let x : ℝ := 1 / (p : ℝ) ^ 2
      let y : ℝ := 1 / (p : ℝ) ^ 3
      let j := lam * ((a p : ℝ) - 1) * log (p : ℝ) + eulerTerm p (a p)
      change min b x + min b y ≤ j + (if x - y < b then y else 0)
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).two_le
      have hp1 : (1 : ℝ) < p := by linarith
      have hp0 : (0 : ℝ) < p := by linarith
      have hb0 : 0 ≤ b := mul_nonneg hlam.le (log_pos hp1).le
      have hy0 : 0 ≤ y := by positivity
      have hxy : y ≤ x - y := by
        have heq : x = (p : ℝ) * y := by
          dsimp only [x, y]
          field_simp [hp0.ne']
          <;> ring
        have hh := mul_le_mul_of_nonneg_right hp2 hy0
        rw [← heq] at hh
        linarith only [hh]
      have hmin : min x (min (b + y) (2 * b)) = min b (x - y) + min b y := by
        by_cases hby : b ≤ y
        · have hbx : b ≤ x - y := hby.trans hxy
          rw [min_eq_right (show 2 * b ≤ b + y by linarith),
            min_eq_right (show 2 * b ≤ x by linarith),
            min_eq_left hbx, min_eq_left hby]
          ring
        · have hyb : y ≤ b := (lt_of_not_ge hby).le
          by_cases hbx : b ≤ x - y
          · rw [min_eq_left (show b + y ≤ 2 * b by linarith),
              min_eq_right (show b + y ≤ x by linarith),
              min_eq_left hbx, min_eq_right hyb]
          · have hxb : x - y ≤ b := (lt_of_not_ge hbx).le
            rw [min_eq_left (le_min (by linarith : x ≤ b + y)
                (by linarith : x ≤ 2 * b)), min_eq_right hxb, min_eq_right hyb]
            ring
      have hd := euler_term_data (hS p hp) (ha p hp)
      have htail : 1 / (p : ℝ) ^ (a p + 1) ≤ eulerTerm p (a p) := by
        have hlog := log_le_sub_one_of_pos
          (show 0 < 1 - 1 / (p : ℝ) ^ (a p + 1) by linarith only [hd.2.1])
        dsimp only [eulerTerm]
        linarith only [hlog]
      have hf : min b (x - y) + min b y ≤ j := by
        rw [← hmin]
        by_cases ha1 : a p = 1
        · have hj : x ≤ j := by
            dsimp only [j, x]
            simpa only [ha1, Nat.cast_one, Nat.reduceAdd, sub_self,
              mul_zero, zero_mul, zero_add] using htail
          exact (min_le_left _ _).trans hj
        · by_cases ha2 : a p = 2
          · have hj : b + y ≤ j := by
              dsimp only [j, b, y]
              simpa only [ha2, Nat.cast_ofNat, Nat.reduceAdd,
                show (2 : ℝ) - 1 = 1 by norm_num, mul_one] using
                add_le_add (le_refl (lam * log (p : ℝ))) htail
            exact ((min_le_right _ _).trans (min_le_left _ _)).trans hj
          · have ha3 : 3 ≤ a p := by have := ha p hp; omega
            have haR : (3 : ℝ) ≤ a p := by exact_mod_cast ha3
            have hh := mul_le_mul_of_nonneg_right
              (show 2 ≤ (a p : ℝ) - 1 by linarith only [haR]) hb0
            have hj : 2 * b ≤ j := by
              dsimp only [j, b] at *
              nlinarith only [hh, hd.2.2]
            exact ((min_le_right _ _).trans (min_le_right _ _)).trans hj
      have hgap : min b x + min b y ≤
          (min b (x - y) + min b y) + (if x - y < b then y else 0) := by
        by_cases hc : x - y < b
        · rw [ite_eq_left hc, min_eq_right hc.le]
          linarith only [min_le_right b x]
        · have hbx : b ≤ x - y := le_of_not_gt hc
          simp only [ite_eq_right hc, min_eq_left hbx,
            min_eq_left (show b ≤ x by linarith only [hbx, hy0]), add_zero]
          exact le_rfl
      exact hgap.trans (add_le_add hf (le_refl _))
    let X := 1 / lam
    let Q := sqrt (X / log X)
    have hX0 : 0 < X := one_div_pos.mpr hlam
    have hXlam : X * lam = 1 := by dsimp only [X]; field_simp
    have hq4 : (16 : ℝ) ≤ q ^ 4 := by
      calc
        (16 : ℝ) = 2 ^ 4 := by norm_num
        _ ≤ q ^ 4 := by gcongr
    have hqX : q ^ 4 ≤ X :=
      (le_div_iff₀ hlam).mpr (by nlinarith only [hquartic])
    have hX16 : 16 ≤ X := hq4.trans hqX
    have hlogX1 : 1 ≤ log X := by
      have hrat := le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 15 by norm_num)
      have hh := log_le_log (by norm_num : (0 : ℝ) < 16) hX16
      norm_num at hrat
      linarith only [hrat, hh]
    have hlogX0 : 0 < log X := by linarith
    have hratio : 1 < X / log X := by
      apply (lt_div_iff₀ hlogX0).mpr
      have hh := log_le_sub_one_of_pos hX0
      linarith only [hh]
    have hQ1 : 1 < Q := by
      apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).mpr
      simpa only [one_pow] using hratio
    have hQ0 : 0 < Q := by linarith
    have hQsq : Q ^ 2 = X / log X := sq_sqrt (div_nonneg hX0.le hlogX0.le)
    have hQlog : log Q ≤ log X / 2 := by
      dsimp only [Q]
      rw [log_sqrt (div_nonneg hX0.le hlogX0.le), log_div hX0.ne' hlogX0.ne']
      have hh := log_nonneg hlogX1
      linarith only [hh]
    have hQcut : Q ^ 2 * log Q ≤ X / 2 := by
      calc
        _ ≤ Q ^ 2 * (log X / 2) :=
          mul_le_mul_of_nonneg_left hQlog (sq_nonneg Q)
        _ = X / 2 := by rw [hQsq]; field_simp [hlogX0.ne']<;> ring
    have hEcut (p : ℕ) (hp : p ∈ E) : Q < (p : ℝ) := by
      rcases mem_filter.mp hp with ⟨hpS, hc⟩
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hpS).two_le
      have hp1 : (1 : ℝ) < p := by linarith
      have hp0 : (0 : ℝ) < p := by linarith
      have hscaled := mul_lt_mul_of_pos_right hc (sq_pos_of_pos hp0)
      have heq : (1 / (p : ℝ) ^ 2 - 1 / (p : ℝ) ^ 3) * (p : ℝ) ^ 2 =
          1 - 1 / (p : ℝ) := by field_simp [hp0.ne']<;> ring
      rw [heq] at hscaled
      have hinv : 1 / (p : ℝ) ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2
      have hh : (1 / 2 : ℝ) < lam * log (p : ℝ) * (p : ℝ) ^ 2 := by
        linarith only [hscaled, hinv]
      have hmult := mul_lt_mul_of_pos_right hh hX0
      have hcancel : (lam * log (p : ℝ) * (p : ℝ) ^ 2) * X =
          (p : ℝ) ^ 2 * log (p : ℝ) := by
        calc
          _ = (X * lam) * ((p : ℝ) ^ 2 * log (p : ℝ)) := by ring
          _ = _ := by rw [hXlam, one_mul]
      rw [hcancel] at hmult
      have hpCut : X / 2 < (p : ℝ) ^ 2 * log (p : ℝ) := by
        linarith only [hmult]
      by_contra hnot
      have hcmp := D5.S3.Arith.Robin.EulerLayerRootSecondOrder.second_cutoff_strictMono.monotoneOn
        (show (p : ℝ) ∈ Set.Ioi 1 from hp1) (show Q ∈ Set.Ioi 1 from hQ1)
        (le_of_not_gt hnot)
      exact (not_le_of_gt hpCut) (hcmp.trans hQcut)
    have hRtail := D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure.finite_cubic_tail
      hQ0 E hEcut
    have hRnorm : 2 / Q ^ 2 = 2 * lam * log (1 / lam) := by
      rw [hQsq]
      dsimp only [X]
      field_simp [hlam.ne', hlogX0.ne']
      <;> ring
    rw [hRnorm] at hRtail
    have hsum : A ≤ linearCost S lam a + ∑ p ∈ E, 1 / (p : ℝ) ^ 3 := by
      simpa only [A, activationSum, secondActivationSum, linearCost,
        E, sum_filter, sum_add_distrib] using sum_le_sum hlocal
    linarith only [hsum, hRtail]
  have hnonneg (a : ℕ → ℕ) (ha : supportedAdmissible S a) :
      0 ≤ phi S (fun p => (a p : ℝ)) - baseline S := by
    obtain ⟨hU, hD, hF⟩ := loss_data hS hH ha
    rw [hF]
    have hu : 0 ≤ clockIncrement S a / H := div_nonneg hU hH0.le
    exact add_nonneg (loglog_price_bounds hu hL1.le).1 hD
  have hpoint (a : ℕ → ℕ) (ha : supportedAdmissible S a) :
      min r (A - 2 * lam * log (1 / lam) - 16 * L * r ^ 2) ≤
        phi S (fun p => (a p : ℝ)) - baseline S := by
    by_cases hrF : r ≤ phi S (fun p => (a p : ℝ)) - baseline S
    · exact (min_le_left _ _).trans hrF
    · have hFr : phi S (fun p => (a p : ℝ)) - baseline S < r := lt_of_not_ge hrF
      obtain ⟨hU, hD, hF⟩ := loss_data hS hH ha
      let u := clockIncrement S a / H
      let s := log (1 + u)
      let t := log (1 + s / L)
      have hu : 0 ≤ u := div_nonneg hU hH0.le
      have hs0 : 0 ≤ s := log_nonneg (by linarith)
      change phi S (fun p => (a p : ℝ)) - baseline S = t + tailCost S a at hF
      have ht : t < r := by linarith only [hF, hFr, hD]
      have hinner : 1 + s / L < exp r :=
        (log_lt_iff_lt_exp (by positivity : 0 < 1 + s / L)).mp ht
      have hsExp : s < L * (exp r - 1) := by
        have hh : s / L < exp r - 1 := by linarith only [hinner]
        have hh' := (div_lt_iff₀ hL0).mp hh
        nlinarith only [hh']
      have her : exp r - 1 ≤ 2 * r := by
        have hh := abs_exp_sub_one_le (show |r| ≤ 1 by
          rw [abs_of_nonneg hr.le]; exact hr1)
        rw [abs_of_nonneg hr.le] at hh
        exact (le_abs_self _).trans hh
      have hs2 : s ≤ 2 * L * r := by
        have hh := mul_le_mul_of_nonneg_left her hL0.le
        nlinarith only [hsExp, hh]
      have hs1 : s ≤ 1 := hs2.trans hrscale
      have hu2 : u ≤ 2 * s := by
        have hh := abs_exp_sub_one_le (show |s| ≤ 1 by
          rw [abs_of_nonneg hs0]; exact hs1)
        rw [abs_of_nonneg hs0] at hh
        have heq : exp s - 1 = u := by
          dsimp only [s]
          rw [exp_log (by linarith : 0 < 1 + u)]
          ring
        rw [heq, abs_of_nonneg hu] at hh
        exact hh
      have hu4 : u ≤ 4 * L * r := by linarith only [hu2, hs2]
      have huSq : u ^ 2 ≤ (4 * L * r) ^ 2 := by
        have hh := mul_nonneg (sub_nonneg.mpr hu4)
          (show 0 ≤ 4 * L * r + u by positivity)
        nlinarith only [hh]
      have herr : u ^ 2 / L ≤ 16 * L * r ^ 2 := by
        apply (div_le_iff₀ hL0).mpr
        nlinarith only [huSq]
      have hscalar := (loglog_price_bounds hu hL1.le).2.2
      change u / L - t ≤ u ^ 2 / L at hscalar
      have hJ : linearCost S lam a = u / L + tailCost S a := by
        rw [hlinear, hnormalize]
      have hA := hfloor a ha
      have hlower : A - 2 * lam * log (1 / lam) - 16 * L * r ^ 2 ≤
          phi S (fun p => (a p : ℝ)) - baseline S := by
        linarith only [hF, hJ, hA, hscalar, herr]
      exact (min_le_right _ _).trans hlower
  have hne : (integerValues S).Nonempty := by
    refine ⟨phi S (fun _ => (1 : ℝ)) - baseline S, fun _ => 1, ?_, by simp only [Nat.cast_one]⟩
    intro p hp
    exact le_rfl
  have hb : BddBelow (integerValues S) := by
    refine ⟨0, ?_⟩
    rintro v ⟨a, ha, rfl⟩
    exact hnonneg a ha
  constructor
  · apply le_csInf hne
    rintro v ⟨a, ha, rfl⟩
    exact hpoint a ha
  · obtain ⟨a, ha, htrial⟩ := constructive_trial_vector hS hlam hq hquartic
    have hmem : phi S (fun p => (a p : ℝ)) - baseline S ∈ integerValues S :=
      ⟨a, ha, rfl⟩
    have hupper : phi S (fun p => (a p : ℝ)) - baseline S ≤ linearCost S lam a := by
      obtain ⟨hU, hD, hF⟩ := loss_data hS hH ha
      have hu : 0 ≤ clockIncrement S a / H := div_nonneg hU hH0.le
      have hh := (loglog_price_bounds hu hL1.le).2.1
      rw [hF, hlinear, hnormalize]
      exact add_le_add hh (le_refl (tailCost S a))
    exact (csInf_le hb hmem).trans (hupper.trans htrial)

#print axioms constructive_trial_vector
#print axioms finite_integer_activation_envelope

end D5.S3.Arith.Robin.PriceRecord.FixedSupportIntegerActivationEnvelope
