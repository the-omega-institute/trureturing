/- GID: D5/S3/CharacterSums/MovingPrimeRowWidth
   generality: I
   mirror-B: D5/B/S3/CharacterSums/MovingPrimeRowWidth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The auxiliary prime row has a sharp width threshold when the exponent loss is fixed inside each power window and may decrease between windows. -/

import D5.S3.CharacterSums.SplitPrimeHostSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter
open D5.S3.CharacterSums.SplitPrimeHostSeries
namespace D5.S3.CharacterSums.MovingPrimeRowWidth

/-- The auxiliary primes, real size bands, prime splitting and conductor budget at x.
The congruence modulo eight spells out the splitting sign at the prime two. -/
structure PrimeRow (q d : ℕ) (ε x : ℝ) : Prop where
  primeQ : q.Prime
  modQ : q % 8 = 3
  primeD : d.Prime
  modD : d % 16 = 7
  splitQ : jacobiSym (-(d : ℤ)) q = 1
  splitTwo : (-(d : ℤ)) % 8 = 1
  splitOdd : ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℝ) ≤ x^(ε/5) → jacobiSym (-(d : ℤ)) p = 1
  lowerQ : x^(ε/5)/2 < Real.log q
  upperQ : Real.log q ≤ x^(ε/5)
  lowerD : x^(ε/5)*Real.log x^2/2 < Real.log d
  upperD : Real.log d ≤ x^(ε/5)*Real.log x^2
  conductor : ∀ n : ℕ, 1 ≤ n → (n:ℝ) ≤ 2*x^(2+8*ε) →
    Real.log (4*(n:ℝ)*q*d) ≤ 2*x^(ε/5)*Real.log x^2

/-- The width and first prime are fixed. The second prime and loss may depend on the
lower threshold and tolerance, but must work for every real cutoff in the window. -/
def HasPrimeRows (q : ℕ) (b : ℝ) : Prop :=
  ∀ R η : ℝ, 0 < η → ∃ (Y ε : ℝ) (d : ℕ), R ≤ Y ∧ Real.exp 5 ≤ Y ∧
    0 < ε ∧ ε < min η (1/52) ∧ ∀ x ∈ Icc Y (Y^b), PrimeRow q d ε x

private lemma conductor_bound {x ε : ℝ} {n q d : ℕ} (hε : 0 < ε) (hsmall : ε < 1/52)
    (hx : Real.exp 5 ≤ x) (hn1 : 1 ≤ n) (hq1 : 1 ≤ q) (hd1 : 1 ≤ d)
    (hn : (n:ℝ) ≤ 2*x^(2+8*ε)) (hq : Real.log q ≤ x^(ε/5))
    (hd : Real.log d ≤ x^(ε/5)*Real.log x^2) :
    Real.log (4*(n:ℝ)*q*d) ≤ 2*x^(ε/5)*Real.log x^2 := by
  have hx0 := (Real.exp_pos 5).trans_le hx
  have hL : 5 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hx1 : 1 ≤ x := (Real.one_le_exp (by norm_num : (0:ℝ) ≤ 5)).trans hx
  have hu : 1 ≤ x^(ε/5) := Real.one_le_rpow hx1 (by positivity)
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn1
  have hq0 : 0 < (q:ℝ) := by exact_mod_cast hq1
  have hd0 : 0 < (d:ℝ) := by exact_mod_cast hd1
  have hln := Real.log_le_log hn0 hn
  rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hx0 _).ne', Real.log_rpow hx0] at hln
  rw [Real.log_mul (by positivity) hd0.ne', Real.log_mul (by positivity) hq0.ne',
    Real.log_mul (by norm_num) hn0.ne']
  have h4 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num)
  have h2 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
  have h3 := mul_le_mul_of_nonneg_right (show 2+8*ε ≤ 3 by linarith) (by linarith : 0 ≤ Real.log x)
  have hpay : 4 + 3*Real.log x + x^(ε/5) ≤ x^(ε/5)*Real.log x^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu)
      (show 0 ≤ Real.log x^2 - 1 by nlinarith [sq_nonneg (Real.log x - 5)]),
      sq_nonneg (Real.log x - 5)]
  linarith

private lemma base_le_top {Y b : ℝ} (hY : 1 ≤ Y) (hb : 1 < b) : Y ≤ Y^b := by
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hY hb.le

private lemma width_necessary {q : ℕ} {b : ℝ} (hL : 1 < Real.log q) (hb : 1 < b)
    (hrows : HasPrimeRows q b) : b^2 * (Real.log q)^(b-1) < 2 := by
  obtain ⟨Y, ε, d, hY, _, _, _, hall⟩ := hrows 2 1 one_pos
  have hY1 : 1 < Y := by linarith
  have hY0 := zero_lt_one.trans hY1
  have hYY := base_le_top hY1.le hb
  have hlo := hall Y ⟨le_rfl,hYY⟩
  have hhi := hall (Y^b) ⟨hYY,le_rfl⟩
  let u := Y^(ε/5)
  have hu : 0 < u := Real.rpow_pos_of_pos hY0 _
  have hlog := Real.log_pos hY1
  have he : (Y^b)^(ε/5) = u^b := by
    dsimp [u]; rw [← Real.rpow_mul hY0.le, ← Real.rpow_mul hY0.le, mul_comm]
  have hedge := hhi.lowerD.trans_le hlo.upperD
  rw [he, Real.log_rpow hY0] at hedge
  change u^b * (b*Real.log Y)^2 / 2 < u * Real.log Y^2 at hedge
  have hrew : u^b = u^(b-1)*u := by
    rw [← Real.rpow_add_one hu.ne']; congr 1; ring
  rw [hrew] at hedge
  have hp : 0 < u*Real.log Y^2 := mul_pos hu (sq_pos_of_pos hlog)
  have hc : (b^2*u^(b-1)) * (u*Real.log Y^2) < 2*(u*Real.log Y^2) := by linarith only [hedge]
  have hbase := Real.rpow_le_rpow (zero_lt_one.trans hL).le hlo.upperQ (sub_pos.mpr hb).le
  exact (mul_le_mul_of_nonneg_left hbase (sq_nonneg b)).trans_lt ((mul_lt_mul_iff_left₀ hp).mp hc)

private lemma window_scales {L a b η s : ℝ} (hL : 1 < L) (ha : 0 < a) (hb : 1 < b)
    (hwidth : b^2*L^(b-1) < 2) (hs1 : 1 ≤ s) (hsb : s ≤ b)
    (hε : η = 5*Real.log L/a) :
    let x := Real.exp (s*a)
    L ≤ x^(η/5) ∧ x^(η/5) ≤ L^b ∧ x^(η/5)/2 < L ∧
    x^(η/5)*Real.log x^2/2 < L*a^2 ∧ L*a^2 ≤ x^(η/5)*Real.log x^2 := by
  dsimp only
  rw [← Real.exp_mul, Real.log_exp]
  have hscale : s*a*(η/5) = Real.log L*s := by rw [hε]; field_simp
  rw [hscale, ← Real.rpow_def_of_pos (zero_lt_one.trans hL)]
  have hlow : L ≤ L^s := by simpa using Real.rpow_le_rpow_of_exponent_le hL.le hs1
  have hu := Real.rpow_le_rpow_of_exponent_le hL.le hsb
  have hpow : L^b = L^(b-1)*L := by
    rw [← Real.rpow_add_one (zero_lt_one.trans hL).ne']; congr 1; ring
  have hbd : b^2*L^b < 2*L := by
    rw [hpow, ← mul_assoc]; exact mul_lt_mul_of_pos_right hwidth (zero_lt_one.trans hL)
  have hb2 : 1 ≤ b^2 := by nlinarith [sq_nonneg (b-1)]
  have hbu : L^b ≤ b^2*L^b := le_mul_of_one_le_left (Real.rpow_nonneg (zero_lt_one.trans hL).le _) hb2
  have hs2 : 1 ≤ s^2 := by nlinarith [sq_nonneg (s-1)]
  have hs2b : s^2 ≤ b^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hsb) (show 0 ≤ b+s by linarith)]
  have htop := mul_le_mul hs2b hu (Real.rpow_nonneg (zero_lt_one.trans hL).le s) (sq_nonneg b)
  have hlower : L ≤ s^2*L^s :=
    hlow.trans (le_mul_of_one_le_left (Real.rpow_nonneg (zero_lt_one.trans hL).le _) hs2)
  refine ⟨hlow,hu,by linarith,?_,?_⟩
  · nlinarith only [mul_lt_mul_of_pos_right (htop.trans_lt hbd) (sq_pos_of_pos ha)]
  · nlinarith only [mul_le_mul_of_nonneg_right hlower (sq_nonneg a)]

private lemma construct_rows {q : ℕ} (hq : q.Prime) (hq8 : q % 8 = 3)
    {b : ℝ} (hb : 1 < b) (hL : 1 < Real.log q)
    (hwidth : b^2*(Real.log q)^(b-1) < 2) : HasPrimeRows q b := by
  intro R η hη
  let L := Real.log (q:ℝ)
  let cap := min η (1/52)
  have hcap : 0 < cap := lt_min hη (by norm_num)
  have hL0 : 0 < L := zero_lt_one.trans hL
  have hc : 0 < Real.log L := Real.log_pos hL
  let K := max 5 (max R (5*Real.log L/cap+1))
  have hK5 : 5 ≤ K := le_max_left _ _
  have hKR : R ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hKc : 5*Real.log L/cap+1 ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨d,hdN,hsplit,hcomp⟩ :=
    ((split_prime_host_series ⌈L^b⌉₊).2.2 q hq hq8).2 ⌈Real.exp (L*K^2)⌉₊
  have hd0 : 0 < (d:ℝ) := by exact_mod_cast hsplit.1.pos
  have hdlog : L*K^2 < Real.log d := (Real.lt_log_iff_exp_lt hd0).2
    ((Nat.le_ceil _).trans_lt (by exact_mod_cast hdN))
  have hdiv : K^2 < Real.log d/L := (lt_div_iff₀ hL0).2 (by linarith only [hdlog])
  let a := Real.sqrt (Real.log d/L)
  have ha2 := Real.sq_sqrt (lt_of_le_of_lt (sq_nonneg K) hdiv).le
  change a^2 = _ at ha2
  have haK : K < a := by nlinarith [Real.sqrt_nonneg (Real.log d/L)]
  have ha : 0 < a := by linarith
  have he : 0 < 5*Real.log L/a := div_pos (by positivity) ha
  have hcut : 5*Real.log L/a < cap := (div_lt_iff₀ ha).2 (by
    have := (div_lt_iff₀ hcap).1 (show 5*Real.log L/cap < a by linarith)
    linarith only [this])
  have hd2 : L*a^2 = Real.log d := by
    have h := (eq_div_iff hL0.ne').1 ha2
    linarith only [h]
  have hRY : R ≤ Real.exp a := by linarith [Real.add_one_le_exp a]
  have hY5 : Real.exp 5 ≤ Real.exp a := Real.exp_le_exp.2 (by linarith)
  refine ⟨Real.exp a,5*Real.log L/a,d,hRY,hY5,he,hcut,?_⟩
  intro x hx
  have hx0 := (Real.exp_pos a).trans_le hx.1
  let s := Real.log x/a
  have hsa : s*a = Real.log x := div_mul_cancel₀ _ ha.ne'
  have hsa1 : 1 ≤ s := (le_div_iff₀ ha).2 (by
    simpa using (Real.le_log_iff_exp_le hx0).2 hx.1)
  have hsab : s ≤ b := (div_le_iff₀ ha).2 (by
    have := Real.log_le_log hx0 hx.2
    rwa [Real.log_rpow (Real.exp_pos a), Real.log_exp] at this)
  have hsx : Real.exp (s*a) = x := by rw [hsa,Real.exp_log hx0]
  obtain ⟨hlow, ht, hqband, hdl, hdu⟩ := window_scales hL ha hb hwidth hsa1 hsab
    (η := 5*Real.log L/a) rfl
  rw [hsx] at hlow ht hqband hdl hdu
  rw [hd2] at hdl hdu
  refine ⟨hq,hq8,hsplit.1,hsplit.2.1,hcomp.2.2,?_,?_,hqband,hlow,hdl,hdu,?_⟩
  · have := hsplit.2.1
    omega
  · intro p hp h2 hpx
    exact hsplit.2.2 p (Finset.mem_range.2 (by
      have hnat : p ≤ ⌈L^b⌉₊ := by exact_mod_cast (hpx.trans ht |>.trans (Nat.le_ceil _))
      omega)) hp h2
  · intro n hn1 hn
    exact conductor_bound he (hcut.trans_le (min_le_right _ _)) (hY5.trans hx.1)
      hn1 hq.one_le hsplit.1.one_le hn hlow hdu

/-- Exact strict power width for the full arithmetic row with a common prime pair
and one adjustable exponent loss on each arbitrarily late real window. -/
theorem prime_pair_power_window_iff {q : ℕ} (hq : q.Prime) (hq8 : q % 8 = 3)
    (hL : 1 < Real.log q) {b : ℝ} (hb : 1 < b) :
    HasPrimeRows q b ↔ b^2*(Real.log q)^(b-1) < 2 :=
  ⟨width_necessary hL hb, construct_rows hq hq8 hb hL⟩

end D5.S3.CharacterSums.MovingPrimeRowWidth
