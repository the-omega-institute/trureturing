/- GID: D5/S3/Arith/Robin/ActualLeastCrossingPriceRecord
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ActualLeastCrossingPriceRecord
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Uniform least crossings have positive-price records and occupied-layer confinement. -/

import D5.S3.Arith.Robin.ActualLeastCrossing5040
import D5.S3.Arith.Robin.ActualTwoPriceDefect

/-! The threshold precedes eta, including eta=1/2. All positive predecessors are
compared. Only occupied layers are confined; no crossing existence or signed Robin
upper bound is asserted. -/

noncomputable section
namespace D5.S3.Arith.Robin.ActualLeastCrossingPriceRecord

open D5.S3.Arith.Robin.OriginalFirstClockTransport
open D5.S3.Arith.Robin.ActualIntegerLogEnvelope
open D5.S3.Arith.Robin.ActualIntegerHeightJump
open D5.S3.Arith.Robin.ActualLeastCrossing5040
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
open D5.S3.Arith.GoldenLayerMarginalDecay

private theorem strict_scalar_remainder {l beta eta : ℝ} (hl : 2 ≤ l) (hb : 0 < beta)
    (heta : 0 < eta) (hetaHalf : eta ≤ 1 / 2) :
    (1 - (39 / 20 : ℝ) * eta) * beta / (l + beta) <
      Real.log (1 + beta / l) - ((39 / 20 : ℝ) / l) *
        (1 - Real.exp (-eta * beta)) := by
  let c : ℝ := 39 / 20
  let a := c * eta
  let G : ℝ → ℝ := fun u => Real.log (l + u) - Real.log l -
    (c / l) * (1 - Real.exp (-eta * u)) - (1 - a) * u / (l + u)
  have hl0 : 0 < l := by linarith
  have ha : 0 < a := mul_pos (by norm_num [c]) heta
  have ha1 : a < 1 := by dsimp [a, c]; linarith
  have hd (u : ℝ) (hu : 0 ≤ u) : HasDerivAt G
      (1 / (l + u) - (a / l) * Real.exp (-eta * u) -
        (1 - a) * l / (l + u) ^ 2) u := by
    have hlog := ((hasDerivAt_id u).const_add l).log (by linarith : l + u ≠ 0)
    have hexp := (Real.hasDerivAt_exp (-eta * u)).comp u
      ((hasDerivAt_id u).const_mul (-eta))
    have hrat := ((hasDerivAt_id u).const_mul (1 - a)).div
      ((hasDerivAt_id u).const_add l) (by linarith : l + u ≠ 0)
    convert ((hlog.sub_const (Real.log l)).sub
      (((hasDerivAt_const u 1).sub hexp).const_mul (c / l))).sub hrat using 1
    · funext x; rfl
    · dsimp [a]; ring
  have hmono : StrictMonoOn G (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · intro u hu
      exact (hd u hu).continuousAt.continuousWithinAt
    · intro u hu
      rw [interior_Ici, Set.mem_Ioi] at hu
      rw [(hd u hu.le).deriv]
      let t := u / l
      have ht : 0 < t := div_pos hu hl0
      have he : 1 + a * t < Real.exp (eta * u) := by
        have harg : a * t ≤ eta * u := by
          calc
            a * t = c * (eta * u) / l := by dsimp [a, t]; ring
            _ ≤ eta * u := (div_le_iff₀ hl0).mpr (by
              have h := mul_le_mul_of_nonneg_right
                (show c ≤ l by dsimp [c]; linarith) (mul_pos heta hu).le
              nlinarith)
        have he := Real.add_one_lt_exp (show eta * u ≠ 0 from (mul_pos heta hu).ne')
        linarith
      have hnum : 0 < Real.exp (eta * u) * (a + t) - a * (1 + t) ^ 2 := by
        have hm := mul_lt_mul_of_pos_right he (add_pos ha ht)
        have hid : (1 + a * t) * (a + t) - a * (1 + t) ^ 2 = t * (1 - a) ^ 2 := by ring
        have hp : 0 ≤ t * (1 - a) ^ 2 := mul_nonneg ht.le (sq_nonneg _)
        nlinarith
      have hid : 1 / (l + u) - (a / l) * Real.exp (-eta * u) -
          (1 - a) * l / (l + u) ^ 2 =
          (Real.exp (eta * u) * (a + t) - a * (1 + t) ^ 2) /
            (l * (1 + t) ^ 2 * Real.exp (eta * u)) := by
        rw [show -eta * u = -(eta * u) by ring, Real.exp_neg]
        dsimp [t]
        field_simp
        <;> ring
      rw [hid]
      exact div_pos hnum (by positivity)
  have hg := hmono (show (0 : ℝ) ∈ Set.Ici 0 by simp)
    (show beta ∈ Set.Ici 0 from hb.le) hb
  have hG0 : G 0 = 0 := by simp [G]
  rw [hG0] at hg
  have hid : Real.log (l + beta) - Real.log l = Real.log (1 + beta / l) := by
    rw [← Real.log_div (by linarith : l + beta ≠ 0) hl0.ne']
    congr 1
    field_simp
  dsimp [G] at hg
  rw [hid] at hg
  dsimp [a, c] at hg
  linarith

private theorem price_height_comparison {eta X Y E delta : ℝ}
    (heta : 0 < eta) (hetaHalf : eta ≤ 1 / 2)
    (hY : 1 < Y) (hYX : Y < X) (hl : 2 ≤ Real.log Y)
    (hE : E ≤ (39 / 20 : ℝ) / Real.log Y)
    (hdelta : delta ≤ ((1 - (39 / 20 : ℝ) * eta) / (X * Real.log X)) * (X - Y)) :
    X ^ eta * (delta + E - (Real.log (Real.log X) - Real.log (Real.log Y))) <
      Y ^ eta * E := by
  have hY0 : 0 < Y := by linarith
  have hX0 : 0 < X := hY0.trans hYX
  have hl0 : 0 < Real.log Y := by linarith
  have hL0 : 0 < Real.log X := hl0.trans (Real.log_lt_log hY0 hYX)
  let beta := Real.log X - Real.log Y
  let a := 1 - (39 / 20 : ℝ) * eta
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < beta := sub_pos.mpr (Real.log_lt_log hY0 hYX)
  let r := (Y / X) ^ eta
  have hr1 : r ≤ 1 := Real.rpow_le_one (div_pos hY0 hX0).le
    ((div_le_one hX0).mpr hYX.le) heta.le
  have hr : r = Real.exp (-eta * beta) := by
    dsimp [r]
    rw [Real.rpow_def_of_pos (div_pos hY0 hX0), Real.log_div hY0.ne' hX0.ne']
    congr 1
    dsimp [beta]
    ring
  have hratio : Real.exp (-beta) = Y / X := by
    rw [show -beta = Real.log Y - Real.log X by dsimp [beta]; ring,
      Real.exp_sub, Real.exp_log hY0, Real.exp_log hX0]
  have hcost : ((1 - (39 / 20 : ℝ) * eta) / (X * Real.log X)) * (X - Y) =
      a * (1 - Real.exp (-beta)) / Real.log X := by
    rw [hratio]
    dsimp [a]
    field_simp
    <;> ring
  have hdrop : 1 - Real.exp (-beta) < beta := by
    linarith [Real.one_sub_lt_exp_neg hb.ne']
  have hdel : delta < a * beta / Real.log X :=
    (hdelta.trans_eq hcost).trans_lt
      (div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hdrop ha) hL0)
  have hid : Real.log (Real.log X) - Real.log (Real.log Y) =
      Real.log (1 + beta / Real.log Y) := by
    rw [← Real.log_div hL0.ne' hl0.ne']
    congr 1
    dsimp [beta]
    field_simp
    ring
  have hscalar := strict_scalar_remainder hl hb heta hetaHalf
  have hL : Real.log Y + beta = Real.log X := by dsimp [beta]; ring
  rw [hL, ← hr, ← hid] at hscalar
  have hterm := mul_le_mul_of_nonneg_right hE (sub_nonneg.mpr hr1)
  have hnegative : delta + E * (1 - r) -
      (Real.log (Real.log X) - Real.log (Real.log Y)) < 0 := by
    dsimp [a] at hdel
    linarith
  have hpow : Y ^ eta = X ^ eta * r := by
    dsimp [r]
    rw [Real.div_rpow hY0.le hX0.le]
    field_simp
  rw [hpow]
  have hxpow : 0 < X ^ eta := Real.rpow_pos_of_pos hX0 _
  nlinarith [mul_neg_of_pos_of_neg hxpow hnegative]

/-- One threshold before eta gives strict records at two positive prices, every
literal occupied-layer cutoff, and divisibility into the existing strict integer.
The 5040 consequence holds at the half endpoint as well. -/
theorem uniform_actual_least_crossing_price_record :
    ∃ T0 : ℝ, 0 < T0 ∧ ∀ eta : ℝ, 0 < eta → eta ≤ 1 / 2 →
      ∀ T : ℝ, T0 ≤ T → ∀ m : ℕ, 3 ≤ m → T ≤ actualHeight eta m →
        (∀ n : ℕ, 3 ≤ n → n < m → actualHeight eta n < T) →
        let X := Real.log (m : ℝ)
        let L := Real.log X
        let lam := (1 - (39 / 20 : ℝ) * eta) / (X * L)
        let lam0 := 1 / (40 * X * L)
        0 < lam ∧ 0 < lam0 ∧
        (∀ n : ℕ, 0 < n → n < m →
          goldenResourceObjective lam n < goldenResourceObjective lam m) ∧
        (∀ n : ℕ, 0 < n → n < m →
          goldenResourceObjective lam0 n < goldenResourceObjective lam0 m) ∧
        (∀ p j : ℕ, p.Prime → 1 ≤ j → j ≤ m.factorization p →
          (p : ℝ) ^ j * Real.log p < 40 * X * L) ∧
        m ∣ ActualTwoPriceDefect.strictInteger lam0 ∧ 5040 ∣ m := by
  obtain ⟨A, hA, hupper⟩ := eventual_actual_integer_envelope_epsilon (1 / 20) (by norm_num)
  let R := max A (max (Real.exp 2) (Real.log 30))
  obtain ⟨T0, hT0, hescape⟩ := uniform_actual_height_escape (R + 1)
  refine ⟨T0, hT0, ?_⟩
  intro eta heta hetaHalf T hT m hm hcross hleast
  dsimp only
  let X := Real.log (m : ℝ)
  let L := Real.log X
  let a := 1 - (39 / 20 : ℝ) * eta
  let lam := a / (X * L)
  let lam0 := 1 / (40 * X * L)
  have hm0 : 0 < m := by omega
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm0
  obtain ⟨hWm, hXexp⟩ := hescape eta heta hetaHalf T hT m hm hcross
  have hX0 : 0 < X := (Real.exp_pos 2).trans_le hXexp
  have hL2 : 2 ≤ L := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 2) hXexp
  have hL0 : 0 < L := by linarith
  have haLower : (1 / 40 : ℝ) ≤ a := by dsimp [a]; linarith
  have ha0 : 0 < a := by linarith
  have ha1 : a ≤ 1 := by dsimp [a]; linarith
  have hlam : 0 < lam := div_pos ha0 (mul_pos hX0 hL0)
  have hlam0 : 0 < lam0 := one_div_pos.mpr (by positivity)
  have hlamLower : lam0 ≤ lam := by
    have hid : lam0 = (1 / 40 : ℝ) / (X * L) := by dsimp [lam0]; ring
    rw [hid]
    exact div_le_div_of_nonneg_right haLower (mul_pos hX0 hL0).le
  have hcost : lam * X ≤ 1 := by
    have hid : lam * X = a / L := by dsimp [lam]; field_simp
    rw [hid]
    exact (div_le_iff₀ hL0).mpr (by linarith)
  have hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lam n < goldenResourceObjective lam m := by
    intro n hn hnm
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hlogn : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    have hYX : Real.log (n : ℝ) < X :=
      Real.log_lt_log hnR (by exact_mod_cast hnm)
    by_contra h
    have hrival := le_of_not_gt h
    rw [golden_resource_sigma_identity lam (by omega : 1 ≤ m),
      golden_resource_sigma_identity lam (by omega : 1 ≤ n)] at hrival
    change divisorLog m - lam * X ≤ divisorLog n - lam * Real.log (n : ℝ) at hrival
    have hWn : R < divisorLog n := by
      have hnonneg := mul_nonneg hlam.le hlogn
      linarith
    have hlogrange : R < Real.log (n : ℝ) := hWn.trans_le (divisor_log_le_log hn)
    have hRA : A < Real.log (n : ℝ) := (le_max_left A _).trans_lt hlogrange
    have hYexp : Real.exp 2 < Real.log (n : ℝ) :=
      ((le_max_left (Real.exp 2) (Real.log 30)).trans (le_max_right A _)).trans_lt hlogrange
    have hY : 1 < Real.log (n : ℝ) :=
      (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2)).trans hYexp
    have hl : 2 ≤ Real.log (Real.log (n : ℝ)) := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 2) hYexp.le
    have hn3 : 3 ≤ n := by
      by_contra hsmall
      have hn2 : (n : ℝ) ≤ 2 := by exact_mod_cast (by omega : n ≤ 2)
      linarith [Real.log_le_sub_one_of_pos hnR]
    have hE := hupper n hn hRA.le
    norm_num only [show (19 / 10 : ℝ) + 1 / 20 = 39 / 20 by norm_num] at hE
    have hdelta : divisorLog m - divisorLog n ≤ lam * (X - Real.log (n : ℝ)) := by
      linarith
    have hcomp := price_height_comparison heta hetaHalf hY hYX hl hE hdelta
    have hid : originalObjective m - Real.eulerMascheroniConstant =
        (divisorLog m - divisorLog n) + (originalObjective n - Real.eulerMascheroniConstant) -
          (Real.log (Real.log X) - Real.log (Real.log (Real.log (n : ℝ)))) := by
      dsimp [X]
      unfold originalObjective divisorLog
      ring
    have hheight : actualHeight eta m < actualHeight eta n := by
      unfold actualHeight
      rw [hid]
      exact hcomp
    linarith [hleast n hn3 hnm]
  have hrecord0 : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lam0 n < goldenResourceObjective lam0 m := by
    intro n hn hnm
    have hrec := hrecord n hn hnm
    have hYX : Real.log (n : ℝ) < X :=
      Real.log_lt_log (by exact_mod_cast hn) (by exact_mod_cast hnm)
    rw [golden_resource_sigma_identity lam (by omega : 1 ≤ n),
      golden_resource_sigma_identity lam (by omega : 1 ≤ m)] at hrec
    rw [golden_resource_sigma_identity lam0 (by omega : 1 ≤ n),
      golden_resource_sigma_identity lam0 (by omega : 1 ≤ m)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hlamLower) (sub_pos.mpr hYX).le]
  have hlast (p : ℕ) (hp : p.Prime) (ha : 1 ≤ m.factorization p) :
      lam0 < goldenLayerMarginal p (m.factorization p) := by
    have hd : p ∣ m := (hp.dvd_iff_one_le_factorization hm0.ne').mpr ha
    have hn : 0 < m / p := Nat.div_pos (Nat.le_of_dvd hm0 hd) hp.pos
    have hproper : m / p < m := Nat.div_lt_self hm0 hp.one_lt
    have heq : m / p * p = m := Nat.div_mul_cancel hd
    have hfac : (m / p).factorization p + 1 = m.factorization p := by
      have h := congrArg (fun n : ℕ => n.factorization p) heq
      simpa [Nat.factorization_mul hn.ne' hp.ne_zero, hp.factorization] using h
    have hdelta := golden_resource_objective_single_layer_delta lam0 (by omega : 1 ≤ m / p) hp
    rw [heq, hfac] at hdelta
    have hrec := sub_pos.mpr (hrecord0 (m / p) hn hproper)
    rw [hdelta] at hrec
    exact sub_pos.mp ((mul_pos_iff_of_pos_right
      (Real.log_pos (by exact_mod_cast hp.one_lt))).mp hrec)
  have hdvd : m ∣ ActualTwoPriceDefect.strictInteger lam0 := by
    apply (Nat.factorization_le_iff_dvd hm0.ne'
      (by have := ActualTwoPriceDefect.strictInteger_pos hlam0; omega)).mp
    intro p
    by_cases hp : p.Prime
    · by_cases hz : m.factorization p = 0
      · rw [hz]; exact Nat.zero_le _
      · have ha : 1 ≤ m.factorization p := by omega
        exact (ActualTwoPriceDefect.strict_layer_iff hlam0 hp ha).mpr (hlast p hp ha)
    · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
      exact Nat.zero_le _
  have hcut : ∀ p j : ℕ, p.Prime → 1 ≤ j → j ≤ m.factorization p →
      (p : ℝ) ^ j * Real.log p < 40 * X * L := by
    intro p j hp hj hja
    have ha : 1 ≤ m.factorization p := hj.trans hja
    have hcount := (ActualTwoPriceDefect.strict_layer_iff hlam0 hp ha).mpr (hlast p hp ha)
    have hprofit := (ActualTwoPriceDefect.strict_layer_iff hlam0 hp hj).mp (hja.trans hcount)
    have hbound := hprofit.trans_le (golden_layer_marginal_le_inv_pow hp hj)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hplog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
    have hden : 0 < (p : ℝ) ^ j * Real.log p := mul_pos (pow_pos hp0 _) hplog
    have hinv : (p : ℝ)⁻¹ ^ j / Real.log p = 1 / ((p : ℝ) ^ j * Real.log p) := by
      rw [inv_pow, inv_eq_one_div, div_div]
    rw [hinv] at hbound
    exact (one_div_lt_one_div (by positivity : 0 < 40 * X * L) hden).mp hbound
  have hAm : 0 < (ArithmeticFunction.sigma 1 m : ℝ) / m :=
    div_pos (by exact_mod_cast ArithmeticFunction.sigma_pos 1 m hm0.ne') hmR
  have h30 : 30 < (ArithmeticFunction.sigma 1 m : ℝ) / m := by
    apply (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 30) hAm).mp
    have hR30 : Real.log 30 ≤ R :=
      (le_max_right (Real.exp 2) (Real.log 30)).trans (le_max_right A _)
    change Real.log 30 < divisorLog m
    linarith
  have hAbundancy : ∀ n : ℕ, 0 < n → n < m →
      (ArithmeticFunction.sigma 1 n : ℝ) / n < (ArithmeticFunction.sigma 1 m : ℝ) / m := by
    intro n hn hnm
    have hrec := hrecord0 n hn hnm
    rw [golden_resource_sigma_identity lam0 (by omega : 1 ≤ n),
      golden_resource_sigma_identity lam0 (by omega : 1 ≤ m)] at hrec
    have hYX : Real.log (n : ℝ) < X :=
      Real.log_lt_log (by exact_mod_cast hn) (by exact_mod_cast hnm)
    apply (Real.log_lt_log_iff
      (div_pos (by exact_mod_cast ArithmeticFunction.sigma_pos 1 n hn.ne')
        (by exact_mod_cast hn)) hAm).mp
    nlinarith [mul_pos hlam0 (sub_pos.mpr hYX)]
  exact ⟨hlam, hlam0, hrecord, hrecord0, hcut, hdvd,
    D5.S3.Arith.ExponentExchange.AbundancyRecord5040.strict_abundancy_record_divisible_5040
      hm0 h30 hAbundancy⟩

#print axioms uniform_actual_least_crossing_price_record

end D5.S3.Arith.Robin.ActualLeastCrossingPriceRecord
