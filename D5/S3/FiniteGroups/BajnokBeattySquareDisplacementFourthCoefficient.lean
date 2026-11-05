/- GID: D5/S3/FiniteGroups/BajnokBeattySquareDisplacementFourthCoefficient
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattySquareDisplacementFourthCoefficient
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Strict negative fourth displacement, exact cancellation, and full natural cubic scaling. -/

import D5.S3.FiniteGroups.BajnokBeattySquareDisplacementCorrection
import D5.S3.FiniteGroups.BajnokBeattySquareDisplacementProfile
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.FiniteGroups.BajnokBeattySquareDisplacementFourthCoefficient

open Filter Set
open D5.S0.Tower.DBonacci.PerronRoot

private noncomputable def Q (q : ℕ) : ℝ := q
private noncomputable def nu (q : ℕ) : ℝ := (Q q)^2
private noncomputable def beta (q : ℕ) : ℝ := dbonacciPerronRoot (q^2)
private noncomputable def sigma (q : ℕ) : ℝ := Real.log (beta q)
private noncomputable def w (q : ℕ) : ℝ := Real.exp (-nu q * sigma q)
private noncomputable def alpha (q : ℕ) : ℝ := (nu q - 1) / (4 * Q q * sigma q)
private noncomputable def g (q : ℕ) : ℝ := beta q - nu q * w q
private noncomputable def C (q : ℕ) : ℝ := 2 * (nu q + 1) / (3 * (nu q - 1)^2)
private noncomputable def E (q : ℕ) : ℝ := 4 / (3 * (nu q - 1)^2)
private noncomputable def B (q : ℕ) : ℝ :=
  16 * ((nu q)^2 + nu q + 1) / (15 * (nu q - 1)^4)
private noncomputable def H (q : ℕ) (s : ℝ) : ℝ :=
  C q * s^3 * (Real.exp s - (nu q)^2 * Real.exp (-nu q * s))
private noncomputable def K (q : ℕ) (s : ℝ) : ℝ :=
  -E q * s^3 * (Real.exp s - nu q * Real.exp (-nu q * s)) +
    B q * s^5 * (Real.exp s - (nu q)^3 * Real.exp (-nu q * s)) +
    ((C q)^2 / 2) * s^6 * (Real.exp s + (nu q)^4 * Real.exp (-nu q * s))
private noncomputable def d (q : ℕ) : ℝ :=
  (nu q + 1) * sigma q / (6 * Q q * (nu q - 1)) *
    ((((nu q)^2 + 1) * beta q - 2 * (nu q)^2) /
      ((nu q + 1) * beta q - 2 * nu q))
private noncomputable def u (q : ℕ) : ℝ := -sigma q * d q / alpha q
private noncomputable def G2 (q : ℕ) : ℝ := beta q + (nu q)^2 * w q
private noncomputable def Hp (q : ℕ) : ℝ :=
  C q * (3 * (sigma q)^2 * (beta q - (nu q)^2 * w q) +
    (sigma q)^3 * (beta q + (nu q)^3 * w q))
private noncomputable def e (q : ℕ) : ℝ :=
  (d q)^2 / alpha q + alpha q / (sigma q * g q) *
    (G2 q * (u q)^2 / 2 + Hp q * u q + K q (sigma q))
private noncomputable def r (q : ℕ) : ℝ := nu q * (nu q - 1) * w q / g q
private noncomputable def A (q : ℕ) : ℝ :=
  (2 * ((nu q)^2 - 4 * nu q + 1) -
    4 * (nu q + 1) * (3 * (nu q)^2 - 2 * nu q - 2) * r q -
    10 * (nu q + 1)^2 * (r q)^2) / (45 * (nu q - 1)^3)
private noncomputable def J (q : ℕ) : ℝ :=
  beta q * (nu q)^2 * w q * (nu q + 1)^2 / (9 * (nu q - 1) * (g q)^3)

private theorem base_data {q : ℕ} (hq : 3 ≤ q) :
    0 < Q q ∧ 9 ≤ nu q ∧ 0 < beta q ∧ beta q < 2 ∧
      (2 / 3 : ℝ) < sigma q ∧ sigma q < Real.log 2 ∧
      Real.exp (sigma q) = beta q ∧ beta q + w q = 2 := by
  have hqR : (3 : ℝ) ≤ Q q := by dsimp [Q]; exact_mod_cast hq
  have hn : 9 ≤ q^2 := by simpa only [pow_two] using Nat.mul_le_mul hq hq
  have hv : (9 : ℝ) ≤ nu q := by
    dsimp [nu, Q]
    exact_mod_cast hn
  have hb : 0 < beta q :=
    lt_trans zero_lt_one (one_lt_dbonacciPerronRoot (q^2) (by omega))
  have hb2 : beta q < 2 := dbonacciPerronRoot_lt_two (q^2) (by omega)
  have hs : (2 / 3 : ℝ) < sigma q := by
    change (2 / 3 : ℝ) < Real.log (dbonacciPerronRoot (q^2))
    exact D5.S3.FiniteGroups.BajnokBeattySquareDisplacementProfile.sigma_gt_two_thirds hq
  have hm : Real.exp (nu q * sigma q) = beta q ^ (q^2) := by
    change Real.exp ((q : ℝ)^2 * Real.log (beta q)) = beta q ^ (q^2)
    rw [← Nat.cast_pow]
    simpa only [Real.exp_log hb] using
      Real.exp_nat_mul (Real.log (beta q)) (q^2)
  have hw : w q = 2 - beta q := by
    unfold w
    rw [neg_mul, Real.exp_neg, hm, ← inv_pow]
    exact (two_sub_dbonacciPerronRoot_eq_inv_pow (q^2) (by omega)).symm
  refine ⟨by linarith only [hqR], hv, hb, hb2, hs, ?_, Real.exp_log hb, ?_⟩
  · exact Real.strictMonoOn_log hb (by norm_num) hb2
  · rw [hw]; ring

private theorem correction_data {q : ℕ} (hq : 3 ≤ q) :
    0 < alpha q ∧ 0 < g q ∧ 0 < d q ∧ u q = -H q (sigma q) / g q := by
  obtain ⟨hQ, hv, hb, hb2, hs, hs2, he, hw⟩ := base_data hq
  have hm : 0 < nu q - 1 := by linarith only [hv]
  have hspos : 0 < sigma q := by linarith only [hs]
  have ha : 0 < alpha q := by unfold alpha; positivity
  have hc := D5.S3.FiniteGroups.BajnokBeattySquareDisplacementCorrection.square_displacement_correction q hq
  have he' : Real.exp (Real.log (dbonacciPerronRoot (q^2))) =
      dbonacciPerronRoot (q^2) := Real.exp_log hb
  have hg : 0 < g q := by
    simpa only [g, w, nu, Q, sigma, beta, he'] using hc.1
  have hd : 0 < d q := by
    convert hc.2.1 using 1 <;>
      simp only [d, nu, Q, sigma, beta, ← pow_mul] <;> ring
  have hcancel : g q * (sigma q * d q / alpha q) = H q (sigma q) := by
    convert hc.2.2.2.2.2 using 1 <;>
      simp only [g, w, H, C, alpha, d, nu, Q, sigma, beta, he', div_div, ← pow_mul] <;> ring
  refine ⟨ha, hg, hd, ?_⟩
  unfold u
  apply (eq_div_iff hg.ne').2
  calc
    (-sigma q * d q / alpha q) * g q = -(g q * (sigma q * d q / alpha q)) := by ring
    _ = -H q (sigma q) := by rw [hcancel]

private theorem exact_cancellation {q : ℕ} (hq : 3 ≤ q) :
    G2 q * (u q)^2 / 2 + Hp q * u q + K q (sigma q) +
      g q * (sigma q * (d q)^2 / (alpha q)^2 - sigma q * e q / alpha q) = 0 := by
  have hb := base_data hq
  have hc := correction_data hq
  have hs : sigma q ≠ 0 := by linarith only [hb.2.2.2.2.1]
  unfold e
  field_simp [hs, hc.1.ne', hc.2.1.ne'] <;> ring

/-- Algebraic reduction before estimating any term, retaining the positive residual. -/
private theorem compact_formula {q : ℕ} (hq : 3 ≤ q) :
    Q q * e q = -sigma q / (3 * (nu q - 1)) +
      A q * (sigma q)^3 + J q * (sigma q)^4 := by
  obtain ⟨hQ, hv, hb, hb2, hs, hs2, he, hw⟩ := base_data hq
  obtain ⟨ha, hg, hd, hu⟩ := correction_data hq
  have hs0 : sigma q ≠ 0 := by linarith only [hs]
  have hv0 : nu q - 1 ≠ 0 := by linarith only [hv]
  have hreduce : Q q * e q = (nu q - 1) / (4 * (sigma q)^2 * g q) *
      (g q * (u q)^2 / sigma q + G2 q * (u q)^2 / 2 +
        Hp q * u q + K q (sigma q)) := by
    unfold e u alpha
    field_simp [hQ.ne', hv0, hs0, hg.ne'] <;> ring
  rw [hreduce, hu]
  have hbform : beta q = 2 - w q := by linarith only [hw]
  have hg0 : 2 - w q - nu q * w q ≠ 0 := by
    simpa only [g, hbform] using hg.ne'
  have hwdef : Real.exp (-nu q * sigma q) = w q := rfl
  simp only [H, K, G2, Hp, C, E, B, A, J, r, he, hwdef]
  simp only [g, hbform]
  field_simp [hv0, hs0, hg0] <;> ring

private theorem exp_six_gt_four_hundred : (400 : ℝ) < Real.exp 6 := by
  have h := Real.sum_le_exp_of_nonneg (x := (6 : ℝ)) (by norm_num) 14
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith only [h]

/-- The only derivative certificate for a weighted negative exponential. -/
theorem quartic_tail {v : ℝ} (hv : 9 ≤ v) :
    v^4 * Real.exp (-2 * v / 3) < (6561 / 400 : ℝ) := by
  let f : ℝ → ℝ := fun x => x^4 * Real.exp (-2 * x / 3)
  have hd (x : ℝ) : HasDerivAt f
      (x^3 * (4 - 2 * x / 3) * Real.exp (-2 * x / 3)) x := by
    have hl : HasDerivAt (fun t : ℝ => -2 * t / 3) (-2 / 3) x := by
      convert (hasDerivAt_id x).const_mul (-2 / 3 : ℝ) using 1 <;>
        (try funext t) <;> (try dsimp only [id]) <;> ring
    convert ((hasDerivAt_id x).pow 4).mul hl.exp using 1 <;>
      (try funext t) <;> dsimp [f] <;> ring
  have hdiff : Differentiable ℝ f := fun x => (hd x).differentiableAt
  have hanti : AntitoneOn f (Ici 9) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 9)
      hdiff.continuous.continuousOn hdiff.differentiableOn
    intro x hx
    have hx9 : (9 : ℝ) ≤ x := interior_subset hx
    have hx0 : 0 ≤ x := by linarith only [hx9]
    rw [(hd x).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith only [hx9]))
      (Real.exp_pos _).le
  have hle : f v ≤ f 9 := hanti (by norm_num) hv hv
  have h9 : f 9 < (6561 / 400 : ℝ) := by
    have hn : Real.exp (-6 : ℝ) < 1 / 400 := by
      rw [Real.exp_neg, inv_eq_one_div]
      apply (div_lt_iff₀ (Real.exp_pos 6)).2
      linarith only [exp_six_gt_four_hundred]
    calc
      f 9 = (6561 : ℝ) * Real.exp (-6) := by norm_num [f]
      _ < 6561 * (1 / 400 : ℝ) := mul_lt_mul_of_pos_left hn (by norm_num)
      _ = (6561 / 400 : ℝ) := by norm_num
  exact lt_of_le_of_lt hle h9

private theorem normalized_tails {q : ℕ} (hq : 3 ≤ q) :
    (nu q + 1) * w q < (1 / 40 : ℝ) ∧
      (nu q)^2 * (nu q + 1)^2 * w q < (81 / 4 : ℝ) := by
  obtain ⟨hQ, hv, hb, hb2, hs, hs2, he, hw⟩ := base_data hq
  have hvpos : 0 < nu q := by linarith only [hv]
  have hwpos : 0 < w q := Real.exp_pos _
  have hexp : w q < Real.exp (-2 * nu q / 3) := by
    apply Real.exp_lt_exp.mpr
    nlinarith only [mul_pos hvpos (sub_pos.mpr hs)]
  have h4 : (nu q)^4 * w q < (6561 / 400 : ℝ) :=
    (mul_lt_mul_of_pos_left hexp (pow_pos hvpos 4)).trans (quartic_tail hv)
  have hv3 : (729 : ℝ) ≤ (nu q)^3 := by
    have ht := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9) hv 3
    norm_num at ht
    exact ht
  have hlow : (729 : ℝ) * (nu q * w q) ≤ (nu q)^4 * w q := by
    nlinarith only [mul_le_mul_of_nonneg_right hv3 (mul_pos hvpos hwpos).le]
  have hlin : (nu q + 1) * w q ≤ (10 / 9 : ℝ) * (nu q * w q) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hv) hwpos.le]
  have hsq : (nu q + 1)^2 ≤ (100 / 81 : ℝ) * (nu q)^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hv)
      (show 0 ≤ 19 * nu q + 9 by linarith only [hv])]
  constructor
  · nlinarith only [h4, hlow, hlin]
  · have ht := mul_le_mul_of_nonneg_right hsq
      (mul_nonneg (sq_nonneg (nu q)) hwpos.le)
    nlinarith only [ht, h4]

private theorem log_two_lt_seven_tenths : Real.log (2 : ℝ) < 7 / 10 := by
  have ht := Real.sum_le_exp_of_nonneg (x := (7 / 10 : ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at ht
  apply Real.exp_lt_exp.mp
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  linarith only [ht]

private theorem compact_coefficient_bounds {q : ℕ} (hq : 3 ≤ q) :
    A q ≤ 2 / (45 * (nu q - 1)) ∧
      0 ≤ J q ∧ J q ≤ 288000 / (493039 * (nu q - 1)) := by
  obtain ⟨hQ, hv, hb, hb2, hs, hs2, he, hw⟩ := base_data hq
  have hm : 0 < nu q - 1 := by linarith only [hv]
  have hvpos : 0 < nu q := by linarith only [hv]
  have ht := normalized_tails hq
  have hwpos : 0 < w q := Real.exp_pos _
  have hg : (79 / 40 : ℝ) < g q := by unfold g; nlinarith only [hw, ht.1]
  have hgpos : 0 < g q := by linarith only [hg]
  have hr : 0 ≤ r q := by unfold r; positivity
  have ht1 : 0 ≤ 4 * (nu q + 1) * (3 * (nu q)^2 - 2 * nu q - 2) * r q := by
    have hn : 0 ≤ 3 * (nu q)^2 - 2 * nu q - 2 := by
      nlinarith only [hv, sq_nonneg (nu q - 9)]
    positivity
  have ht2 : 0 ≤ 10 * (nu q + 1)^2 * (r q)^2 := by positivity
  refine ⟨?_, by unfold J; positivity, ?_⟩
  · unfold A
    apply (div_le_iff₀ (show 0 < 45 * (nu q - 1)^3 by positivity)).2
    have heq : 2 / (45 * (nu q - 1)) * (45 * (nu q - 1)^3) =
        2 * (nu q - 1)^2 := by field_simp [hm.ne'] <;> ring
    rw [heq]
    nlinarith only [ht1, ht2, hv]
  · have htpos : 0 ≤ (nu q)^2 * (nu q + 1)^2 * w q := by
      have hwpos : 0 < w q := Real.exp_pos _
      positivity
    have hnum : beta q * ((nu q)^2 * (nu q + 1)^2 * w q) ≤ (81 / 2 : ℝ) := by
      calc
        _ ≤ 2 * ((nu q)^2 * (nu q + 1)^2 * w q) :=
          mul_le_mul_of_nonneg_right hb2.le htpos
        _ ≤ 2 * (81 / 4 : ℝ) := by linarith only [ht.2]
        _ = (81 / 2 : ℝ) := by norm_num
    have hg3 : (493039 / 64000 : ℝ) ≤ (g q)^3 := by
      have ht := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 79 / 40) hg.le 3
      norm_num at ht
      exact ht
    have hratio : beta q * ((nu q)^2 * (nu q + 1)^2 * w q) /
        (9 * (g q)^3) ≤ (288000 / 493039 : ℝ) := by
      apply (div_le_iff₀ (by positivity : 0 < 9 * (g q)^3)).2
      nlinarith only [hnum, hg3]
    calc
      J q = (beta q * ((nu q)^2 * (nu q + 1)^2 * w q) /
          (9 * (g q)^3)) / (nu q - 1) := by
            unfold J
            field_simp [hm.ne', hgpos.ne'] <;> ring
      _ ≤ (288000 / 493039 : ℝ) / (nu q - 1) :=
        div_le_div_of_nonneg_right hratio hm.le
      _ = 288000 / (493039 * (nu q - 1)) := by field_simp [hm.ne'] <;> ring

private theorem strict_negative {q : ℕ} (hq : 3 ≤ q) : e q < 0 := by
  obtain ⟨hQ, hv, hb, hb2, hs, hs2, he, hw⟩ := base_data hq
  have hm : 0 < nu q - 1 := by linarith only [hv]
  have hspos : 0 ≤ sigma q := by linarith only [hs]
  have hsmax : sigma q ≤ (7 / 10 : ℝ) := (hs2.trans log_two_lt_seven_tenths).le
  obtain ⟨hA, hJpos, hJ⟩ := compact_coefficient_bounds hq
  have h3 : (sigma q)^3 ≤ (7 / 10 : ℝ)^3 := pow_le_pow_left₀ hspos hsmax 3
  have h4 : (sigma q)^4 ≤ (7 / 10 : ℝ)^4 := pow_le_pow_left₀ hspos hsmax 4
  have hAt : A q * (sigma q)^3 ≤ 2 / (45 * (nu q - 1)) * (7 / 10 : ℝ)^3 := by
    calc
      _ ≤ 2 / (45 * (nu q - 1)) * (sigma q)^3 :=
        mul_le_mul_of_nonneg_right hA (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)
  have hJt : J q * (sigma q)^4 ≤
      288000 / (493039 * (nu q - 1)) * (7 / 10 : ℝ)^4 := by
    calc
      _ ≤ 288000 / (493039 * (nu q - 1)) * (sigma q)^4 :=
        mul_le_mul_of_nonneg_right hJ (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)
  have hfirst : -sigma q / (3 * (nu q - 1)) ≤ -(2 / 3 : ℝ) / (3 * (nu q - 1)) :=
    div_le_div_of_nonneg_right (by linarith only [hs]) (by positivity)
  have hbound : Q q * e q ≤ (-740234623 / 11093377500 : ℝ) / (nu q - 1) := by
    rw [compact_formula hq]
    calc
      _ ≤ -(2 / 3 : ℝ) / (3 * (nu q - 1)) +
          2 / (45 * (nu q - 1)) * (7 / 10 : ℝ)^3 +
          288000 / (493039 * (nu q - 1)) * (7 / 10 : ℝ)^4 :=
        add_le_add (add_le_add hfirst hAt) hJt
      _ = _ := by field_simp [hm.ne']; ring
  have hneg : Q q * e q < 0 :=
    hbound.trans_lt (div_neg_of_neg_of_pos (by norm_num) hm)
  by_contra hn
  have hnonneg := mul_nonneg hQ.le (le_of_not_gt hn)
  linarith only [hneg, hnonneg]

private theorem nu_tendsto : Tendsto nu atTop atTop :=
  (tendsto_pow_atTop (α := ℝ) (by decide : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop

private theorem beta_tendsto : Tendsto beta atTop (nhds 2) :=
  dbonacciPerronRoot_tendsto_two.comp (tendsto_pow_atTop (α := ℕ) (by decide : 2 ≠ 0))

private theorem sigma_tendsto : Tendsto sigma atTop (nhds (Real.log 2)) :=
  beta_tendsto.log (by norm_num)

/-- One quartic majorant controls all four moments (and the zeroth moment). -/
private theorem moment_tendsto (j : ℕ) (hj : j ≤ 4) :
    Tendsto (fun q : ℕ => (nu q)^j * w q) atTop (nhds 0) := by
  have hx : Tendsto (fun q : ℕ => (2 / 3 : ℝ) * nu q) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 2 / 3)).2 nu_tendsto
  have hraw := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).comp hx
  have hmajor : Tendsto (fun q : ℕ => (nu q)^4 * Real.exp (-2 * nu q / 3))
      atTop (nhds 0) := by
    have ht := hraw.const_mul ((3 / 2 : ℝ)^4)
    convert ht using 1
    · funext q
      simp only [Function.comp_apply]
      rw [show -((2 / 3 : ℝ) * nu q) = -2 * nu q / 3 by ring]
      ring
    · norm_num
  apply squeeze_zero' (g := fun q : ℕ => (nu q)^4 * Real.exp (-2 * nu q / 3))
  · filter_upwards [eventually_ge_atTop 3] with q hq
    have hv := (base_data hq).2.1
    have hv0 : 0 ≤ nu q := by linarith only [hv]
    have hw : 0 < w q := Real.exp_pos _
    exact mul_nonneg (pow_nonneg hv0 j) hw.le
  · filter_upwards [eventually_ge_atTop 3] with q hq
    have hb := base_data hq
    have hnu : 1 ≤ nu q := by linarith only [hb.2.1]
    have hp : (nu q)^j ≤ (nu q)^4 := pow_le_pow_right₀ hnu hj
    have hexp : w q ≤ Real.exp (-2 * nu q / 3) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_nonneg (by linarith only [hnu] : 0 ≤ nu q)
        (sub_nonneg.mpr hb.2.2.2.2.1.le)]
    exact mul_le_mul hp hexp (Real.exp_pos _).le (by positivity)
  · exact hmajor

private theorem normalized_limits :
    Tendsto (fun q : ℕ => (nu q)⁻¹) atTop (nhds 0) ∧
      Tendsto g atTop (nhds 2) ∧ Tendsto r atTop (nhds 0) ∧
      Tendsto (fun q : ℕ => nu q * r q) atTop (nhds 0) := by
  have hm1 : Tendsto (fun q : ℕ => nu q * w q) atTop (nhds 0) := by
    simpa using moment_tendsto 1 (by omega)
  have hm2 := moment_tendsto 2 (by omega)
  have hm3 := moment_tendsto 3 (by omega)
  have hg : Tendsto g atTop (nhds 2) := by
    change Tendsto (fun q : ℕ => beta q - nu q * w q) atTop (nhds 2)
    simpa only [sub_zero] using beta_tendsto.sub hm1
  refine ⟨tendsto_inv_atTop_zero.comp nu_tendsto, hg, ?_, ?_⟩
  · have ht := (hm2.sub hm1).div hg (by norm_num)
    simp only [sub_zero, zero_div] at ht
    apply ht.congr'
    exact Eventually.of_forall (fun q => by
      change ((nu q)^2 * w q - nu q * w q) / g q = r q
      unfold r
      ring)
  · have ht := (hm3.sub hm2).div hg (by norm_num)
    simp only [sub_zero, zero_div] at ht
    apply ht.congr'
    exact Eventually.of_forall (fun q => by
      change ((nu q)^3 * w q - (nu q)^2 * w q) / g q = nu q * r q
      unfold r
      ring)

private theorem rescaled_coefficients_tendsto :
    Tendsto (fun q : ℕ => nu q * A q) atTop (nhds (2 / 45 : ℝ)) ∧
      Tendsto (fun q : ℕ => nu q * J q) atTop (nhds 0) := by
  obtain ⟨hi, hg, hr, hnr⟩ := normalized_limits
  let t : ℕ → ℝ := fun q => (nu q)⁻¹
  have ht : Tendsto t atTop (nhds 0) := hi
  have hc (a : ℝ) : Tendsto (fun _ : ℕ => a) atTop (nhds a) := tendsto_const_nhds
  have hnormA : Tendsto (fun q : ℕ =>
      (2 * (1 - 4 * t q + (t q)^2) -
        4 * (1 + t q) * (3 - 2 * t q - 2 * (t q)^2) * (nu q * r q) -
        10 * (1 + t q)^2 * (r q)^2) / (45 * (1 - t q)^3))
      atTop (nhds (2 / 45 : ℝ)) := by
    have hP := (((hc 1).sub (ht.const_mul 4)).add (ht.pow 2)).const_mul 2
    have hR := ((((hc 1).add ht).const_mul 4).mul
      (((hc 3).sub (ht.const_mul 2)).sub ((ht.pow 2).const_mul 2))).mul hnr
    have hT := ((((hc 1).add ht).pow 2).const_mul 10).mul (hr.pow 2)
    have hD := (((hc 1).sub ht).pow 3).const_mul 45
    convert ((hP.sub hR).sub hT).div hD (by norm_num) using 1 <;> norm_num
  have hnormJ : Tendsto (fun q : ℕ => beta q * ((nu q)^4 * w q) * (1 + t q)^2 /
      (9 * (1 - t q) * (g q)^3)) atTop (nhds 0) := by
    convert ((beta_tendsto.mul (moment_tendsto 4 (by omega))).mul
      (((hc 1).add ht).pow 2)).div
      ((((hc 1).sub ht).const_mul 9).mul (hg.pow 3)) (by norm_num) using 1 <;>
      norm_num
  constructor
  · apply hnormA.congr'
    filter_upwards [eventually_ge_atTop 3] with q hq
    have hv := (base_data hq).2.1
    have hv0 : nu q ≠ 0 := by linarith only [hv]
    have hm0 : nu q - 1 ≠ 0 := by linarith only [hv]
    have ht0 : 1 - (nu q)⁻¹ ≠ 0 := by
      exact (sub_pos.mpr (inv_lt_one_of_one_lt₀
        (show 1 < nu q by linarith only [hv]))).ne'
    dsimp [A, t]
    field_simp [hv0, hm0, ht0] <;> ring
  · apply hnormJ.congr'
    filter_upwards [eventually_ge_atTop 3] with q hq
    have hv := (base_data hq).2.1
    have hv0 : nu q ≠ 0 := by linarith only [hv]
    have hm0 : nu q - 1 ≠ 0 := by linarith only [hv]
    have hg0 := (correction_data hq).2.1.ne'
    have ht0 : 1 - (nu q)⁻¹ ≠ 0 := by
      exact (sub_pos.mpr (inv_lt_one_of_one_lt₀
        (show 1 < nu q by linarith only [hv]))).ne'
    dsimp [J, t]
    field_simp [hv0, hm0, ht0, hg0] <;> ring

private theorem scaled_limit : Tendsto (fun q : ℕ => (q : ℝ)^3 * e q) atTop
    (nhds (-Real.log 2 / 3 + 2 * (Real.log 2)^3 / 45)) := by
  have hi := normalized_limits.1
  have hratio : Tendsto (fun q : ℕ => nu q / (nu q - 1)) atTop (nhds 1) := by
    have hden : Tendsto (fun q : ℕ => (1 : ℝ) - (nu q)⁻¹) atTop (nhds 1) := by
      simpa only [sub_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub hi
    have ht : Tendsto (fun q : ℕ => 1 / (1 - (nu q)⁻¹)) atTop (nhds 1) := by
      have hquot := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop
        (nhds 1)).div hden (by norm_num)
      change Tendsto (fun q : ℕ => (1 : ℝ) / (1 - (nu q)⁻¹)) atTop
        (nhds ((1 : ℝ) / 1)) at hquot
      simpa only [div_one] using hquot
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 3] with q hq
    have hv := (base_data hq).2.1
    have hv0 : nu q ≠ 0 := by linarith only [hv]
    have hm0 : nu q - 1 ≠ 0 := by linarith only [hv]
    field_simp [hv0, hm0] <;> ring
  obtain ⟨hA, hJ⟩ := rescaled_coefficients_tendsto
  have ht : Tendsto (fun q : ℕ =>
      -(sigma q / 3) * (nu q / (nu q - 1)) +
        (nu q * A q) * (sigma q)^3 + (nu q * J q) * (sigma q)^4) atTop
      (nhds (-Real.log 2 / 3 + 2 * (Real.log 2)^3 / 45)) := by
    convert (((sigma_tendsto.div_const 3).neg.mul hratio).add
      (hA.mul (sigma_tendsto.pow 3))).add (hJ.mul (sigma_tendsto.pow 4)) using 1 <;> ring
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 3] with q hq
  have hm0 : nu q - 1 ≠ 0 := by linarith only [(base_data hq).2.1]
  calc
    -(sigma q / 3) * (nu q / (nu q - 1)) +
        (nu q * A q) * (sigma q)^3 + (nu q * J q) * (sigma q)^4 =
        nu q * (-sigma q / (3 * (nu q - 1)) +
          A q * (sigma q)^3 + J q * (sigma q)^4) := by
            field_simp [hm0] <;> ring
    _ = nu q * (Q q * e q) := by rw [compact_formula hq]
    _ = (q : ℝ)^3 * e q := by dsimp [nu, Q]; ring

/-- Total analytic coefficients, all natural q>=3 (including even q), and the full Nat limit. -/
theorem square_displacement_fourth_coefficient :
    let Q : ℕ → ℝ := fun q => (q : ℝ)
    let nu : ℕ → ℝ := fun q => (Q q)^2
    let beta : ℕ → ℝ := fun q => dbonacciPerronRoot (q^2)
    let sigma : ℕ → ℝ := fun q => Real.log (beta q)
    let w : ℕ → ℝ := fun q => Real.exp (-nu q * sigma q)
    let alpha : ℕ → ℝ := fun q => (nu q - 1) / (4 * Q q * sigma q)
    let g : ℕ → ℝ := fun q => beta q - nu q * w q
    let C : ℕ → ℝ := fun q => 2 * (nu q + 1) / (3 * (nu q - 1)^2)
    let E : ℕ → ℝ := fun q => 4 / (3 * (nu q - 1)^2)
    let B : ℕ → ℝ := fun q =>
      16 * ((nu q)^2 + nu q + 1) / (15 * (nu q - 1)^4)
    let H : ℕ → ℝ → ℝ := fun q s =>
      C q * s^3 * (Real.exp s - (nu q)^2 * Real.exp (-nu q * s))
    let K : ℕ → ℝ → ℝ := fun q s =>
      -E q * s^3 * (Real.exp s - nu q * Real.exp (-nu q * s)) +
        B q * s^5 * (Real.exp s - (nu q)^3 * Real.exp (-nu q * s)) +
        ((C q)^2 / 2) * s^6 * (Real.exp s + (nu q)^4 * Real.exp (-nu q * s))
    let d : ℕ → ℝ := fun q =>
      (nu q + 1) * sigma q / (6 * Q q * (nu q - 1)) *
        ((((nu q)^2 + 1) * beta q - 2 * (nu q)^2) /
          ((nu q + 1) * beta q - 2 * nu q))
    let u : ℕ → ℝ := fun q => -sigma q * d q / alpha q
    let G2 : ℕ → ℝ := fun q => beta q + (nu q)^2 * w q
    let Hp : ℕ → ℝ := fun q =>
      C q * (3 * (sigma q)^2 * (beta q - (nu q)^2 * w q) +
        (sigma q)^3 * (beta q + (nu q)^3 * w q))
    let e : ℕ → ℝ := fun q =>
      (d q)^2 / alpha q + alpha q / (sigma q * g q) *
        (G2 q * (u q)^2 / 2 + Hp q * u q + K q (sigma q))
    let r : ℕ → ℝ := fun q => nu q * (nu q - 1) * w q / g q
    let A : ℕ → ℝ := fun q =>
      (2 * ((nu q)^2 - 4 * nu q + 1) -
        4 * (nu q + 1) * (3 * (nu q)^2 - 2 * nu q - 2) * r q -
        10 * (nu q + 1)^2 * (r q)^2) / (45 * (nu q - 1)^3)
    let J : ℕ → ℝ := fun q =>
      beta q * (nu q)^2 * w q * (nu q + 1)^2 / (9 * (nu q - 1) * (g q)^3)
    (∀ q : ℕ, 3 ≤ q → e q < 0) ∧
    (∀ q : ℕ, 3 ≤ q → u q = -H q (sigma q) / g q ∧
      G2 q * (u q)^2 / 2 + Hp q * u q + K q (sigma q) +
        g q * (sigma q * (d q)^2 / (alpha q)^2 - sigma q * e q / alpha q) = 0) ∧
    (∀ q : ℕ, 3 ≤ q → Q q * e q = -sigma q / (3 * (nu q - 1)) +
      A q * (sigma q)^3 + J q * (sigma q)^4) ∧
    Tendsto (fun q : ℕ => (q : ℝ)^3 * e q) atTop
      (nhds (-Real.log 2 / 3 + 2 * (Real.log 2)^3 / 45)) := by
  change
    (∀ q : ℕ, 3 ≤ q → e q < 0) ∧
    (∀ q : ℕ, 3 ≤ q → u q = -H q (sigma q) / g q ∧
      G2 q * (u q)^2 / 2 + Hp q * u q + K q (sigma q) +
        g q * (sigma q * (d q)^2 / (alpha q)^2 - sigma q * e q / alpha q) = 0) ∧
    (∀ q : ℕ, 3 ≤ q → Q q * e q = -sigma q / (3 * (nu q - 1)) +
      A q * (sigma q)^3 + J q * (sigma q)^4) ∧
    Tendsto (fun q : ℕ => (q : ℝ)^3 * e q) atTop
      (nhds (-Real.log 2 / 3 + 2 * (Real.log 2)^3 / 45))
  exact ⟨fun _ hq => strict_negative hq,
    fun _ hq => ⟨(correction_data hq).2.2.2, exact_cancellation hq⟩,
    fun _ hq => compact_formula hq, scaled_limit⟩

end D5.S3.FiniteGroups.BajnokBeattySquareDisplacementFourthCoefficient
