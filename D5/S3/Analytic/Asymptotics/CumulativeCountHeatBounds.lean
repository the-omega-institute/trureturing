/- GID: D5/S3/Analytic/Asymptotics/CumulativeCountHeatBounds
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/CumulativeCountHeatBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cumulative geometric counts give summability and two-sided heat bounds. -/

import Mathlib

open Filter
open scoped Topology
open scoped BigOperators

namespace D5.S3.Analytic.Asymptotics.CumulativeCountHeatBounds

noncomputable section

set_option maxHeartbeats 800000 in
-- The single theorem contains the full cutoff, summability, and comparison argument.
/-- A monotone cumulative geometric count controls the scalar heat series at every positive time. -/
theorem cumulative_count_heat_bounds (N : ℕ → ℕ) (c_minus c_plus lambda q : ℝ)
    (hN : Monotone N) (hN0 : N 0 = 1)
    (hcminus : 0 < c_minus) (hcplus : 0 < c_plus)
    (hlambda : 1 < lambda) (hq : 1 < q)
    (hcount : ∀ L : ℕ,
      c_minus * lambda ^ L ≤ (N L : ℝ) ∧ (N L : ℝ) ≤ c_plus * lambda ^ L) :
    let m : ℕ → ℕ := fun L => match L with
      | 0 => 1
      | k + 1 => N (k + 1) - N k
    let a : ℕ → ℝ := fun L => match L with
      | 0 => 0
      | k + 1 => q ^ (k + 1)
    let gamma : ℝ := Real.log lambda / Real.log q
    let F : ℝ → ℕ → ℝ := fun t L => (m L : ℝ) * Real.exp (-t * a L)
    let S : ℝ → ℝ := fun t => ∑' L : ℕ, F t L
    let u : ℕ → ℝ := fun k => lambda ^ (k + 1) * Real.exp (-(q ^ k))
    let U : ℝ := ∑' k : ℕ, u k
    let C_minus : ℝ := c_minus / (Real.exp 1 * lambda)
    let C_plus : ℝ := c_plus * (1 + U)
    (0 < gamma ∧ 0 < C_minus ∧ 0 < C_plus) ∧
      (∀ t : ℝ, 0 < t → Summable (fun L => F t L)) ∧
      (∀ t : ℝ, 0 < t → t ≤ 1 →
        C_minus * Real.rpow t (-gamma) ≤ S t ∧
          S t ≤ C_plus * Real.rpow t (-gamma)) := by
  dsimp
  let m : ℕ → ℕ := fun L => match L with
    | 0 => 1
    | k + 1 => N (k + 1) - N k
  let a : ℕ → ℝ := fun L => match L with
    | 0 => 0
    | k + 1 => q ^ (k + 1)
  let gamma : ℝ := Real.log lambda / Real.log q
  let F : ℝ → ℕ → ℝ := fun t L => (m L : ℝ) * Real.exp (-t * a L)
  let S : ℝ → ℝ := fun t => ∑' L : ℕ, F t L
  let u : ℕ → ℝ := fun k => lambda ^ (k + 1) * Real.exp (-(q ^ k))
  have hloglambda : 0 < Real.log lambda := Real.log_pos hlambda
  have hlogq : 0 < Real.log q := Real.log_pos hq
  have hgamma : 0 < gamma := div_pos hloglambda hlogq
  have hu_pos : ∀ k : ℕ, 0 < u k := by
    intro k
    dsimp [u]
    positivity
  have hqpow : Tendsto (fun k : ℕ => q ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hq
  have hratio_exp : Tendsto (fun k : ℕ =>
      Real.exp (-(q - 1) * (q ^ k))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact Filter.Tendsto.const_mul_atTop_of_neg (by linarith : -(q - 1) < 0) hqpow
  have hratio : Tendsto (fun k : ℕ => ‖u (k + 1)‖ / ‖u k‖) atTop (𝓝 0) := by
    have hratio_eq : (fun k : ℕ => ‖u (k + 1)‖ / ‖u k‖) =
        (fun k : ℕ => lambda * Real.exp (-(q - 1) * (q ^ k))) := by
      funext k
      rw [Real.norm_eq_abs, abs_of_pos (hu_pos (k + 1)),
        Real.norm_eq_abs, abs_of_pos (hu_pos k)]
      dsimp [u]
      rw [div_eq_iff (ne_of_gt (hu_pos k))]
      calc
        lambda ^ (k + 1 + 1) * Real.exp (-q ^ (k + 1)) =
            lambda * (lambda ^ (k + 1) * Real.exp (-q ^ (k + 1))) := by
              rw [pow_succ]
              ring
        _ = lambda * (Real.exp (-(q - 1) * q ^ k) *
            (lambda ^ (k + 1) * Real.exp (-q ^ k))) := by
              have he : Real.exp (-(q - 1) * q ^ k) * Real.exp (-q ^ k) =
                  Real.exp (-q ^ (k + 1)) := by
                rw [← Real.exp_add]
                congr 1
                rw [pow_succ]
                ring
              calc
                lambda * (lambda ^ (k + 1) * Real.exp (-q ^ (k + 1))) =
                    lambda * (lambda ^ (k + 1) *
                      (Real.exp (-(q - 1) * q ^ k) * Real.exp (-q ^ k))) := by
                        rw [he]
                _ = _ := by ring
        _ = lambda * Real.exp (-(q - 1) * q ^ k) * u k := by simp [u]; ring
    rw [hratio_eq]
    simpa using hratio_exp.const_mul lambda
  have hu : Summable u := by
    have hzero : (0 : ℝ) < 1 := by norm_num
    have hne : Filter.Eventually (fun k : ℕ => u k ≠ 0) atTop :=
      Filter.Eventually.of_forall (fun k => ne_of_gt (hu_pos k))
    exact summable_of_ratio_test_tendsto_lt_one hzero hne hratio
  have hprefixNat : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), m k = N n := by
    intro n
    rw [Finset.sum_range_succ']
    dsimp [m]
    rw [Finset.sum_range_tsub hN n, hN0]
    have hNn : 1 ≤ N n := by
      rw [← hN0]
      exact hN (Nat.zero_le n)
    omega
  have hm_le_N : ∀ L : ℕ, (m L : ℝ) ≤ (N L : ℝ) := by
    intro L
    cases L with
    | zero => simp [m, hN0]
    | succ k =>
      dsimp [m]
      exact_mod_cast Nat.sub_le _ _
  have hm_nonneg : ∀ L : ℕ, 0 ≤ (m L : ℝ) := fun L => Nat.cast_nonneg _
  have hF_nonneg : ∀ (t : ℝ) (L : ℕ), 0 ≤ F t L := by
    intro t L
    dsimp [F]
    positivity
  have hF_summable_small : ∀ t : ℝ, 0 < t → t ≤ 1 → Summable (F t) := by
    intro t ht ht1
    let n : ℕ := ⌊Real.logb q (1 / t)⌋₊
    have htpos : 0 < 1 / t := one_div_pos.mpr ht
    have htinv : 1 ≤ 1 / t := by rw [le_div_iff₀ ht]; linarith
    have hlogb_nonneg : 0 ≤ Real.logb q (1 / t) := Real.logb_nonneg hq htinv
    have hcutlo : q ^ n ≤ 1 / t := by
      dsimp [n]
      have := Nat.floor_le hlogb_nonneg
      simpa only [Nat.cast_add, Real.rpow_natCast] using
        (Real.le_logb_iff_rpow_le hq htpos).mp this
    have hcuthi : 1 / t < q ^ (n + 1) := by
      dsimp [n]
      have := Nat.lt_floor_add_one (Real.logb q (1 / t))
      have h := (Real.logb_lt_iff_lt_rpow hq (show 0 < (1 / t) from htpos)).mp this
      rw [← Nat.cast_one, ← Nat.cast_add] at h
      simpa only [Nat.cast_one, Real.rpow_natCast] using h
    have htn : t * q ^ n ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hcutlo ht.le
      simpa [ht.ne'] using h
    have htnext : 1 < t * q ^ (n + 1) := by
      have h := mul_lt_mul_of_pos_left hcuthi ht
      simpa [ht.ne'] using h
    have htail_geom : Summable (fun k : ℕ =>
        c_plus * lambda ^ (k + (n + 1)) * Real.exp (-t * q ^ (k + (n + 1)))) := by
      have htail_le : ∀ k : ℕ,
          c_plus * lambda ^ (k + (n + 1)) * Real.exp (-t * q ^ (k + (n + 1))) ≤
            c_plus * lambda ^ n * u k := by
        intro k
        dsimp [u]
        have hpow : q ^ k ≤ t * q ^ (k + (n + 1)) := by
          have h := mul_lt_mul_of_pos_right htnext (by positivity : 0 < q ^ k)
          exact (calc
            q ^ k < (t * q ^ (n + 1)) * q ^ k := by simpa only [one_mul] using h
            _ = t * q ^ (k + (n + 1)) := by rw [pow_add]; ring).le
        have hexp : Real.exp (-t * q ^ (k + (n + 1))) ≤ Real.exp (-(q ^ k)) := by
          apply Real.exp_monotone
          linarith
        have hlpow : lambda ^ (k + (n + 1)) = lambda ^ n * lambda ^ (k + 1) := by
          rw [pow_add, pow_add]
          ring
        rw [hlpow]
        calc
          c_plus * (lambda ^ n * lambda ^ (k + 1)) *
              Real.exp (-t * q ^ (k + (n + 1))) =
              c_plus * lambda ^ n *
                (lambda ^ (k + 1) * Real.exp (-t * q ^ (k + (n + 1)))) := by ring
          _ ≤ c_plus * lambda ^ n *
                (lambda ^ (k + 1) * Real.exp (-(q ^ k))) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hexp (by positivity)) (by positivity)
      have hscaled : Summable (fun k : ℕ => c_plus * lambda ^ n * u k) := by
        simpa only [mul_assoc] using hu.mul_left (c_plus * lambda ^ n)
      exact Summable.of_nonneg_of_le (fun k => by positivity) htail_le hscaled
    have hgeom_full : Summable (fun k : ℕ =>
        c_plus * lambda ^ k * Real.exp (-t * q ^ k)) := by
      exact (summable_nat_add_iff (n + 1)).mp htail_geom
    have htail_geom_shift : Summable (fun k : ℕ =>
        c_plus * lambda ^ (k + (n + 1)) * Real.exp (-t * q ^ (k + (n + 1)))) := by
      exact (summable_nat_add_iff (n + 1)).mpr hgeom_full
    have hF_tail : Summable (fun k : ℕ => F t (k + (n + 1))) := by
      apply Summable.of_nonneg_of_le (fun k => hF_nonneg t (k + (n + 1)))
      · intro k
        have hNbound := (hcount (k + (n + 1))).2
        dsimp [F, a]
        calc
          (m (k + (n + 1)) : ℝ) * Real.exp
              (-t * a (k + (n + 1))) ≤
              (N (k + (n + 1)) : ℝ) * Real.exp
                (-t * a (k + (n + 1))) :=
            mul_le_mul_of_nonneg_right (hm_le_N (k + (n + 1))) (Real.exp_nonneg _)
          _ ≤ c_plus * lambda ^ (k + (n + 1)) * Real.exp
                (-t * q ^ (k + (n + 1))) := by
            have ha : a (k + (n + 1)) = q ^ (k + (n + 1)) := by
              have hidx : k + n + 1 = k + (n + 1) := by omega
              simp [a, hidx]
            rw [ha]
            exact mul_le_mul_of_nonneg_right hNbound (Real.exp_nonneg _)
      · exact htail_geom_shift
    have hFfull : Summable (F t) := (summable_nat_add_iff (n + 1)).mp hF_tail
    exact hFfull
  have hF_summable : ∀ t : ℝ, 0 < t → Summable (F t) := by
    intro t ht
    by_cases ht1 : t ≤ 1
    · exact hF_summable_small t ht ht1
    · have hF1 := hF_summable_small 1 zero_lt_one le_rfl
      exact Summable.of_nonneg_of_le (fun L => hF_nonneg t L) (fun L => by
        dsimp [F]
        have ha : 0 ≤ a L := by
          cases L with
          | zero => simp [a]
          | succ j => dsimp [a]; positivity
        have he : Real.exp (-t * a L) ≤ Real.exp (-1 * a L) := by
          apply Real.exp_monotone
          have ht1' : 1 < t := lt_of_not_ge ht1
          have hmul := mul_le_mul_of_nonneg_right ht1'.le ha
          linarith
        exact mul_le_mul_of_nonneg_left he (hm_nonneg L)) hF1
  let U : ℝ := ∑' k : ℕ, u k
  let C_minus : ℝ := c_minus / (Real.exp 1 * lambda)
  let C_plus : ℝ := c_plus * (1 + U)
  have hU_nonneg : 0 ≤ U := by
    dsimp [U]
    exact tsum_nonneg (fun k => (hu_pos k).le)
  have hU_pos : 0 < 1 + U := by linarith
  have hCminus : 0 < C_minus := by
    dsimp [C_minus]
    positivity
  have hCplus : 0 < C_plus := by
    dsimp [C_plus]
    positivity
  refine ⟨⟨hgamma, hCminus, hCplus⟩, hF_summable, ?_⟩
  intro t ht ht1
  let n : ℕ := ⌊Real.logb q (1 / t)⌋₊
  have htpos : 0 < 1 / t := one_div_pos.mpr ht
  have htinv : 1 ≤ 1 / t := by rw [le_div_iff₀ ht]; linarith
  have hlogb_nonneg : 0 ≤ Real.logb q (1 / t) := Real.logb_nonneg hq htinv
  have hcutlo : q ^ n ≤ 1 / t := by
    have h := (Real.le_logb_iff_rpow_le hq htpos).mp (Nat.floor_le hlogb_nonneg)
    simpa only [Real.rpow_natCast] using h
  have hcuthi : 1 / t < q ^ (n + 1) := by
    have h := (Real.logb_lt_iff_lt_rpow hq htpos).mp (Nat.lt_floor_add_one _)
    rw [← Nat.cast_one, ← Nat.cast_add] at h
    simpa only [Nat.cast_one, Real.rpow_natCast] using h
  have htn : t * q ^ n ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hcutlo ht.le
    simpa [ht.ne'] using h
  have htnext : 1 < t * q ^ (n + 1) := by
    have h := mul_lt_mul_of_pos_left hcuthi ht
    simpa [ht.ne'] using h
  have hFsum := hF_summable t ht
  have hdecomp := hFsum.sum_add_tsum_nat_add (n + 1)
  have hprefix_upper : ∑ k ∈ Finset.range (n + 1), F t k ≤ (N n : ℝ) := by
    calc
      ∑ k ∈ Finset.range (n + 1), F t k ≤
          ∑ k ∈ Finset.range (n + 1), (m k : ℝ) :=
        Finset.sum_le_sum (fun k _ => by
          dsimp [F]
          have ha : 0 ≤ a k := by
            cases k with
            | zero => simp [a]
            | succ j => dsimp [a]; positivity
          have hE : Real.exp (-t * a k) ≤ 1 :=
            have hneg : -t * a k ≤ 0 := by
              nlinarith [mul_nonneg ht.le ha]
            Real.exp_le_one_iff.mpr hneg
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hE (hm_nonneg k))
      _ = (N n : ℝ) := by
        rw [← Nat.cast_sum, hprefixNat n]
  have hprefix_lower : (Real.exp (-1)) * (N n : ℝ) ≤
      ∑ k ∈ Finset.range (n + 1), F t k := by
    have hterm : ∀ k ∈ Finset.range (n + 1),
        Real.exp (-1) * (m k : ℝ) ≤ F t k := by
      intro k hk
      dsimp [F]
      have hklt : k < n + 1 := Finset.mem_range.mp hk
      have hk_le : k ≤ n := by omega
      have hak : a k ≤ q ^ n := by
        cases k with
        | zero => simpa [a] using (pow_nonneg (by positivity : (0 : ℝ) ≤ q) n)
        | succ j =>
          dsimp [a]
          have hj : j + 1 ≤ n := by omega
          exact pow_le_pow_right₀ hq.le hj
      have he : Real.exp (-1) ≤ Real.exp (-t * a k) := by
        apply Real.exp_monotone
        have : t * a k ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hak ht.le) htn
        linarith
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left he (hm_nonneg k)
    calc
      Real.exp (-1) * (N n : ℝ) = Real.exp (-1) * ∑ k ∈ Finset.range (n + 1), (m k : ℝ) := by
        congr 1
        exact_mod_cast (hprefixNat n).symm
      _ = ∑ k ∈ Finset.range (n + 1), (Real.exp (-1) * (m k : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum hterm
  have htail_le : ∀ k : ℕ,
      F t (k + (n + 1)) ≤ c_plus * lambda ^ n * u k := by
    intro k
    have hNbound := (hcount (k + (n + 1))).2
    dsimp [F, a, u]
    have hpow : q ^ k ≤ t * q ^ (k + (n + 1)) := by
      have h := mul_lt_mul_of_pos_right htnext (by positivity : 0 < q ^ k)
      have h' : q ^ k < t * q ^ (k + (n + 1)) := by
        calc
          q ^ k < (t * q ^ (n + 1)) * q ^ k := by simpa only [one_mul] using h
          _ = t * q ^ (k + (n + 1)) := by rw [pow_add]; ring
      exact h'.le
    have hexp : Real.exp (-t * q ^ (k + (n + 1))) ≤ Real.exp (-(q ^ k)) := by
      apply Real.exp_monotone
      linarith
    have hlpow : lambda ^ (k + (n + 1)) = lambda ^ n * lambda ^ (k + 1) := by
      rw [pow_add, pow_add]
      ring
    calc
      (m (k + (n + 1)) : ℝ) * Real.exp (-t * a (k + (n + 1))) ≤
          (N (k + (n + 1)) : ℝ) * Real.exp (-t * a (k + (n + 1))) :=
        mul_le_mul_of_nonneg_right (hm_le_N (k + (n + 1))) (Real.exp_nonneg _)
      _ ≤ c_plus * lambda ^ (k + (n + 1)) *
            Real.exp (-t * q ^ (k + (n + 1))) := by
          have ha : a (k + (n + 1)) = q ^ (k + (n + 1)) := by
            have hidx : k + n + 1 = k + (n + 1) := by omega
            simp [a, hidx]
          rw [ha]
          exact mul_le_mul_of_nonneg_right hNbound (Real.exp_nonneg _)
      _ = c_plus * lambda ^ n *
            (lambda ^ (k + 1) * Real.exp (-t * q ^ (k + (n + 1)))) := by
          rw [hlpow]
          ring
      _ ≤ c_plus * lambda ^ n * (lambda ^ (k + 1) * Real.exp (-(q ^ k))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hexp (by positivity)) (by positivity)
  have htail_sum : Summable (fun k : ℕ => F t (k + (n + 1))) :=
    (summable_nat_add_iff (n + 1)).mpr hFsum
  have hscaled : Summable (fun k : ℕ => c_plus * lambda ^ n * u k) := by
    simpa only [mul_assoc] using hu.mul_left (c_plus * lambda ^ n)
  have htail_tsum : (∑' k : ℕ, F t (k + (n + 1))) ≤ c_plus * lambda ^ n * U := by
    calc
      (∑' k : ℕ, F t (k + (n + 1))) ≤ ∑' k : ℕ, c_plus * lambda ^ n * u k :=
        htail_sum.tsum_le_tsum htail_le hscaled
      _ = c_plus * lambda ^ n * U := by
        dsimp [U]
        rw [Summable.tsum_mul_left _ hu]
  have hS_eq : S t = (∑ k ∈ Finset.range (n + 1), F t k) +
      ∑' k : ℕ, F t (k + (n + 1)) := by
    dsimp [S]
    exact hdecomp.symm
  have hS_lower : Real.exp (-1) * (N n : ℝ) ≤ S t := by
    rw [hS_eq]
    linarith [hFsum.sum_le_tsum (Finset.range (n + 1)) (fun k _ => hF_nonneg t k)]
  have hS_upper : S t ≤ (N n : ℝ) + c_plus * lambda ^ n * U := by
    rw [hS_eq]
    linarith [hprefix_upper, htail_tsum]
  have hqgamma : q ^ gamma = lambda := by
    rw [Real.rpow_def_of_pos (by positivity : 0 < q)]
    rw [show Real.log q * gamma = Real.log lambda by
      dsimp [gamma]
      field_simp [ne_of_gt hlogq]]
    exact Real.exp_log (by positivity)
  have hpowt : (1 / t) ^ gamma = Real.rpow t (-gamma) := by
    rw [show (1 / t : ℝ) = t⁻¹ by simp, Real.inv_rpow ht.le]
    exact (Real.rpow_neg ht.le gamma).symm
  have hpower_upper : lambda ^ n ≤ Real.rpow t (-gamma) := by
    have hlowr : (q ^ n : ℝ) ^ gamma ≤ (1 / t) ^ gamma :=
      Real.rpow_le_rpow (by positivity) hcutlo hgamma.le
    have hqnr : (q ^ n : ℝ) ^ gamma = lambda ^ n := by
      rw [← Real.rpow_natCast q n, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ q)]
      rw [mul_comm]
      rw [Real.rpow_mul (by positivity : (0 : ℝ) ≤ q)]
      rw [Real.rpow_natCast, hqgamma]
    rw [hpowt, hqnr] at hlowr
    exact hlowr
  have hpower_lower : lambda ^ n ≥ Real.rpow t (-gamma) / lambda := by
    have hhighr : Real.rpow t (-gamma) <
        (q ^ (n + 1) : ℝ) ^ gamma := by
      have h := Real.rpow_lt_rpow (by positivity : (0 : ℝ) ≤ 1 / t)
        hcuthi hgamma
      rw [hpowt] at h
      exact h
    have hqnr : (q ^ (n + 1) : ℝ) ^ gamma = lambda ^ (n + 1) := by
      rw [← Real.rpow_natCast q (n + 1)]
      rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ q)]
      rw [mul_comm]
      rw [Real.rpow_mul (by positivity : (0 : ℝ) ≤ q)]
      rw [Real.rpow_natCast, hqgamma]
    rw [hqnr] at hhighr
    have hdiv : Real.rpow t (-gamma) / lambda < lambda ^ n := by
      apply (div_lt_iff₀ (lt_trans zero_lt_one hlambda)).2
      simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hhighr
    exact hdiv.le
  have hlow_final : C_minus * Real.rpow t (-gamma) ≤ S t := by
    have hNlower := (hcount n).1
    have hmul := mul_le_mul_of_nonneg_left hNlower (Real.exp_pos (-1)).le
    have hconst : C_minus * Real.rpow t (-gamma) =
        Real.exp (-1) * (c_minus / lambda) * Real.rpow t (-gamma) := by
      dsimp [C_minus]
      rw [show Real.exp (-1) = (Real.exp 1)⁻¹ by rw [Real.exp_neg]]
      field_simp [ne_of_gt (Real.exp_pos 1), ne_of_gt (zero_lt_one.trans hlambda)]
    rw [hconst]
    have hratio : (c_minus / lambda) * Real.rpow t (-gamma) ≤
        c_minus * lambda ^ n := by
      have h := mul_le_mul_of_nonneg_left hpower_lower hcminus.le
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
    calc
      Real.exp (-1) * (c_minus / lambda) * Real.rpow t (-gamma) ≤
          Real.exp (-1) * (c_minus * lambda ^ n) := by
            simpa only [mul_assoc] using
              mul_le_mul_of_nonneg_left hratio (Real.exp_pos (-1)).le
      _ ≤ Real.exp (-1) * (N n : ℝ) := hmul
      _ ≤ S t := hS_lower
  have hu_upper : S t ≤ C_plus * Real.rpow t (-gamma) := by
    have hscale := mul_le_mul_of_nonneg_left hpower_upper (mul_nonneg hcplus.le hU_pos.le)
    have hconst : C_plus * Real.rpow t (-gamma) =
        c_plus * (1 + U) * Real.rpow t (-gamma) := by rfl
    rw [hconst]
    calc
      S t ≤ (N n : ℝ) + c_plus * lambda ^ n * U := hS_upper
      _ ≤ c_plus * lambda ^ n * (1 + U) := by
        have hNupper := (hcount n).2
        nlinarith [mul_le_mul_of_nonneg_right hNupper (by positivity : 0 ≤ 1 + U)]
      _ ≤ c_plus * (1 + U) * Real.rpow t (-gamma) := by
        have hnonneg : 0 ≤ c_plus * (1 + U) := mul_nonneg hcplus.le hU_pos.le
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_left hpower_upper hnonneg
  exact ⟨hlow_final, hu_upper⟩

end
end D5.S3.Analytic.Asymptotics.CumulativeCountHeatBounds
