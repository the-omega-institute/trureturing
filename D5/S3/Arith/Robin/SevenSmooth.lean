/- GID: D5/S3/Arith/Robin/SevenSmooth
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/SevenSmooth
   mirror-E: none(waiver:universal-inequality)
   anchors: []
   utility: none
   digest: Every product of powers of 2, 3, 5 and 7 above 5040 satisfies Robin's inequality. -/

import D5.S3.Arith.GoldenResource.RobinRationalBasis
import Mathlib.Tactic.FinCases

namespace D5.S3.Arith.Robin.SevenSmooth

open D5.S3.Arith.GoldenResource.RobinRationalBasis

private def smooth (a b c d : Nat) : Nat := 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d

private def geometric (p e : Nat) : Nat :=
  (Finset.range (e + 1)).sum (fun i => p ^ i)

private def divisorSum (a b c d : Nat) : Nat :=
  geometric 2 a * geometric 3 b * geometric 5 c * geometric 7 d

private theorem sigma_smooth (a b c d : Nat) :
    ArithmeticFunction.sigma 1 (smooth a b c d) = divisorSum a b c d := by
  have cop (p q i j : Nat) (h : Nat.Coprime p q) : Nat.Coprime (p ^ i) (q ^ j) :=
    (h.pow_left i).pow_right j
  unfold smooth divisorSum geometric
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
      (((cop 2 7 a d (by decide)).mul_left (cop 3 7 b d (by decide))).mul_left
        (cop 5 7 c d (by decide))),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
      ((cop 2 5 a c (by decide)).mul_left (cop 3 5 b c (by decide))),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (cop 2 3 a b (by decide)),
    ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 2),
    ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 3),
    ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 5),
    ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 7)]

private theorem geometric_bound {p : Nat} (hp : 1 < p) (e : Nat) :
    (geometric p e : Real) < (p : Real) / ((p : Real) - 1) * (p : Real) ^ e := by
  have hpR : (1 : Real) < p := by exact_mod_cast hp
  have hg : (geometric p e : Real) * ((p : Real) - 1) = (p : Real) ^ (e + 1) - 1 := by
    simpa only [geometric, Nat.cast_sum, Nat.cast_pow] using geom_sum_mul (p : Real) (e + 1)
  rw [div_mul_eq_mul_div, lt_div_iff₀ (by linarith : (0 : Real) < p - 1)]
  rw [pow_succ] at hg
  nlinarith only [hg]

private theorem sigma_uniform_bound (a b c d : Nat) :
    (ArithmeticFunction.sigma 1 (smooth a b c d) : Real) <
      (35 / 8 : Real) * smooth a b c d := by
  rw [sigma_smooth]
  have h2 := geometric_bound (by norm_num : 1 < (2 : Nat)) a
  have h3 := geometric_bound (by norm_num : 1 < (3 : Nat)) b
  have h5 := geometric_bound (by norm_num : 1 < (5 : Nat)) c
  have h7 := geometric_bound (by norm_num : 1 < (7 : Nat)) d
  simp only [Nat.cast_ofNat] at h2 h3 h5 h7
  calc
    (divisorSum a b c d : Real) =
        (geometric 2 a : Real) * geometric 3 b * geometric 5 c * geometric 7 d := by
      simp only [divisorSum, Nat.cast_mul]
    _ < (2 / (2 - 1) * (2 : Real) ^ a) * (3 / (3 - 1) * (3 : Real) ^ b) *
        (5 / (5 - 1) * (5 : Real) ^ c) * (7 / (7 - 1) * (7 : Real) ^ d) := by
      gcongr
    _ = (35 / 8 : Real) * smooth a b c d := by
      simp only [smooth, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring

-- This private finite arithmetic statement is consumed only by the universal theorem.
private theorem small_values (a : Fin 17) :
    forall (b : Fin 11) (c : Fin 8) (d : Fin 7),
      5040 < smooth a b c d -> smooth a b c d < 131072 ->
      if smooth a b c d < 10000 then
        100 * divisorSum a b c d <= 381 * smooth a b c d
      else if smooth a b c d < 20000 then
        50 * divisorSum a b c d <= 197 * smooth a b c d
      else 100 * divisorSum a b c d <= 407 * smooth a b c d := by
  fin_cases a <;> decide +kernel

private theorem exponent_bounds (a b c d : Nat) (h : smooth a b c d < 131072) :
    a < 17 ∧ b < 11 ∧ c < 8 ∧ d < 7 := by
  have ha : 2 ^ a <= smooth a b c d := Nat.le_of_dvd (by unfold smooth; positivity)
    (by
      unfold smooth
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _)
  have hb : 3 ^ b <= smooth a b c d := Nat.le_of_dvd (by unfold smooth; positivity)
    (by
      unfold smooth
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _)
  have hc : 5 ^ c <= smooth a b c d := Nat.le_of_dvd (by unfold smooth; positivity)
    (by unfold smooth; exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _)
  have hd : 7 ^ d <= smooth a b c d := Nat.le_of_dvd (by unfold smooth; positivity)
    (by unfold smooth; exact dvd_mul_left _ _)
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals by_contra hx
  · have := Nat.pow_le_pow_right (by norm_num : 0 < (2 : Nat)) (show 17 <= a by omega)
    norm_num at this
    omega
  · have := Nat.pow_le_pow_right (by norm_num : 0 < (3 : Nat)) (show 11 <= b by omega)
    norm_num at this
    omega
  · have := Nat.pow_le_pow_right (by norm_num : 0 < (5 : Nat)) (show 8 <= c by omega)
    norm_num at this
    omega
  · have := Nat.pow_le_pow_right (by norm_num : 0 < (7 : Nat)) (show 7 <= d by omega)
    norm_num at this
    omega

private theorem exp_gamma_lower : (89 / 50 : Real) < Real.exp Real.eulerMascheroniConstant := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : Real) <= 577 / 1000) 5
  norm_num [Finset.sum_range_succ] at h
  have he : Real.exp (577 / 1000) <= Real.exp Real.eulerMascheroniConstant :=
    Real.exp_le_exp.mpr (by linarith only [eulerMascheroni_decimal_bounds.1])
  linarith only [h, he]

private theorem log_lower (x y l : Real) (k K : Nat)
    (hx : x = (2 : Real) ^ k * y) (hk : 1 <= k) (hy : 1 <= y) (hy' : y < 2)
    (hc : l < (k : Real) * (6931471803 / 10000000000 : Real) +
      atanhPartial ((y - 1) / (y + 1)) K) : l < Real.log x := by
  rw [hx]
  exact hc.trans (log_pow_two_mul_bounds y k K hk hy hy').1

private theorem loglog_5040 : (1071 / 500 : Real) < Real.log (Real.log 5040) := by
  have h := log_lower 5040 (315 / 256) (341 / 40) 12 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hh := log_lower (341 / 40) (341 / 320) (1071 / 500) 3 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  exact hh.trans (Real.log_lt_log (by norm_num) h)

private theorem loglog_10000 : (111 / 50 : Real) < Real.log (Real.log 10000) := by
  have h := log_lower 10000 (625 / 512) (921 / 100) 13 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hh := log_lower (921 / 100) (921 / 800) (111 / 50) 3 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  exact hh.trans (Real.log_lt_log (by norm_num) h)

private theorem loglog_20000 : (229 / 100 : Real) < Real.log (Real.log 20000) := by
  have h := log_lower 20000 (625 / 512) (99 / 10) 14 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hh := log_lower (99 / 10) (99 / 80) (229 / 100) 3 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  exact hh.trans (Real.log_lt_log (by norm_num) h)

private theorem loglog_tail : (123 / 50 : Real) < Real.log (Real.log 131072) := by
  have h := log_lower 131072 1 (589 / 50) 17 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial])
  have hh := log_lower (589 / 50) (589 / 400) (123 / 50) 3 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  exact hh.trans (Real.log_lt_log (by norm_num) h)

private theorem rhs_lower {m n : Nat} {l : Real} (hm : 1 < m) (hmn : m <= n)
    (hl : 0 < l) (hlog : l < Real.log (Real.log (m : Real))) :
    (89 / 50 : Real) * l <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : Real)) := by
  have hmR : (1 : Real) < m := by exact_mod_cast hm
  have hmnR : (m : Real) <= n := by exact_mod_cast hmn
  have hlogn : l < Real.log (Real.log (n : Real)) := hlog.trans_le
    (Real.log_le_log (Real.log_pos hmR) (Real.log_le_log (by linarith) hmnR))
  exact mul_lt_mul exp_gamma_lower hlogn.le hl (Real.exp_pos _).le

/-- Robin's strict inequality for the whole family, with no bound on any exponent. -/
theorem robin_seven_smooth (a b c d : Nat) (hn : 5040 < 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d) :
    (ArithmeticFunction.sigma 1 (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d) : Real) /
        (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d : Nat) <
      Real.exp Real.eulerMascheroniConstant *
        Real.log (Real.log (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d : Nat)) := by
  change (ArithmeticFunction.sigma 1 (smooth a b c d) : Real) / smooth a b c d <
    Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (smooth a b c d : Real))
  change 5040 < smooth a b c d at hn
  have hnR : (0 : Real) < smooth a b c d := by exact_mod_cast (show 0 < smooth a b c d by omega)
  by_cases ht : smooth a b c d < 131072
  · obtain ⟨ha, hb, hc, hd⟩ := exponent_bounds a b c d ht
    have hv := small_values ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩ hn ht
    rw [← sigma_smooth] at hv
    by_cases h1 : smooth a b c d < 10000
    · rw [if_pos h1] at hv
      have hbnd : (ArithmeticFunction.sigma 1 (smooth a b c d) : Real) /
          smooth a b c d <= 381 / 100 := by
        rw [div_le_iff₀ hnR]
        have hvR : (100 : Real) * ArithmeticFunction.sigma 1 (smooth a b c d) <=
            381 * smooth a b c d := by exact_mod_cast hv
        linarith only [hvR]
      have hr := rhs_lower (by norm_num : 1 < (5040 : Nat)) (by omega : 5040 <= smooth a b c d)
        (by norm_num) loglog_5040
      exact hbnd.trans_lt (by norm_num at hr; linarith only [hr])
    · rw [if_neg h1] at hv
      by_cases h2 : smooth a b c d < 20000
      · rw [if_pos h2] at hv
        have hbnd : (ArithmeticFunction.sigma 1 (smooth a b c d) : Real) /
            smooth a b c d <= 197 / 50 := by
          rw [div_le_iff₀ hnR]
          have hvR : (50 : Real) * ArithmeticFunction.sigma 1 (smooth a b c d) <=
              197 * smooth a b c d := by exact_mod_cast hv
          linarith only [hvR]
        have hr := rhs_lower (by norm_num : 1 < (10000 : Nat))
          (by omega : 10000 <= smooth a b c d) (by norm_num) loglog_10000
        exact hbnd.trans_lt (by norm_num at hr; linarith only [hr])
      · rw [if_neg h2] at hv
        have hbnd : (ArithmeticFunction.sigma 1 (smooth a b c d) : Real) /
            smooth a b c d <= 407 / 100 := by
          rw [div_le_iff₀ hnR]
          have hvR : (100 : Real) * ArithmeticFunction.sigma 1 (smooth a b c d) <=
              407 * smooth a b c d := by exact_mod_cast hv
          linarith only [hvR]
        have hr := rhs_lower (by norm_num : 1 < (20000 : Nat))
          (by omega : 20000 <= smooth a b c d) (by norm_num) loglog_20000
        exact hbnd.trans_lt (by norm_num at hr; linarith only [hr])
  · have hbound : (ArithmeticFunction.sigma 1 (smooth a b c d) : Real) /
        smooth a b c d < 35 / 8 := (div_lt_iff₀ hnR).mpr (sigma_uniform_bound a b c d)
    have hr := rhs_lower (by norm_num : 1 < (131072 : Nat))
      (by omega : 131072 <= smooth a b c d) (by norm_num) loglog_tail
    exact hbound.trans (by norm_num at hr; linarith only [hr])

#print axioms robin_seven_smooth

end D5.S3.Arith.Robin.SevenSmooth
