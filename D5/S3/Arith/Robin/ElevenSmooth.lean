/- GID: D5/S3/Arith/Robin/ElevenSmooth
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ElevenSmooth
   mirror-E: none(waiver:universal-inequality)
   anchors: []
   utility: none
   digest: Every product of powers of 2, 3, 5, 7 and 11 above 5040 satisfies Robin's inequality. -/

import D5.S3.Arith.Robin.SevenSmooth
import Mathlib.Tactic.FinCases

/-! The case without the prime 11 is the frozen seven-smooth theorem. The remaining
cases use the saturation bound 77/16 above `2^22` and a kernel-checked finite table
below it. -/

namespace D5.S3.Arith.Robin.ElevenSmooth

open D5.S3.Arith.GoldenResource.RobinRationalBasis

private def smooth (a b c d e : Nat) : Nat := 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 11 ^ e

private def geometric (p e : Nat) : Nat := (Finset.range (e + 1)).sum (fun i => p ^ i)

private def divisorSum (a b c d e : Nat) : Nat :=
  geometric 2 a * geometric 3 b * geometric 5 c * geometric 7 d * geometric 11 e

private theorem sigma_smooth (a b c d e : Nat) :
    ArithmeticFunction.sigma 1 (smooth a b c d e) = divisorSum a b c d e := by
  have cop (p q i j : Nat) (h : Nat.Coprime p q) : Nat.Coprime (p ^ i) (q ^ j) :=
    (h.pow_left i).pow_right j
  unfold smooth divisorSum geometric
  rw [(ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime
      ((((cop 2 11 a e (by decide)).mul_left (cop 3 11 b e (by decide))).mul_left
        (cop 5 11 c e (by decide))).mul_left (cop 7 11 d e (by decide))),
    (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime
      (((cop 2 7 a d (by decide)).mul_left (cop 3 7 b d (by decide))).mul_left
        (cop 5 7 c d (by decide))),
    (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime
      ((cop 2 5 a c (by decide)).mul_left (cop 3 5 b c (by decide))),
    (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime (cop 2 3 a b (by decide)),
    ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 2),
    ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 3),
    ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 5),
    ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 7),
    ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 11)]

private theorem geometric_bound {p : Nat} (hp : 1 < p) (e : Nat) :
    (geometric p e : Real) < (p : Real) / ((p : Real) - 1) * (p : Real) ^ e := by
  have hpR : (1 : Real) < p := by exact_mod_cast hp
  have hg : (geometric p e : Real) * ((p : Real) - 1) = (p : Real) ^ (e + 1) - 1 := by
    simpa only [geometric, Nat.cast_sum, Nat.cast_pow] using geom_sum_mul (p : Real) (e + 1)
  rw [div_mul_eq_mul_div, lt_div_iff₀ (by linarith : (0 : Real) < p - 1)]
  rw [pow_succ] at hg
  nlinarith only [hg]

private theorem sigma_uniform_bound (a b c d e : Nat) :
    (ArithmeticFunction.sigma 1 (smooth a b c d e) : Real) <
      (77 / 16 : Real) * smooth a b c d e := by
  rw [sigma_smooth]
  have h2 := geometric_bound (by norm_num : 1 < (2 : Nat)) a
  have h3 := geometric_bound (by norm_num : 1 < (3 : Nat)) b
  have h5 := geometric_bound (by norm_num : 1 < (5 : Nat)) c
  have h7 := geometric_bound (by norm_num : 1 < (7 : Nat)) d
  have h11 := geometric_bound (by norm_num : 1 < (11 : Nat)) e
  simp only [Nat.cast_ofNat] at h2 h3 h5 h7 h11
  calc
    (divisorSum a b c d e : Real) =
        (geometric 2 a : Real) * geometric 3 b * geometric 5 c * geometric 7 d *
          geometric 11 e := by
      simp only [divisorSum, Nat.cast_mul]
    _ < (2 / (2 - 1) * (2 : Real) ^ a) * (3 / (3 - 1) * (3 : Real) ^ b) *
        (5 / (5 - 1) * (5 : Real) ^ c) * (7 / (7 - 1) * (7 : Real) ^ d) *
          (11 / (11 - 1) * (11 : Real) ^ e) := by
      gcongr
    _ = (77 / 16 : Real) * smooth a b c d e := by
      simp only [smooth, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring

/-- The finite table: the ratio bound on each interval below `2^22`, for one exponent of 11. -/
private abbrev TableBound (n s : Nat) : Prop :=
  if n < 10000 then 100 * s ≤ 375 * n
  else if n < 20000 then 100 * s ≤ 387 * n
  else if n < 40000 then 100 * s ≤ 406 * n
  else if n < 80000 then 100 * s ≤ 419 * n
  else if n < 160000 then 100 * s ≤ 426 * n
  else if n < 640000 then 100 * s ≤ 440 * n
  else 100 * s ≤ 455 * n

-- These private finite arithmetic statements are consumed only by the universal theorem.
private theorem table_1 : ∀ (a : Fin 22) (b : Fin 14) (c : Fin 10) (d : Fin 8),
    5040 < smooth a b c d 1 → smooth a b c d 1 < 4194304 →
      TableBound (smooth a b c d 1) (divisorSum a b c d 1) := by
  intro a
  fin_cases a <;> decide +kernel

private theorem table_2 : ∀ (a : Fin 22) (b : Fin 14) (c : Fin 10) (d : Fin 8),
    5040 < smooth a b c d 2 → smooth a b c d 2 < 4194304 →
      TableBound (smooth a b c d 2) (divisorSum a b c d 2) := by
  intro a
  fin_cases a <;> decide +kernel

private theorem table_3 : ∀ (a : Fin 22) (b : Fin 14) (c : Fin 10) (d : Fin 8),
    5040 < smooth a b c d 3 → smooth a b c d 3 < 4194304 →
      TableBound (smooth a b c d 3) (divisorSum a b c d 3) := by
  intro a
  fin_cases a <;> decide +kernel

private theorem table_4 : ∀ (a : Fin 22) (b : Fin 14) (c : Fin 10) (d : Fin 8),
    5040 < smooth a b c d 4 → smooth a b c d 4 < 4194304 →
      TableBound (smooth a b c d 4) (divisorSum a b c d 4) := by
  intro a
  fin_cases a <;> decide +kernel

private theorem table_5 : ∀ (a : Fin 22) (b : Fin 14) (c : Fin 10) (d : Fin 8),
    5040 < smooth a b c d 5 → smooth a b c d 5 < 4194304 →
      TableBound (smooth a b c d 5) (divisorSum a b c d 5) := by
  intro a
  fin_cases a <;> decide +kernel

private theorem table_6 : ∀ (a : Fin 22) (b : Fin 14) (c : Fin 10) (d : Fin 8),
    5040 < smooth a b c d 6 → smooth a b c d 6 < 4194304 →
      TableBound (smooth a b c d 6) (divisorSum a b c d 6) := by
  intro a
  fin_cases a <;> decide +kernel

private theorem exponent_bounds (a b c d e : Nat) (h : smooth a b c d e < 4194304) :
    a < 22 ∧ b < 14 ∧ c < 10 ∧ d < 8 ∧ e < 7 := by
  have hpos : 0 < smooth a b c d e := by unfold smooth; positivity
  have dv (x : Nat) (hx : x ∣ smooth a b c d e) : x ≤ smooth a b c d e := Nat.le_of_dvd hpos hx
  have ha := dv (2 ^ a) (by
    unfold smooth; exact Dvd.intro (3 ^ b * 5 ^ c * 7 ^ d * 11 ^ e) (by ring))
  have hb := dv (3 ^ b) (by
    unfold smooth; exact Dvd.intro (2 ^ a * 5 ^ c * 7 ^ d * 11 ^ e) (by ring))
  have hc := dv (5 ^ c) (by
    unfold smooth; exact Dvd.intro (2 ^ a * 3 ^ b * 7 ^ d * 11 ^ e) (by ring))
  have hd := dv (7 ^ d) (by
    unfold smooth; exact Dvd.intro (2 ^ a * 3 ^ b * 5 ^ c * 11 ^ e) (by ring))
  have he := dv (11 ^ e) (by
    unfold smooth; exact Dvd.intro_left (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d) rfl)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals by_contra hx
  · have := Nat.pow_le_pow_right (by norm_num : 0 < (2 : Nat)) (show 22 <= a by omega)
    norm_num at this
    omega
  · have := Nat.pow_le_pow_right (by norm_num : 0 < (3 : Nat)) (show 14 <= b by omega)
    norm_num at this
    omega
  · have := Nat.pow_le_pow_right (by norm_num : 0 < (5 : Nat)) (show 10 <= c by omega)
    norm_num at this
    omega
  · have := Nat.pow_le_pow_right (by norm_num : 0 < (7 : Nat)) (show 8 <= d by omega)
    norm_num at this
    omega
  · have := Nat.pow_le_pow_right (by norm_num : 0 < (11 : Nat)) (show 7 <= e by omega)
    norm_num at this
    omega

private theorem table (a b c d e : Nat) (he1 : 1 ≤ e) (hn : 5040 < smooth a b c d e)
    (ht : smooth a b c d e < 4194304) :
    TableBound (smooth a b c d e) (divisorSum a b c d e) := by
  obtain ⟨ha, hb, hc, hd, he⟩ := exponent_bounds a b c d e ht
  interval_cases e
  · exact table_1 ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩ hn ht
  · exact table_2 ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩ hn ht
  · exact table_3 ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩ hn ht
  · exact table_4 ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩ hn ht
  · exact table_5 ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩ hn ht
  · exact table_6 ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩ hn ht

/-- A rational lower bound for `e^γ`. -/
theorem exp_gamma_lower : (89 / 50 : Real) < Real.exp Real.eulerMascheroniConstant := by
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

/-- Two certified logarithm brackets give a rational lower bound for `log (log t)`. -/
theorem loglog_of (t mid lo y₁ y₂ : Real) (k₁ k₂ : Nat)
    (h₁ : t = (2 : Real) ^ k₁ * y₁) (hk₁ : 1 <= k₁) (hy₁ : 1 <= y₁) (hy₁' : y₁ < 2)
    (hc₁ : mid < (k₁ : Real) * (6931471803 / 10000000000 : Real) +
      atanhPartial ((y₁ - 1) / (y₁ + 1)) 4)
    (h₂ : mid = (2 : Real) ^ k₂ * y₂) (hk₂ : 1 <= k₂) (hy₂ : 1 <= y₂) (hy₂' : y₂ < 2)
    (hc₂ : lo < (k₂ : Real) * (6931471803 / 10000000000 : Real) +
      atanhPartial ((y₂ - 1) / (y₂ + 1)) 4) (hmid : 0 < mid) :
    lo < Real.log (Real.log t) := by
  have h := log_lower t y₁ mid k₁ 4 h₁ hk₁ hy₁ hy₁' hc₁
  have hh := log_lower mid y₂ lo k₂ 4 h₂ hk₂ hy₂ hy₂' hc₂
  exact hh.trans (Real.log_lt_log hmid h)

/-- A rational lower bound for `log (log 5040)`. -/
theorem loglog_5040 : (1071 / 500 : Real) < Real.log (Real.log 5040) :=
  loglog_of 5040 (341 / 40) _ (315 / 256) (341 / 320) 12 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [atanhPartial, Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ]) (by norm_num)

private theorem loglog_10000 : (111 / 50 : Real) < Real.log (Real.log 10000) :=
  loglog_of 10000 (921 / 100) _ (625 / 512) (921 / 800) 13 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [atanhPartial, Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ]) (by norm_num)

private theorem loglog_20000 : (229 / 100 : Real) < Real.log (Real.log 20000) :=
  loglog_of 20000 (99 / 10) _ (625 / 512) (99 / 80) 14 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [atanhPartial, Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ]) (by norm_num)

private theorem loglog_40000 : (1179 / 500 : Real) < Real.log (Real.log 40000) :=
  loglog_of 40000 (1059 / 100) _ (625 / 512) (1059 / 800) 15 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [atanhPartial, Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ]) (by norm_num)

private theorem loglog_80000 : (121 / 50 : Real) < Real.log (Real.log 80000) :=
  loglog_of 80000 (282 / 25) _ (625 / 512) (141 / 100) 16 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [atanhPartial, Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ]) (by norm_num)

private theorem loglog_160000 : (62 / 25 : Real) < Real.log (Real.log 160000) :=
  loglog_of 160000 (599 / 50) _ (625 / 512) (599 / 400) 17 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [atanhPartial, Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ]) (by norm_num)

private theorem loglog_640000 : (259 / 100 : Real) < Real.log (Real.log 640000) :=
  loglog_of 640000 (334 / 25) _ (625 / 512) (167 / 100) 19 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [atanhPartial, Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ]) (by norm_num)

private theorem loglog_tail : (271 / 100 : Real) < Real.log (Real.log 4194304) :=
  loglog_of 4194304 (381 / 25) _ 1 (381 / 200) 22 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [atanhPartial, Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ]) (by norm_num)

/-- One interval of the table: a ratio bound `K/100` paid by `89/50 · l < e^γ log log n`. -/
theorem finish {n t K : Nat} {l : Real} (ht : 1 < t) (htn : t ≤ n) (hl : 0 < l)
    (hlog : l < Real.log (Real.log (t : Real))) (hK : (K : Real) / 100 ≤ 89 / 50 * l)
    (hv : 100 * ArithmeticFunction.sigma 1 n ≤ K * n) :
    (ArithmeticFunction.sigma 1 n : Real) / n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : Real)) := by
  have hnR : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have htR : (1 : Real) < t := by exact_mod_cast ht
  have htnR : (t : Real) ≤ n := by exact_mod_cast htn
  have hbnd : (ArithmeticFunction.sigma 1 n : Real) / n ≤ (K : Real) / 100 := by
    rw [div_le_div_iff₀ hnR (by norm_num)]
    have hvR : (100 : Real) * ArithmeticFunction.sigma 1 n ≤ K * n := by exact_mod_cast hv
    linarith only [hvR]
  have hlogn : l < Real.log (Real.log (n : Real)) := hlog.trans_le
    (Real.log_le_log (Real.log_pos htR) (Real.log_le_log (by linarith) htnR))
  have hr : (89 / 50 : Real) * l <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : Real)) :=
    mul_lt_mul exp_gamma_lower hlogn.le hl (Real.exp_pos _).le
  linarith only [hbnd, hK, hr]

/-- Robin's strict inequality for every product of powers of 2, 3, 5, 7 and 11 above 5040,
with no bound on any exponent. -/
theorem robin_eleven_smooth (a b c d e : Nat)
    (hn : 5040 < 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 11 ^ e) :
    (ArithmeticFunction.sigma 1 (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 11 ^ e) : Real) /
        (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 11 ^ e : Nat) <
      Real.exp Real.eulerMascheroniConstant *
        Real.log (Real.log (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 11 ^ e : Nat)) := by
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he
    simp only [pow_zero, mul_one] at hn ⊢
    exact D5.S3.Arith.Robin.SevenSmooth.robin_seven_smooth a b c d hn
  change (ArithmeticFunction.sigma 1 (smooth a b c d e) : Real) / smooth a b c d e <
    Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (smooth a b c d e : Real))
  change 5040 < smooth a b c d e at hn
  have hnR : (0 : Real) < smooth a b c d e := by
    exact_mod_cast (show 0 < smooth a b c d e by omega)
  by_cases ht : smooth a b c d e < 4194304
  · have hv := table a b c d e he hn ht
    rw [← sigma_smooth] at hv
    unfold TableBound at hv
    split_ifs at hv with h1 h2 h3 h4 h5 h6
    · exact finish (t := 5040) (l := 1071 / 500) (by norm_num) hn.le (by norm_num)
        (by exact_mod_cast loglog_5040)
        (by norm_num) hv
    · exact finish (t := 10000) (l := 111 / 50) (by norm_num) (by omega) (by norm_num)
        (by exact_mod_cast loglog_10000) (by norm_num) hv
    · exact finish (t := 20000) (l := 229 / 100) (by norm_num) (by omega) (by norm_num)
        (by exact_mod_cast loglog_20000) (by norm_num) hv
    · exact finish (t := 40000) (l := 1179 / 500) (by norm_num) (by omega) (by norm_num)
        (by exact_mod_cast loglog_40000) (by norm_num) hv
    · exact finish (t := 80000) (l := 121 / 50) (by norm_num) (by omega) (by norm_num)
        (by exact_mod_cast loglog_80000) (by norm_num) hv
    · exact finish (t := 160000) (l := 62 / 25) (by norm_num) (by omega) (by norm_num)
        (by exact_mod_cast loglog_160000) (by norm_num) hv
    · exact finish (t := 640000) (l := 259 / 100) (by norm_num) (by omega) (by norm_num)
        (by exact_mod_cast loglog_640000) (by norm_num) hv
  · have hbound : (ArithmeticFunction.sigma 1 (smooth a b c d e) : Real) /
        smooth a b c d e < 77 / 16 := (div_lt_iff₀ hnR).mpr (sigma_uniform_bound a b c d e)
    have htR : (4194304 : Real) ≤ smooth a b c d e := by exact_mod_cast (not_lt.mp ht)
    have hlogn : (271 / 100 : Real) < Real.log (Real.log (smooth a b c d e : Real)) :=
      loglog_tail.trans_le (Real.log_le_log (Real.log_pos (by norm_num))
        (Real.log_le_log (by norm_num) htR))
    have hr : (89 / 50 : Real) * (271 / 100) <
        Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (smooth a b c d e : Real)) :=
      mul_lt_mul exp_gamma_lower hlogn.le (by norm_num) (Real.exp_pos _).le
    exact hbound.trans (by norm_num at hr; linarith only [hr])

end D5.S3.Arith.Robin.ElevenSmooth
