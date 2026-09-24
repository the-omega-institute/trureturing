/- GID: D5/S3/Constants/Moments/A331474HankelGeneratingFunction
   generality: I
   mirror-B: D5/B/S3/Constants/Moments/A331474HankelGeneratingFunction
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [D5/S3/Constants/Moments/A331474HankelBridge]
   utility: none
   digest: The literal A331474 Hankel determinants have the conjectured rational generating function. -/

import D5.S3.Constants.Moments.A331474HankelBridge
import Mathlib.RingTheory.PowerSeries.Inverse

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators Polynomial

namespace D5.S3.Constants.Moments.A331474HankelGeneratingFunction

open D5.S3.Constants.Moments.A331474HankelBridge

private def delta (N : Nat) : Int :=
  ∏ k : Fin N, (-1 : Int) ^ k.1

private def kernel (N : Nat) : Int :=
  ∑ k : Fin N, (-1 : Int) ^ k.1 * p k.1 * u k.1

private def w (n : Nat) : Int :=
  p (n + 1) * u n - p n * u (n + 1)

private def U (m : Nat) : Int :=
  u (2 * m)

private theorem scalar_parity :
    (∀ n, 0 < n → H n = delta n * w n) ∧
    (∀ m, p (2 * m) = 1 ∧ p (2 * m + 1) = -4 * (m + 1)) ∧
    (U 0 = 1 ∧ U 1 = 1 ∧ U 2 = 7) ∧
    (∀ m, 1 ≤ m → u (2 * m + 1) = U m - U (m + 1)) ∧
    (∀ m, 2 ≤ m → U (m + 1) = 7 * U m - U (m - 1)) ∧
    (∀ m, 1 ≤ m → H (2 * m) =
      (-1 : Int) ^ m * (U (m + 1) - (4 * (m : Int) + 5) * U m)) ∧
    (∀ m, 1 ≤ m → H (2 * m + 1) =
      (-1 : Int) ^ m * (U m + (4 * (m : Int) + 3) * U (m + 1))) ∧
    (H 0 = 1 ∧ H 1 = 3 ∧ H 2 = 2 ∧ H 3 = -50 ∧ H 4 = -43 ∧
      H 5 = 535 ∧ H 6 = 487 ∧ H 7 = -4983 ∧ H 8 = -4654 ∧ H 9 = 43174) ∧
    (∀ n, 8 ≤ n → H n + 14 * H (n - 2) + 51 * H (n - 4) +
      14 * H (n - 6) + H (n - 8) = 0) := by
  rcases (literal_hankel_eq_signed_kernel 0).2 with
    ⟨hp0, hp1, hpRec, hu0, hu1, hu2, huRec⟩
  have hbridge (n : Nat) : H n = delta (n + 1) * kernel (n + 1) := by
    simpa [delta, kernel] using (literal_hankel_eq_signed_kernel n).1
  have hdelta (N : Nat) : delta (N + 1) = delta N * (-1 : Int) ^ N := by
    simp [delta, Fin.prod_univ_castSucc]
  have hkernel (N : Nat) : kernel (N + 1) =
      kernel N + (-1 : Int) ^ N * p N * u N := by
    simp [kernel, Fin.sum_univ_castSucc]
  have hwstep (n : Nat) (hn : 1 ≤ n) :
      w (n + 1) = -w n + p (n + 1) * u (n + 1) := by
    rw [w, w, hpRec n, huRec (n + 1) (by omega)]
    rw [show n + 1 - 1 = n by omega]
    ring
  have hp2 : p 2 = 1 := by
    rw [show 2 = 0 + 2 by omega, hpRec]
    norm_num [a, hp0, hp1]
  have hkw (n : Nat) (hn : 1 ≤ n) : kernel (n + 1) = (-1 : Int) ^ n * w n := by
    induction n, hn using Nat.le_induction with
    | base =>
        norm_num [kernel, w, Fin.sum_univ_castSucc, hp0, hp1, hp2, hu0, hu1, hu2]
    | succ n hn ih =>
        rw [hkernel, ih, hwstep n hn]
        rw [pow_succ]
        ring
  have hH (n : Nat) (hn : 0 < n) : H n = delta n * w n := by
    rw [hbridge, hdelta, hkw n hn]
    have hs : ((-1 : Int) ^ n) ^ 2 = 1 := by
      rw [← pow_mul]
      simp
    calc
      delta n * (-1 : Int) ^ n * ((-1 : Int) ^ n * w n) =
          delta n * (((-1 : Int) ^ n) ^ 2) * w n := by ring
      _ = delta n * w n := by rw [hs]; ring
  have hpParity (m : Nat) :
      p (2 * m) = 1 ∧ p (2 * m + 1) = -4 * (m + 1) := by
    induction m with
    | zero => norm_num [hp0, hp1]
    | succ m ih =>
        have hEven : p (2 * (m + 1)) = 1 := by
          rw [show 2 * (m + 1) = (2 * m) + 2 by omega, hpRec]
          simp [a, ih.1, ih.2]
        constructor
        · exact hEven
        · rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega, hpRec]
          have heven : (2 * m + 2) % 2 = 0 := by omega
          rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega, hEven]
          simp [a, heven, ih.2]
          ring
  have hU0 : U 0 = 1 := by simpa [U] using hu0
  have hU1 : U 1 = 1 := by simpa [U] using hu2
  have hu3 : u 3 = -6 := by
    rw [show 3 = 2 + 1 by omega, huRec 2 (by omega)]
    simp [a, hu1, hu2]
  have hU2 : U 2 = 7 := by
    change u 4 = 7
    rw [show 4 = 3 + 1 by omega, huRec 3 (by omega)]
    simp [a, hu2, hu3]
  have hOdd (m : Nat) (hm : 1 ≤ m) : u (2 * m + 1) = U m - U (m + 1) := by
    rw [U, U, show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
      huRec (2 * m + 1) (by omega)]
    simp [a]
  have hURec (m : Nat) (hm : 2 ≤ m) : U (m + 1) = 7 * U m - U (m - 1) := by
    have he := huRec (2 * m) (by omega)
    rw [hOdd m (by omega), show 2 * m - 1 = 2 * (m - 1) + 1 by omega,
      hOdd (m - 1) (by omega)] at he
    simp [a, U] at he
    rw [show m - 1 + 1 = m by omega] at he
    change u (2 * (m + 1)) = 7 * u (2 * m) - u (2 * (m - 1))
    linarith
  have hDeltaParity (m : Nat) :
      delta (2 * m) = (-1 : Int) ^ m ∧ delta (2 * m + 1) = (-1 : Int) ^ m := by
    induction m with
    | zero => simp [delta]
    | succ m ih =>
        have hEvenDelta : delta (2 * (m + 1)) = (-1 : Int) ^ (m + 1) := by
          rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, hdelta, ih.2]
          simp [pow_succ]
        constructor
        · exact hEvenDelta
        · rw [hdelta, hEvenDelta]
          simp
  have hEvenH (m : Nat) (hm : 1 ≤ m) : H (2 * m) =
      (-1 : Int) ^ m * (U (m + 1) - (4 * (m : Int) + 5) * U m) := by
    rw [hH (2 * m) (by omega), (hDeltaParity m).1]
    simp only [w]
    rw [(hpParity m).2, (hpParity m).1, hOdd m hm]
    simp only [U]
    ring
  have hOddH (m : Nat) (hm : 1 ≤ m) : H (2 * m + 1) =
      (-1 : Int) ^ m * (U m + (4 * (m : Int) + 3) * U (m + 1)) := by
    rw [hH (2 * m + 1) (by omega), (hDeltaParity m).2]
    simp only [w]
    rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega,
      (hpParity (m + 1)).1, (hpParity m).2, hOdd m hm]
    simp only [U]
    ring
  have hU3 : U 3 = 48 := by
    rw [show 3 = 2 + 1 by omega, hURec 2 (by omega)]
    norm_num [hU0, hU1, hU2]
  have hU4 : U 4 = 329 := by
    rw [show 4 = 3 + 1 by omega, hURec 3 (by omega)]
    norm_num [hU1, hU2, hU3]
  have hU5 : U 5 = 2255 := by
    rw [show 5 = 4 + 1 by omega, hURec 4 (by omega)]
    norm_num [hU2, hU3, hU4]
  have hH0 : H 0 = 1 := by
    have ht := (literal_hankel_eq_signed_kernel 0).1
    norm_num [delta, kernel, hp0, hu0] at ht ⊢
    exact ht
  have hH1 : H 1 = 3 := by
    rw [hH 1 (by omega)]
    norm_num [delta, w, hp1, hp2, hu1, hu2]
  have hH2 : H 2 = 2 := by
    simpa [hU1, hU2] using hEvenH 1 (by omega)
  have hH3 : H 3 = -50 := by
    simpa [hU1, hU2] using hOddH 1 (by omega)
  have hH4 : H 4 = -43 := by
    simpa [hU2, hU3] using hEvenH 2 (by omega)
  have hH5 : H 5 = 535 := by
    simpa [hU2, hU3] using hOddH 2 (by omega)
  have hH6 : H 6 = 487 := by
    simpa [hU3, hU4] using hEvenH 3 (by omega)
  have hH7 : H 7 = -4983 := by
    simpa [hU3, hU4] using hOddH 3 (by omega)
  have hH8 : H 8 = -4654 := by
    simpa [hU4, hU5] using hEvenH 4 (by omega)
  have hH9 : H 9 = 43174 := by
    simpa [hU4, hU5] using hOddH 4 (by omega)
  have hEvenAnn (m : Nat) (hm : 5 ≤ m) :
      H (2 * m) + 14 * H (2 * m - 2) + 51 * H (2 * m - 4) +
        14 * H (2 * m - 6) + H (2 * m - 8) = 0 := by
    rw [hEvenH m (by omega)]
    rw [show 2 * m - 2 = 2 * (m - 1) by omega, hEvenH (m - 1) (by omega)]
    rw [show 2 * m - 4 = 2 * (m - 2) by omega, hEvenH (m - 2) (by omega)]
    rw [show 2 * m - 6 = 2 * (m - 3) by omega, hEvenH (m - 3) (by omega)]
    rw [show 2 * m - 8 = 2 * (m - 4) by omega, hEvenH (m - 4) (by omega)]
    rw [show m - 1 + 1 = m by omega, show m - 2 + 1 = m - 1 by omega,
      show m - 3 + 1 = m - 2 by omega, show m - 4 + 1 = m - 3 by omega]
    have hs1 : (-1 : Int) ^ (m - 1) = -(-1 : Int) ^ m := by
      have ht := pow_add (-1 : Int) (m - 1) 1
      norm_num at ht
      rw [show m - 1 + 1 = m by omega] at ht
      linarith
    have hs2 : (-1 : Int) ^ (m - 2) = (-1 : Int) ^ m := by
      have ht := pow_add (-1 : Int) (m - 2) 2
      norm_num at ht
      rw [show m - 2 + 2 = m by omega] at ht
      linarith
    have hs3 : (-1 : Int) ^ (m - 3) = -(-1 : Int) ^ m := by
      have ht := pow_add (-1 : Int) (m - 3) 3
      norm_num at ht
      rw [show m - 3 + 3 = m by omega] at ht
      linarith
    have hs4 : (-1 : Int) ^ (m - 4) = (-1 : Int) ^ m := by
      have ht := pow_add (-1 : Int) (m - 4) 4
      norm_num at ht
      rw [show m - 4 + 4 = m by omega] at ht
      linarith
    rw [hs1, hs2, hs3, hs4]
    have hc1 : ((m - 1 : Nat) : Int) = (m : Int) - 1 := by omega
    have hc2 : ((m - 2 : Nat) : Int) = (m : Int) - 2 := by omega
    have hc3 : ((m - 3 : Nat) : Int) = (m : Int) - 3 := by omega
    have hc4 : ((m - 4 : Nat) : Int) = (m : Int) - 4 := by omega
    rw [hc1, hc2, hc3, hc4]
    have hr1 := hURec (m - 3) (by omega)
    have hr2 := hURec (m - 2) (by omega)
    have hr3 := hURec (m - 1) (by omega)
    have hr4 := hURec m (by omega)
    rw [show m - 3 + 1 = m - 2 by omega,
      show m - 3 - 1 = m - 4 by omega] at hr1
    rw [show m - 2 + 1 = m - 1 by omega,
      show m - 2 - 1 = m - 3 by omega] at hr2
    rw [show m - 1 + 1 = m by omega,
      show m - 1 - 1 = m - 2 by omega] at hr3
    rw [hr4, hr3, hr2, hr1]
    ring
  have hOddAnn (m : Nat) (hm : 5 ≤ m) :
      H (2 * m + 1) + 14 * H (2 * m - 1) + 51 * H (2 * m - 3) +
        14 * H (2 * m - 5) + H (2 * m - 7) = 0 := by
    rw [hOddH m (by omega)]
    rw [show 2 * m - 1 = 2 * (m - 1) + 1 by omega, hOddH (m - 1) (by omega)]
    rw [show 2 * m - 3 = 2 * (m - 2) + 1 by omega, hOddH (m - 2) (by omega)]
    rw [show 2 * m - 5 = 2 * (m - 3) + 1 by omega, hOddH (m - 3) (by omega)]
    rw [show 2 * m - 7 = 2 * (m - 4) + 1 by omega, hOddH (m - 4) (by omega)]
    rw [show m - 1 + 1 = m by omega, show m - 2 + 1 = m - 1 by omega,
      show m - 3 + 1 = m - 2 by omega, show m - 4 + 1 = m - 3 by omega]
    have hs1 : (-1 : Int) ^ (m - 1) = -(-1 : Int) ^ m := by
      have ht := pow_add (-1 : Int) (m - 1) 1
      norm_num at ht
      rw [show m - 1 + 1 = m by omega] at ht
      linarith
    have hs2 : (-1 : Int) ^ (m - 2) = (-1 : Int) ^ m := by
      have ht := pow_add (-1 : Int) (m - 2) 2
      norm_num at ht
      rw [show m - 2 + 2 = m by omega] at ht
      linarith
    have hs3 : (-1 : Int) ^ (m - 3) = -(-1 : Int) ^ m := by
      have ht := pow_add (-1 : Int) (m - 3) 3
      norm_num at ht
      rw [show m - 3 + 3 = m by omega] at ht
      linarith
    have hs4 : (-1 : Int) ^ (m - 4) = (-1 : Int) ^ m := by
      have ht := pow_add (-1 : Int) (m - 4) 4
      norm_num at ht
      rw [show m - 4 + 4 = m by omega] at ht
      linarith
    rw [hs1, hs2, hs3, hs4]
    have hc1 : ((m - 1 : Nat) : Int) = (m : Int) - 1 := by omega
    have hc2 : ((m - 2 : Nat) : Int) = (m : Int) - 2 := by omega
    have hc3 : ((m - 3 : Nat) : Int) = (m : Int) - 3 := by omega
    have hc4 : ((m - 4 : Nat) : Int) = (m : Int) - 4 := by omega
    rw [hc1, hc2, hc3, hc4]
    have hr1 := hURec (m - 3) (by omega)
    have hr2 := hURec (m - 2) (by omega)
    have hr3 := hURec (m - 1) (by omega)
    have hr4 := hURec m (by omega)
    rw [show m - 3 + 1 = m - 2 by omega,
      show m - 3 - 1 = m - 4 by omega] at hr1
    rw [show m - 2 + 1 = m - 1 by omega,
      show m - 2 - 1 = m - 3 by omega] at hr2
    rw [show m - 1 + 1 = m by omega,
      show m - 1 - 1 = m - 2 by omega] at hr3
    rw [hr4, hr3, hr2, hr1]
    ring
  have hRec (n : Nat) (hn : 8 ≤ n) :
      H n + 14 * H (n - 2) + 51 * H (n - 4) +
        14 * H (n - 6) + H (n - 8) = 0 := by
    rcases Nat.even_or_odd' n with ⟨m, hm | hm⟩
    · subst n
      by_cases hb : m = 4
      · subst m
        norm_num [hH0, hH2, hH4, hH6, hH8]
      · exact hEvenAnn m (by omega)
    · subst n
      by_cases hb : m = 4
      · subst m
        norm_num [hH1, hH3, hH5, hH7, hH9]
      · exact hOddAnn m (by omega)
  exact ⟨hH, hpParity, ⟨hU0, hU1, hU2⟩, hOdd, hURec, hEvenH, hOddH,
    ⟨hH0, hH1, hH2, hH3, hH4, hH5, hH6, hH7, hH8, hH9⟩, hRec⟩

private theorem determinant_series_coefficient (n : Nat) :
    PowerSeries.coeff n
        (((1 + 7 * PowerSeries.X ^ 2 + PowerSeries.X ^ 4) ^ 2) * PowerSeries.mk H) =
      PowerSeries.coeff n
        (1 + 3 * PowerSeries.X + 16 * PowerSeries.X ^ 2 - 8 * PowerSeries.X ^ 3 +
          36 * PowerSeries.X ^ 4 - 12 * PowerSeries.X ^ 5 + PowerSeries.X ^ 6 -
          PowerSeries.X ^ 7) := by
  let F : PowerSeries Int := PowerSeries.mk H
  let D : PowerSeries Int :=
    (1 + 7 * PowerSeries.X ^ 2 + PowerSeries.X ^ 4) ^ 2
  let N : PowerSeries Int :=
    1 + 3 * PowerSeries.X + 16 * PowerSeries.X ^ 2 - 8 * PowerSeries.X ^ 3 +
      36 * PowerSeries.X ^ 4 - 12 * PowerSeries.X ^ 5 + PowerSeries.X ^ 6 -
      PowerSeries.X ^ 7
  change PowerSeries.coeff n (D * F) = PowerSeries.coeff n N
  rcases scalar_parity with ⟨_, _, _, _, _, _, _, hvalues, hrec⟩
  rcases hvalues with ⟨hH0, hH1, hH2, hH3, hH4, hH5, hH6, hH7, hH8, hH9⟩
  have hD : D = 1 + PowerSeries.C 14 * PowerSeries.X ^ 2 +
      PowerSeries.C 51 * PowerSeries.X ^ 4 +
      PowerSeries.C 14 * PowerSeries.X ^ 6 + PowerSeries.X ^ 8 := by
    have hC14 : PowerSeries.C (14 : Int) = (14 : PowerSeries Int) := by norm_num
    have hC51 : PowerSeries.C (51 : Int) = (51 : PowerSeries Int) := by norm_num
    dsimp [D]
    rw [hC14, hC51]
    ring
  have hcoeff (n : Nat) : PowerSeries.coeff n (D * F) =
      H n + (if 2 ≤ n then 14 * H (n - 2) else 0) +
        (if 4 ≤ n then 51 * H (n - 4) else 0) +
        (if 6 ≤ n then 14 * H (n - 6) else 0) +
        (if 8 ≤ n then H (n - 8) else 0) := by
    rw [hD]
    simp only [add_mul, map_add, one_mul, mul_assoc, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_X_pow_mul', F, PowerSeries.coeff_mk]
    simp only [mul_ite, mul_zero]
  have hNcoeff (n : Nat) : PowerSeries.coeff n N =
      (if n = 0 then 1 else 0) + (if n = 1 then 3 else 0) +
        (if n = 2 then 16 else 0) - (if n = 3 then 8 else 0) +
        (if n = 4 then 36 else 0) - (if n = 5 then 12 else 0) +
        (if n = 6 then 1 else 0) - (if n = 7 then 1 else 0) := by
    have hC3 : (3 : PowerSeries Int) = PowerSeries.C 3 := by norm_num
    have hC8 : (8 : PowerSeries Int) = PowerSeries.C 8 := by norm_num
    have hC12 : (12 : PowerSeries Int) = PowerSeries.C 12 := by norm_num
    have hC16 : (16 : PowerSeries Int) = PowerSeries.C 16 := by norm_num
    have hC36 : (36 : PowerSeries Int) = PowerSeries.C 36 := by norm_num
    dsimp [N]
    rw [hC3, hC8, hC12, hC16, hC36,
      show PowerSeries.C (3 : Int) * PowerSeries.X =
        PowerSeries.C 3 * PowerSeries.X ^ 1 by simp]
    simp only [map_add, map_sub, PowerSeries.coeff_one,
      PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_X_pow]
  rw [hcoeff, hNcoeff]
  by_cases hn : 8 ≤ n
  · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos hn,
      hrec n hn]
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    have hn2 : n ≠ 2 := by omega
    have hn3 : n ≠ 3 := by omega
    have hn4 : n ≠ 4 := by omega
    have hn5 : n ≠ 5 := by omega
    have hn6 : n ≠ 6 := by omega
    have hn7 : n ≠ 7 := by omega
    simp [hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7]
  · have hnlt : n < 8 := by omega
    interval_cases n <;>
      norm_num [hH0, hH1, hH2, hH3, hH4, hH5, hH6, hH7]

/-- The complete literal A331474 Hankel determinant generating function. -/
theorem a331474_hankel_generating_function :
    PowerSeries.mk H =
      (1 + 3 * PowerSeries.X + 16 * PowerSeries.X ^ 2 - 8 * PowerSeries.X ^ 3 +
          36 * PowerSeries.X ^ 4 - 12 * PowerSeries.X ^ 5 + PowerSeries.X ^ 6 -
          PowerSeries.X ^ 7) *
        PowerSeries.invOfUnit
          ((1 + 7 * PowerSeries.X ^ 2 + PowerSeries.X ^ 4) ^ 2) 1 := by
  let F : PowerSeries Int := PowerSeries.mk H
  let D : PowerSeries Int :=
    (1 + 7 * PowerSeries.X ^ 2 + PowerSeries.X ^ 4) ^ 2
  let N : PowerSeries Int :=
    1 + 3 * PowerSeries.X + 16 * PowerSeries.X ^ 2 - 8 * PowerSeries.X ^ 3 +
      36 * PowerSeries.X ^ 4 - 12 * PowerSeries.X ^ 5 + PowerSeries.X ^ 6 -
      PowerSeries.X ^ 7
  change F = N * PowerSeries.invOfUnit D 1
  have hproduct : D * F = N := by
    ext n
    simpa [D, F, N] using determinant_series_coefficient n
  have hconstant : PowerSeries.constantCoeff D = (1 : Int) := by
    simp [D]
  calc
    F = 1 * F := by rw [one_mul]
    _ = (PowerSeries.invOfUnit D 1 * D) * F := by
      rw [PowerSeries.invOfUnit_mul D 1 hconstant]
    _ = PowerSeries.invOfUnit D 1 * (D * F) := by rw [mul_assoc]
    _ = PowerSeries.invOfUnit D 1 * N := by rw [hproduct]
    _ = N * PowerSeries.invOfUnit D 1 := by rw [mul_comm]

end D5.S3.Constants.Moments.A331474HankelGeneratingFunction
