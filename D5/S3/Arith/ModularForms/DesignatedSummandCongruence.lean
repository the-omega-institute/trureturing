/- GID: D5/S3/Arith/ModularForms/DesignatedSummandCongruence
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/DesignatedSummandCongruence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.NumberTheory.Padics.PadicVal.Basic]
   utility: none
   digest: The exact common dyadic divisor of all designated-summand counts in degree 3 mod 4. -/

/-
admission_basis: open-problem-resolution of the exact Conjecture 6.1 from #33469
exceptional_sharp proof_shape: content
  escape_witness: the modulo-64 period of the degree-seven coefficient and its uniform residue
result proof_shape: content
  escape_witness: the three uniform support arguments and sharpness at degrees three and seven
Escape registration: unfinished. See https://github.com/the-omega-institute/trureturing/issues/33480.

Direct frozen dependencies:
  D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators
  D5.S3.Arith.ModularForms.CubicThetaJacobi
  D5.S3.Arith.ModularForms.CubicThetaJacobiCube
  D5.S3.Arith.ModularForms.CubicThetaProductTwist
  D5.S3.Arith.ModularForms.CubicThetaTwistedColumns
  D5.S3.Arith.ModularForms.WeightedJacobiSpecialization
  D5.S3.Combinatorics.PowerSeries.LaurentSpecialization
-/

import D5.S3.Arith.ModularForms.DesignatedSummandEtaDissection
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-! Yaqubi–Mirzavaziri, arXiv:2611.05623v1, Conjecture 6.1. Degree three supplies sharpness outside the exceptional class and degree seven supplies sharpness throughout that class. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace D5.S3.Arith.ModularForms.DesignatedSummandCongruence

open _root_.PowerSeries Finset
open D5.S3.Combinatorics.PowerSeries.DilatedEulerProduct D5.S3.Combinatorics.Partitions.DesignatedSummands D5.S3.Combinatorics.PowerSeries.DyadicDilation D5.S3.Arith.ModularForms.DesignatedSummandEtaDissection

section InitialCoefficients

private def prefixEq {R : Type*} [CommRing R] (d : ℕ) (p q : PowerSeries R) : Prop :=
  ∀ n ≤ d, coeff n p = coeff n q

private theorem prefix_eq_trunc {R : Type*} [CommRing R] (d : ℕ) (p q : PowerSeries R) :
    prefixEq d p q ↔ trunc (d + 1) p = trunc (d + 1) q := by
  unfold prefixEq
  constructor
  · intro h
    ext n
    by_cases hn : n < d + 1
    · simpa only [coeff_trunc, if_pos hn] using h n (Nat.lt_succ_iff.mp hn)
    · simp only [coeff_trunc, if_neg hn]
  · intro h n hn
    simpa only [coeff_trunc, if_pos (Nat.lt_succ_of_le hn)] using
      congrArg (fun f => Polynomial.coeff f n) h

private theorem prefix_mul {R : Type*} [CommRing R] {d : ℕ} {p q u v : PowerSeries R}
    (hp : prefixEq d p q) (hu : prefixEq d u v) : prefixEq d (p * u) (q * v) := by
  apply (prefix_eq_trunc _ _ _).2
  rw [← trunc_trunc_mul_trunc p u, ← trunc_trunc_mul_trunc q v,
    (prefix_eq_trunc _ _ _).1 hp, (prefix_eq_trunc _ _ _).1 hu]

private theorem prefix_pow {R : Type*} [CommRing R] {d : ℕ} {p q : PowerSeries R}
    (h : prefixEq d p q) (k : ℕ) : prefixEq d (p ^ k) (q ^ k) := by
  apply (prefix_eq_trunc _ _ _).2
  rw [← trunc_trunc_pow p (d + 1) k, ← trunc_trunc_pow q (d + 1) k,
    (prefix_eq_trunc _ _ _).1 h]

private theorem prefix_cancel {R : Type*} [CommRing R] {d : ℕ} {p q u : PowerSeries R}
    (hu : constantCoeff u = 1) (h : prefixEq d (p * u) (q * u)) : prefixEq d p q := by
  have hInv : prefixEq d (invOfUnit u 1) (invOfUnit u 1) := fun _ _ => rfl
  simpa only [mul_assoc, mul_invOfUnit u 1 hu, mul_one] using prefix_mul h hInv

private def convolution {R : Type*} [CommRing R] (p q : ℕ → R) (n : ℕ) : R :=
  ∑ j ∈ range (n+1), p j * q (n-j)

private theorem series_convolution {R : Type*} [CommRing R] (p q : ℕ → R) :
    (PowerSeries.mk p) * (PowerSeries.mk q) = PowerSeries.mk (convolution p q) := by
  ext n
  simp [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, convolution]

private theorem le_pentagonal (k : ℤ) : k.natAbs ≤ pentagonal k := by
  have h := two_mul_natCast_pentagonal k
  by_cases hk : 0 ≤ k
  · have habs : (k.natAbs : ℤ) = k := Int.natAbs_of_nonneg hk
    by_cases hz : k = 0
    · simp [hz]
    · have hmul : 0 ≤ k * (k - 1) := mul_nonneg hk (by omega)
      exact_mod_cast (show (k.natAbs : ℤ) ≤ (pentagonal k : ℤ) by rw [habs]; nlinarith)
  · have habs : (k.natAbs : ℤ) = -k := Int.ofNat_natAbs_of_nonpos (by omega)
    have hmul : 0 ≤ (-k) * (-k - 1) := mul_nonneg (by omega) (by omega)
    exact_mod_cast (show (k.natAbs : ℤ) ≤ (pentagonal k : ℤ) by rw [habs]; nlinarith)

private theorem F_mul_den :
    (F : PowerSeries ℤ) * (euler 1 (by decide) * euler 2 (by decide) * euler 3 (by decide)) =
      euler 6 (by decide) := by
  let D : PowerSeries ℤ := euler 1 (by decide) * euler 2 (by decide) * euler 3 (by decide)
  have hu : D * invOfUnit D 1 = 1 := mul_invOfUnit D 1 (by simp [D, euler_const])
  change (euler 6 (by decide) * invOfUnit D 1) * D = _
  rw [mul_assoc, mul_comm (invOfUnit D 1), hu, mul_one]

private theorem coefficient_formula_three (k : ℕ) :
    2 * coeff 2 ((F : PowerSeries ℤ)^k) = (k : ℤ) * ((k : ℤ) + 5) ∧
    6 * coeff 3 ((F : PowerSeries ℤ)^k) = (k : ℤ) * ((k : ℤ) + 1) * ((k : ℤ) + 14) := by
  let initial (n : ℕ) : ℤ := [1, 1, 3, 5][n]!
  let pent (n : ℕ) : ℤ := [1, -1, -1, 0][n]!
  have hPent (n : ℕ) (hn : n ≤ 3) : coeff n (pentagonalSeries ℤ) = pent n := by
    have hzero {i : ℕ} (hi : i ≤ 3)
        (h : ∀ k : ℤ, -3 ≤ k → k ≤ 3 → pentagonal k ≠ i) :
        coeff i (pentagonalSeries ℤ) = 0 := by
      apply coeff_pentagonalSeries_eq_zero
      rintro ⟨k, hk⟩
      have hbound := le_pentagonal k
      rw [hk] at hbound
      exact h k (by omega) (by omega) hk
    interval_cases n
    · exact (coeff_pentagonalSeries_pentagonal ℤ 0).trans (by decide)
    · exact (coeff_pentagonalSeries_pentagonal ℤ 1).trans (by decide)
    · change coeff (pentagonal (-1)) (pentagonalSeries ℤ) = -1
      rw [coeff_pentagonalSeries_pentagonal]
      decide
    · apply hzero (i := 3) (by decide)
      intro k hl hu
      interval_cases k <;> decide
  let eulerPrefix (d n : ℕ) : ℤ := if d ∣ n then pent (n / d) else 0
  have hEuler (d : ℕ) (hd : d ≠ 0) :
      prefixEq 3 (euler d hd : PowerSeries ℤ) (PowerSeries.mk (eulerPrefix d)) := by
    intro n hn
    simp only [euler, coeff_expand, coeff_mk, eulerPrefix]
    split_ifs
    · exact hPent (n / d) ((Nat.div_le_self _ _).trans hn)
    · rfl
  have hF : prefixEq 3 (F : PowerSeries ℤ) (PowerSeries.mk initial) := by
    apply prefix_cancel (u := euler 1 (by decide) * euler 2 (by decide) * euler 3 (by decide))
    · simp [euler_const]
    rw [F_mul_den]
    have hDen := prefix_mul (prefix_mul (hEuler 1 (by decide)) (hEuler 2 (by decide)))
      (hEuler 3 (by decide))
    intro n hn
    rw [hEuler 6 (by decide) n hn, (prefix_mul (fun _ _ => rfl : prefixEq 3 (PowerSeries.mk initial)
      (PowerSeries.mk initial)) hDen) n hn]
    simp only [series_convolution, coeff_mk]
    interval_cases n <;> decide
  have hcoeff (n : ℕ) (hn : n ≤ 3) : coeff n (F : PowerSeries ℤ) = initial n := by
    rw [hF n hn, coeff_mk]
  have hc1 (j : ℕ) : coeff 1 ((F : PowerSeries ℤ)^j) = (j : ℤ) := by
    induction j with
    | zero => simp
    | succ j ih => simp [pow_succ, coeff_one_mul, ih, F_const, hcoeff 1 (by decide), initial]
  induction k with
  | zero => simp
  | succ k ih =>
    have h0 : constantCoeff ((F : PowerSeries ℤ)^k) = 1 := by simp [F_const]
    have h0' : coeff 0 ((F : PowerSeries ℤ)^k) = 1 := by simpa using h0
    have hr2 : coeff 2 ((F : PowerSeries ℤ)^(k+1)) =
        3 + (k : ℤ) + coeff 2 ((F : PowerSeries ℤ)^k) := by
      rw [pow_succ, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp [sum_range_succ, hc1, h0', hcoeff 1 (by decide), hcoeff 2 (by decide),
        hcoeff 3 (by decide), F_const, initial]
    have hr3 : coeff 3 ((F : PowerSeries ℤ)^(k+1)) =
        5 + 3*(k : ℤ) + coeff 2 ((F : PowerSeries ℤ)^k) + coeff 3 ((F : PowerSeries ℤ)^k) := by
      rw [pow_succ, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp [sum_range_succ, hc1, h0', hcoeff 1 (by decide), hcoeff 2 (by decide),
        hcoeff 3 (by decide), F_const, initial]
      ring
    push_cast
    rw [hr2, hr3]
    constructor
    · nlinarith only [ih.1]
    · linear_combination ih.2 + 3 * ih.1

end InitialCoefficients

section ProgressionDivisibility

private theorem coeff_mul_dilated_zero {R : Type*} [CommRing R] (d n : ℕ) (hd : d ≠ 0)
    (p q : PowerSeries R)
    (hq : ∀ j, j%d = n%d → coeff j q = 0) :
    coeff n (expand d hd p * q) = 0 := by
  rw [coeff_mul]
  apply sum_eq_zero
  rintro ⟨i,j⟩ hij
  have he : i+j=n := mem_antidiagonal.mp hij
  by_cases hi : d ∣ i
  · rw [hq j (by rw [←he, Nat.add_mod, Nat.mod_eq_zero_of_dvd hi, zero_add, Nat.mod_mod]), mul_zero]
  · rw [coeff_expand_of_not_dvd d hd _ hi, zero_mul]

private theorem lower_four_divides_k (p : PowerSeries ℤ) (j n : ℕ) {k : ℕ}
    (hk : 2^(j+1) ∣ k) : (2 : ℤ)^(j+1) ∣ coeff (4*n+3) (p^k) := by
  obtain ⟨t,rfl⟩ := hk
  rw [show (2 : ℤ) ^ (j+1) = ((2^(j+1) : ℕ) : ℤ) by simp only [Nat.cast_pow, Nat.cast_ofNat], ← coeff_reduce_eq_zero]
  exact (by rw [reduce_lift_mul p j 0 t]; exact coeff_expand_of_not_dvd _ _ _ (by omega))

private theorem lower_odd_k (p h : PowerSeries ℤ) (hunit : p*h=1)
    (hH : ∀ n, coeff (4*n+3) h = 0) (j n k : ℕ)
    (hk : 2^(j+2) ∣ k+1) :
    (2 : ℤ)^(j+1) ∣ coeff (4*n+3) (p^k) := by
  have hpow : p^(k+1)*h=p^k := by rw [pow_succ,mul_assoc,hunit,mul_one]
  rw [show (2 : ℤ) ^ (j+1) = ((2^(j+1) : ℕ) : ℤ) by simp only [Nat.cast_pow, Nat.cast_ofNat], ← coeff_reduce_eq_zero, ← hpow, map_mul]
  obtain ⟨t,ht⟩ := hk
  have hr := reduce_lift_mul p j 1 t
  change reduce (2^(j+1)) (p^(2^(j+2)*t)) = _ at hr
  rw [ht, hr]
  apply coeff_mul_dilated_zero
  intro i hi
  have he : i = 4*(i/4)+3 := by omega
  rw [he, reduce, coeff_map, hH, map_zero]

private theorem reduce_power_after_even_multiple (A B : PowerSeries ℤ) (j t : ℕ)
    (h : C (2 : ℤ) ∣ A-B) :
    reduce (2^(j+1)) (A^(2^j*t)) = reduce (2^(j+1)) (B^(2^j*t)) := by
  have h' : (2 : PowerSeries ℤ) ∣ A-B := by simpa only [map_ofNat] using h
  have hh := (map_mod_eq_iff (2^(j+1)) (A^(2^j)) (B^(2^j))).2
    (by simpa only [Nat.cast_pow, Nat.cast_ofNat, map_pow, map_ofNat] using
      dvd_sub_pow_of_dvd_sub (p := 2) h' j)
  change reduce (2^(j+1)) _ = reduce (2^(j+1)) _ at hh
  simpa only [pow_mul, map_pow] using congrArg (fun z => z^t) hh

private theorem lower_from_square (p E W : PowerSeries ℤ)
    (he : p^2 = expand 2 (by decide) E + 2 * PowerSeries.X * expand 2 (by decide) W)
    (hW : ∀ n, (4 : ℤ) ∣ coeff (2*n+1) W)
    (j : ℕ) (hj : j = 1 ∨ j = 2) (t n : ℕ) :
    (2 : ℤ)^(j+1) ∣ coeff (4*n+3) (p^(2*(2^j*t+1))) := by
  let B : PowerSeries ℤ := expand 2 (by decide) E
  let D : PowerSeries ℤ := PowerSeries.X * expand 2 (by decide) W
  have he' : p^2 = B + 2*D := by simpa only [B,D,mul_assoc] using he
  have hd : C (2 : ℤ) ∣ p^2 - B := by rw [he', add_sub_cancel_left, map_ofNat]; exact dvd_mul_right _ _
  have hmain : reduce (2^(j+1)) (p^(2*(2^j*t+1))) =
      reduce (2^(j+1)) (B^(2^j*t+1) + 2*(B^(2^j*t)*D)) := by
    calc
      _ = reduce (2^(j+1)) ((p^2)^(2^j*t) * p^2) := by rw [pow_mul, pow_succ (p^2)]
      _ = reduce (2^(j+1)) (B^(2^j*t) * (B+2*D)) := by
        rw [map_mul, map_mul, reduce_power_after_even_multiple _ _ j t hd, he']
      _ = _ := by congr 1; rw [pow_succ B]; ring
  rw [show (2 : ℤ) ^ (j+1) = ((2^(j+1) : ℕ) : ℤ) by simp only [Nat.cast_pow, Nat.cast_ofNat],
    ← coeff_reduce_eq_zero, hmain, map_add, map_add]
  have even_term : coeff (4*n+3) (reduce (2^(j+1)) (B^(2^j*t+1))) = 0 := by
    simp only [B, ← map_pow, reduce, map_expand]
    exact coeff_expand_of_not_dvd _ _ _ (by omega)
  rw [even_term, zero_add, coeff_reduce_eq_zero]
  simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul, pow_succ', show (2 : PowerSeries ℤ) = C (2 : ℤ) by simp,
    coeff_C_mul]
  apply mul_dvd_mul_left
  have hB : reduce (2^j) (B^(2^j*t)) =
      expand 4 (by decide) (reduce (2^j) E ^ (2^(j-1)*t)) := by
    calc
      _ = expand 2 (by decide) (reduce (2^j) (E^(2^j*t))) := by
        simp only [B, ← map_pow (expand 2 (by decide)), reduce, map_expand]
      _ = _ := by
        obtain rfl | rfl := hj
        · exact (congrArg (expand 2 (by decide)) (reduce_lift_mul E 0 0 t)).trans
            (expand_mul 2 (by decide) 2 (by decide) _).symm
        · exact (congrArg (expand 2 (by decide)) (reduce_lift_mul E 1 0 t)).trans
            (expand_mul 2 (by decide) 2 (by decide) _).symm
  rw [show (2 : ℤ)^j = ((2^j : ℕ) : ℤ) by simp only [Nat.cast_pow, Nat.cast_ofNat], ← coeff_reduce_eq_zero, map_mul, hB]
  apply coeff_mul_dilated_zero
  intro i hi
  have hi' : i % 4 = 3 := by omega
  have hX : coeff i (reduce (2^j) D) =
      if 1 ≤ i then coeff (i-1) (expand 2 (by decide) (reduce (2^j) W)) else 0 := by
    simp only [D, reduce, map_mul, map_expand, PowerSeries.map_X]
    simpa only [reduce, pow_one] using coeff_X_pow_mul' (expand 2 (by decide) (reduce (2^j) W)) 1 i
  rw [hX, ite_eq_left (by omega), coeff_expand, ite_eq_left (by omega)]
  have hi'' : (i-1)/2 = 2*(i/4)+1 := by omega
  rw [hi'', coeff_reduce_eq_zero]
  apply dvd_trans _ (hW (i/4))
  obtain rfl | rfl := hj <;> decide

end ProgressionDivisibility

local notation "p" => (F : PowerSeries ℤ)
local notation "ν" => padicValNat 2

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private noncomputable def conjectureExponent (k : ℕ) : ℕ :=
  if k % 16 = 2 then 3 else ν (markedCount k 3)

private theorem A3_formula (k : ℕ) :
    6 * markedCount k 3 = k*(k+1)*(k+14) := by
  have hc := (coefficient_formula_three k).2
  rw [← marked_count_coeff] at hc
  exact_mod_cast hc

private theorem A3_ne_zero {k : ℕ} (hk : 0 < k) : markedCount k 3 ≠ 0 := by
  intro he
  have h := A3_formula k
  rw [he, mul_zero] at h
  have hh : 0 < k*(k+1)*(k+14) := by positivity
  omega

private theorem val_exact {k e : ℕ} (hk : k ≠ 0)
    (h : 2^e ∣ k) (h' : ¬ 2^(e+1) ∣ k) :
    ν k = e := by
  rw [padicValNat_dvd_iff_le hk] at h h'
  omega

private theorem A3_valuation {k : ℕ} (hk : 0 < k) :
    1 + ν (markedCount k 3) = ν k + ν (k+1) + ν (k+14) := by
  have h := congrArg (padicValNat 2) (A3_formula k)
  rw [padicValNat.mul (by decide) (A3_ne_zero hk),
    padicValNat.mul (by positivity) (by positivity),
    padicValNat.mul hk.ne' (by positivity),
    val_exact (k := 6) (e := 1) (by decide) (by decide) (by decide)] at h
  exact h

private theorem coeff_seven_period (k : ℕ) :
    coeff 7 (reduce 16 (p^k)) = coeff 7 (reduce 16 (p^(k % 64))) := by
  have hp := reduce_lift p 3 2
  change reduce 16 (p^64) = reduce 16 (expand 8 (by decide) (p^8)) at hp
  have h0 : prefixEq 7 (reduce 16 (p^64)) 1 := by
    rw [hp, reduce, map_expand]
    intro i hi
    cases i with
    | zero =>
      have hm : constantCoeff ((PowerSeries.map (Int.castRingHom (ZMod 16))) p) = 1 := by
        rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff, F_const, map_one]
      simp [map_pow, hm]
    | succ i =>
      rw [coeff_expand_of_not_dvd 8 _ _ (by omega), coeff_one, ite_eq_right (by omega)]
  have hk : k = 64*(k/64) + k%64 := by omega
  have hsame : prefixEq 7 (reduce 16 (p^(k%64))) (reduce 16 (p^(k%64))) := fun _ _ => rfl
  have h := prefix_mul (prefix_pow h0 (k/64)) hsame
  have hh := h 7 (by decide)
  simp only [one_pow, one_mul, ← map_pow, ← pow_mul, ← map_mul, ← pow_add] at hh
  nth_rw 1 [hk]
  exact hh

theorem exceptional_sharp (k : ℕ) (hk : k % 16 = 2) :
    coeff 7 (reduce 16 (p^k)) = 8 := by
  let initial (n : ℕ) : ℤ := [1, 1, 3, 5, 10, 15, 28, 41][n]!
  let pent (n : ℕ) : ℤ := [1, -1, -1, 0, 0, 1, 0, 1][n]!
  have hPent (n : ℕ) (hn : n ≤ 7) : coeff n (pentagonalSeries ℤ) = pent n := by
    have hzero {i : ℕ} (hi : i ≤ 7)
        (h : ∀ k : ℤ, -7 ≤ k → k ≤ 7 → pentagonal k ≠ i) :
        coeff i (pentagonalSeries ℤ) = 0 := by
      apply coeff_pentagonalSeries_eq_zero
      rintro ⟨k, hk⟩
      have hbound := le_pentagonal k
      rw [hk] at hbound
      exact h k (by omega) (by omega) hk
    interval_cases n
    · exact (coeff_pentagonalSeries_pentagonal ℤ 0).trans (by decide)
    · exact (coeff_pentagonalSeries_pentagonal ℤ 1).trans (by decide)
    · change coeff (pentagonal (-1)) (pentagonalSeries ℤ) = -1
      rw [coeff_pentagonalSeries_pentagonal]
      decide
    · apply hzero (i := 3) (by decide)
      intro k hl hu
      interval_cases k <;> decide
    · apply hzero (i := 4) (by decide)
      intro k hl hu
      interval_cases k <;> decide
    · exact (coeff_pentagonalSeries_pentagonal ℤ 2).trans (by decide)
    · apply hzero (i := 6) (by decide)
      intro k hl hu
      interval_cases k <;> decide
    · change coeff (pentagonal (-2)) (pentagonalSeries ℤ) = 1
      rw [coeff_pentagonalSeries_pentagonal]
      decide
  let eulerPrefix (d n : ℕ) : ℤ := if d ∣ n then pent (n / d) else 0
  have hEuler (d : ℕ) (hd : d ≠ 0) :
      prefixEq 7 (euler d hd : PowerSeries ℤ) (PowerSeries.mk (eulerPrefix d)) := by
    intro n hn
    simp only [euler, coeff_expand, coeff_mk, eulerPrefix]
    split_ifs
    · exact hPent (n / d) ((Nat.div_le_self _ _).trans hn)
    · rfl
  have hF : prefixEq 7 (F : PowerSeries ℤ) (PowerSeries.mk initial) := by
    apply prefix_cancel (u := euler 1 (by decide) * euler 2 (by decide) * euler 3 (by decide))
    · simp [euler_const]
    rw [F_mul_den]
    have hDen := prefix_mul (prefix_mul (hEuler 1 (by decide)) (hEuler 2 (by decide)))
      (hEuler 3 (by decide))
    intro n hn
    rw [hEuler 6 (by decide) n hn, (prefix_mul (fun _ _ => rfl : prefixEq 7 (PowerSeries.mk initial)
      (PowerSeries.mk initial)) hDen) n hn]
    simp only [series_convolution, coeff_mk]
    interval_cases n <;> decide
  have hFmod : prefixEq 7 (reduce 16 p)
      (PowerSeries.mk fun n => (initial n : ZMod 16)) := by
    intro n hn
    rw [reduce, coeff_map, hF n hn, coeff_mk, coeff_mk]
    rfl
  have square (m : ℕ) (a b : ℕ → ZMod 16)
      (ha : prefixEq 7 (reduce 16 p ^ m) (PowerSeries.mk a))
      (hb : ∀ n ≤ 7, convolution a a n = b n) :
      prefixEq 7 (reduce 16 p ^ (m + m)) (PowerSeries.mk b) := by
    intro n hn
    rw [pow_add, prefix_mul ha ha n hn, series_convolution, coeff_mk, coeff_mk, hb n hn]
  let v2 (n : ℕ) : ZMod 16 := [1, 2, 7, 0, 7, 0, 11, 8][n]!
  have h2 : prefixEq 7 (reduce 16 p ^ 2) (PowerSeries.mk v2) :=
    square 1 _ v2 (by simpa only [pow_one] using hFmod) (by
      intro n hn
      interval_cases n <;> decide)
  let v4 (n : ℕ) : ZMod 16 := [1, 4, 2, 12, 15, 12, 8, 12][n]!
  have h4 : prefixEq 7 (reduce 16 p ^ 4) (PowerSeries.mk v4) :=
    square 2 v2 v4 h2 (by intro n hn; interval_cases n <;> decide)
  let v8 (n : ℕ) : ZMod 16 := [1, 8, 4, 8, 2, 0, 12, 0][n]!
  have h8 : prefixEq 7 (reduce 16 p ^ 8) (PowerSeries.mk v8) :=
    square 4 v4 v8 h4 (by intro n hn; interval_cases n <;> decide)
  let v16 (n : ℕ) : ZMod 16 := [1, 0, 8, 0, 4, 0, 8, 0][n]!
  have h16 : prefixEq 7 (reduce 16 p ^ 16) (PowerSeries.mk v16) :=
    square 8 v8 v16 h8 (by intro n hn; interval_cases n <;> decide)
  let v32 (n : ℕ) : ZMod 16 := [1, 0, 0, 0, 8, 0, 0, 0][n]!
  have h32 : prefixEq 7 (reduce 16 p ^ 32) (PowerSeries.mk v32) :=
    square 16 v16 v32 h16 (by intro n hn; interval_cases n <;> decide)
  rw [coeff_seven_period, map_pow]
  have hr : k % 64 = 2 ∨ k % 64 = 18 ∨ k % 64 = 34 ∨ k % 64 = 50 := by omega
  rcases hr with h | h | h | h
  · rw [h, h2 7 (by decide), coeff_mk]
    decide
  · rw [h, show 18 = 16 + 2 by decide, pow_add, prefix_mul h16 h2 7 (by decide),
      series_convolution, coeff_mk]
    decide
  · rw [h, show 34 = 32 + 2 by decide, pow_add, prefix_mul h32 h2 7 (by decide),
      series_convolution, coeff_mk]
    decide
  · rw [h, show 50 = (32 + 16) + 2 by decide, pow_add, pow_add _ 32 16,
      prefix_mul (prefix_mul h32 h16) h2 7 (by decide), series_convolution,
      series_convolution, coeff_mk]
    decide

private theorem full_lower (h E W : PowerSeries ℤ)
    (hunit : p*h=1) (hH : ∀ n, coeff (4*n+3) h=0)
    (hSquare : p^2 = expand 2 (by decide) E + 2 * PowerSeries.X * expand 2 (by decide) W)
    (hW : ∀ n, (4 : ℤ) ∣ coeff (2*n+1) W)
    (k : ℕ) (hk : 0 < k) (n : ℕ) :
    (2 : ℤ)^(conjectureExponent k) ∣ coeff (4*n+3) (p^k) := by
  have hv := A3_valuation hk
  have hdiv (a : ℕ) : 2 ^ (ν a) ∣ a := pow_padicValNat_dvd
  have hvzero (a : ℕ) (ha : a%2=1) : ν a = 0 :=
    padicValNat.eq_zero_of_not_dvd (by omega)
  by_cases hodd : k%2=1
  · have h14 := hvzero (k+14) (by omega)
    have h0 := hvzero k hodd
    have he : conjectureExponent k = ν (k+1)-1 := by
      unfold conjectureExponent
      rw [ite_eq_right (by omega)]
      omega
    rw [he]
    cases hr : ν (k+1)-1 with
    | zero => simp
    | succ j =>
      apply lower_odd_k p h hunit hH j n k
      have hh := hdiv (k+1)
      rw [show ν (k+1) = j+2 by omega] at hh
      exact hh
  · by_cases hfour : k%4=0
    · have h14 : ν (k+14) = 1 := val_exact (by positivity) (by norm_num; omega) (by norm_num; omega)
      have h1 := hvzero (k+1) (by omega)
      have he : conjectureExponent k = ν k := by
        unfold conjectureExponent
        rw [ite_eq_right (by omega)]
        omega
      rw [he]
      cases h : ν k with
      | zero => simp
      | succ j =>
        exact lower_four_divides_k p j n (by simpa only [h] using hdiv k)
    · have hk4 : k%4=2 := by omega
      have h0 : ν k = 1 := val_exact hk.ne' (by norm_num; omega) (by norm_num; omega)
      have h1 := hvzero (k+1) (by omega)
      by_cases h6 : k%8=6
      · have h14 : ν (k+14) = 2 := val_exact (by positivity) (by norm_num; omega) (by norm_num; omega)
        have he : conjectureExponent k = 2 := by
          unfold conjectureExponent
          rw [ite_eq_right (by omega)]
          omega
        rw [he]
        have hk' : k = 2*(2^1*(k/4)+1) := by norm_num; omega
        rw [hk']
        exact lower_from_square p E W hSquare hW 1 (Or.inl rfl) (k/4) n
      · have hk8 : k%8=2 := by omega
        have he : conjectureExponent k = 3 := by
          unfold conjectureExponent
          split_ifs with he
          · rfl
          · have h14 : ν (k+14) = 3 :=
              val_exact (by positivity) (by norm_num; omega) (by norm_num; omega)
            omega
        rw [he]
        have hk' : k = 2*(2^2*(k/8)+1) := by norm_num; omega
        rw [hk']
        exact lower_from_square p E W hSquare hW 2 (Or.inr rfl) (k/8) n

/-- Yaqubi–Mirzavaziri Conjecture 6.1 for ordered partitions with designated summands. -/
theorem result (k e : ℕ) (hk : 0 < k) :
    (∀ n : ℕ, 2 ^ e ∣ markedCount k (4 * n + 3)) ↔
      e ≤ (if k % 16 = 2 then 3 else padicValNat 2 (markedCount k 3)) := by
  change (∀ n : ℕ, 2 ^ e ∣ markedCount k (4 * n + 3)) ↔ e ≤ conjectureExponent k
  constructor
  · intro he
    unfold conjectureExponent
    split_ifs with hr
    · by_contra! hh
      have hd := (pow_dvd_pow 2 (show 4 ≤ e by omega)).trans (he 1)
      have hi : (16 : ℤ) ∣ coeff 7 (p^k) := by
        rw [← marked_count_coeff]
        exact_mod_cast hd
      have hz := (coeff_reduce_eq_zero 16 7 _).2 hi
      rw [exceptional_sharp k hr] at hz
      exact (by decide : (8 : ZMod 16) ≠ 0) hz
    · exact (padicValNat_dvd_iff_le (A3_ne_zero hk)).mp (by simpa using he 0)
  · intro he n
    have hi := (pow_dvd_pow (2 : ℤ) he).trans (full_lower H E W FH H_support F_square W_support k hk n)
    rw [← marked_count_coeff] at hi
    exact_mod_cast hi

end D5.S3.Arith.ModularForms.DesignatedSummandCongruence
