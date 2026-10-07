/- GID: D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedGolden
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedGolden
   mirror-E: none(waiver:golden-three-state-fraction)
   anchors: [mathlib/module/Mathlib.RingTheory.Henselian]
   utility: none
   digest: A three-state quadratic cycle constructs the golden continuants and their errors. -/

import Mathlib.RingTheory.Henselian
import D5.S3.Combinatorics.MetallicHankel.MetallicHankelData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MetallicHankel.MetallicHankelUnboundedGolden

open PowerSeries

set_option maxHeartbeats 4000000 in
/-- The golden three-state cycle gives integral continuants at every normal index. -/
theorem golden_approximation
    (k s : ℕ → ℕ) (v h : ℕ → ℤ) (D Q N : ℕ → PowerSeries ℤ)
    (data : ∀ p, k p = (if p % 3 = 2 then 1 else 0) ∧
      v p = (if p = 0 then 1 else if p % 3 = 1 then 1 else -1) ∧
      D p = (if p % 3 = 2 then 1 + X - X ^ 2 else 1 + X))
    (s_zero : s 0 = 0) (s_step : ∀ p, s (p + 1) = s p + k p + 1)
    (h_zero : h 0 = v 0) (h_step : ∀ p, h (p + 1) = h p * v (p + 1))
    (q_zero : Q 0 = 1) (q_one : Q 1 = D 0)
    (n_zero : N 0 = 0) (n_one : N 1 = C (v 0) * X ^ k 0)
    (q_step : ∀ p, Q (p + 2) = D (p + 1) * Q (p + 1) -
      C (v (p + 1)) * X ^ (k p + k (p + 1) + 2) * Q p)
    (n_step : ∀ p, N (p + 2) = D (p + 1) * N (p + 1) -
      C (v (p + 1)) * X ^ (k p + k (p + 1) + 2) * N p) :
    ∃ F : ℕ → PowerSeries ℤ,
      X ^ 3 * F 0 ^ 2 + (1 + X - X ^ 2) * F 0 = 1 ∧
      (∀ p, constantCoeff (Q p) = 1 ∧
        (∀ r, s p < r → coeff r (Q p) = 0) ∧
        (∀ r, s p ≤ r → coeff r (N p) = 0)) ∧
      ∀ p, ∃ R : PowerSeries ℤ,
        Q p * F 0 - N p = X ^ (2 * s p + k p) * R ∧ constantCoeff R = h p := by
  classical
  have quadratic_solution (A B C : PowerSeries ℤ) (hB : constantCoeff B = 1) :
      ∃! F : PowerSeries ℤ, PowerSeries.X * C * F ^ 2 + B * F = A := by
    classical
    let I : Ideal (PowerSeries ℤ) := Ideal.span {PowerSeries.X}
    let f : Polynomial (PowerSeries ℤ) :=
      Polynomial.X ^ 2 - Polynomial.C B * Polynomial.X -
        Polynomial.C (PowerSeries.X * C * A)
    have fm : f.Monic := by
      dsimp [f]
      apply Polynomial.Monic.sub_of_left
      · apply Polynomial.Monic.sub_of_left
        · exact Polynomial.monic_X_pow 2
        · apply lt_of_le_of_lt (Polynomial.degree_C_mul_X_le B)
          norm_num
      · apply lt_of_le_of_lt (Polynomial.degree_C_le)
        rw [Polynomial.degree_sub_eq_left_of_degree_lt
          (lt_of_le_of_lt (Polynomial.degree_C_mul_X_le B) (by norm_num))]
        norm_num
    have fi : f.eval 1 ∈ I := by
      rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
      simp [f, hB]
    have fd : IsUnit (Ideal.Quotient.mk I (f.derivative.eval 1)) := by
      apply IsUnit.map
      rw [PowerSeries.isUnit_iff_constantCoeff]
      have hc : constantCoeff (f.derivative.eval 1) = 1 := by simp [f,hB]
      rw [hc]
      exact isUnit_one
    obtain ⟨U, hU, hUI⟩ := HenselianRing.is_henselian f fm 1 fi fd
    have hU0 : constantCoeff U = 1 := by
      rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, map_sub, map_one] at hUI
      exact sub_eq_zero.mp hUI
    let V := PowerSeries.invOfUnit U (1 : ℤˣ)
    have hUV : U * V = 1 := PowerSeries.mul_invOfUnit U 1 (by simpa using hU0)
    have root : U ^ 2 - B * U - PowerSeries.X * C * A = 0 := by
      simpa [f, Polynomial.IsRoot] using hU
    let F := A * V
    have hF : PowerSeries.X * C * F ^ 2 + B * F = A := by
      dsimp [F]
      linear_combination -A*V^2*root + (A*(U*V+1)-B*A*V)*hUV
    refine ⟨F,hF,?_⟩
    intro G hG
    have hu : IsUnit (B + PowerSeries.X*C*(G+F)) := by
      rw [PowerSeries.isUnit_iff_constantCoeff]
      simp [hB]
    apply hu.mul_left_injective
    linear_combination hG-hF
  let next (z : ℕ) := (z + 1) % 3
  let A (z : ℕ) : PowerSeries ℤ := if z = 0 then 1 else if z = 1 then -1 else X
  let B (z : ℕ) : PowerSeries ℤ := if z = 1 then 1 + X + X ^ 2 else 1 + X - X ^ 2
  let C₀ (z : ℕ) : PowerSeries ℤ := if z = 0 then -X ^ 2 else -X
  let kd (z : ℕ) : ℕ := if z = 2 then 1 else 0
  let bd (z : ℕ) : ℤ := if z = 1 then 1 else -1
  let Dd (z : ℕ) : PowerSeries ℤ := if z = 2 then 1 + X - X ^ 2 else 1 + X
  have roots (z : ℕ) : ∃! U : PowerSeries ℤ, X * C₀ z * U ^ 2 + B z * U = -A z :=
    quadratic_solution _ _ _ (by simp [B]; split_ifs <;> simp)
  let Fs (z : ℕ) := Classical.choose (roots z)
  have root_eq (z : ℕ) : X * C₀ z * Fs z ^ 2 + B z * Fs z = -A z :=
    (Classical.choose_spec (roots z)).1
  let K (z : ℕ) := Dd z - X ^ (kd z + 2) * Fs (next z)
  let J (z : ℕ) := invOfUnit (K z) 1
  let Gs (z : ℕ) := C (bd z) * J z
  have hcycle (z : ℕ) (hz : z < 3) :
      Fs z = X ^ kd z * Gs z ∧ constantCoeff (Gs z) = bd z ∧
      Dd z * Fs z - C (bd z) * X ^ kd z =
        X ^ (kd z + 2) * Fs (next z) * Fs z := by
    have hK0 : constantCoeff (K z) = 1 := by simp [K, Dd]; split_ifs <;> simp
    have hKI : K z * J z = 1 := mul_invOfUnit (K z) 1 (by simpa using hK0)
    let U := C (bd z) * X ^ kd z * J z
    have hUK : U * K z = C (bd z) * X ^ kd z := by
      dsimp [U]
      calc
        _ = C (bd z) * X ^ kd z * (K z * J z) := by ring
        _ = _ := by rw [hKI, mul_one]
    have hr := root_eq (next z)
    have hraw : A z * K z ^ 2 + B z * (C (bd z) * X ^ kd z) * K z +
        X * C₀ z * (C (bd z) * X ^ kd z) ^ 2 = 0 := by
      have he : A (next z) + B (next z) * Fs (next z) +
          X * C₀ (next z) * Fs (next z) ^ 2 = 0 := by linear_combination hr
      obtain rfl | rfl | rfl : z = 0 ∨ z = 1 ∨ z = 2 := by omega
      · have hn : next 0 = 1 := by norm_num [next]
        simp only [hn] at he ⊢
        norm_num [A, B, C₀, bd, kd, K, Dd, hn] at he ⊢
        linear_combination -X ^ 2 * he
      · have hn : next 1 = 2 := by norm_num [next]
        simp only [hn] at he ⊢
        norm_num [A, B, C₀, bd, kd, K, Dd, hn] at he ⊢
        linear_combination X ^ 2 * he
      · have hn : next 2 = 0 := by norm_num [next]
        simp only [hn] at he ⊢
        norm_num [A, B, C₀, bd, kd, K, Dd, hn] at he ⊢
        linear_combination -X ^ 4 * he
    have hUroot : X * C₀ z * U ^ 2 + B z * U = -A z := by
      have he : K z ^ 2 * (X * C₀ z * U ^ 2 + B z * U + A z) = 0 := by
        calc
          _ = A z * K z ^ 2 + B z * (U * K z) * K z +
              X * C₀ z * (U * K z) ^ 2 := by ring
          _ = 0 := by rw [hUK]; exact hraw
      have hu : IsUnit (K z) := by
        rw [isUnit_iff_constantCoeff, hK0]
        exact isUnit_one
      have hh := (hu.pow 2).mul_right_injective
        (show K z ^ 2 * (X * C₀ z * U ^ 2 + B z * U + A z) = K z ^ 2 * 0 by
          simpa using he)
      linear_combination hh
    have hU : U = Fs z := (Classical.choose_spec (roots z)).2 U hUroot
    refine ⟨?_, ?_, ?_⟩
    · rw [← hU]
      dsimp [U, Gs]
      ring
    · simp [Gs, J]
    · have he : Fs z * K z = C (bd z) * X ^ kd z := by rw [← hU]; exact hUK
      dsimp [K] at he
      linear_combination he
  have d_zero (p : ℕ) : constantCoeff (D p) = 1 := by
    rw [(data p).2.2]
    split_ifs <;> simp
  have d_support (p r : ℕ) (hr : k p + 1 < r) : coeff r (D p) = 0 := by
    rw [(data p).1] at hr
    rw [(data p).2.2]
    split_ifs with hp
    · simp only [hp, if_true] at hr
      simp [coeff_X, coeff_X_pow, show r ≠ 0 by omega, show r ≠ 1 by omega,
        show r ≠ 2 by omega]
    · simp only [hp, if_false] at hr
      simp [coeff_X, show r ≠ 0 by omega, show r ≠ 1 by omega]
  have approximation
      (k s : ℕ → ℕ) (v h : ℕ → ℤ)
      (D F G Q N : ℕ → PowerSeries ℤ)
      (s_zero : s 0 = 0) (s_step : ∀ p, s (p + 1) = s p + k p + 1)
      (h_zero : h 0 = v 0) (h_step : ∀ p, h (p + 1) = h p * v (p + 1))
      (tail : ∀ p, F p = X ^ k p * G p)
      (leading : ∀ p, constantCoeff (G p) = v p)
      (transition : ∀ p, D p * F p - C (v p) * X ^ k p =
        X ^ (k p + 2) * F (p + 1) * F p)
      (q_zero : Q 0 = 1) (q_one : Q 1 = D 0)
      (n_zero : N 0 = 0) (n_one : N 1 = C (v 0) * X ^ k 0)
      (q_step : ∀ p, Q (p + 2) = D (p + 1) * Q (p + 1) -
        C (v (p + 1)) * X ^ (k p + k (p + 1) + 2) * Q p)
      (n_step : ∀ p, N (p + 2) = D (p + 1) * N (p + 1) -
        C (v (p + 1)) * X ^ (k p + k (p + 1) + 2) * N p) :
      ∀ p, ∃ R : PowerSeries ℤ,
        Q p * F 0 - N p = X ^ (2 * s p + k p) * R ∧ constantCoeff R = h p := by
    have error_step : ∀ p,
        Q (p + 1) * F 0 - N (p + 1) =
          X ^ (k p + 2) * F (p + 1) * (Q p * F 0 - N p) := by
      intro p
      induction p with
      | zero =>
        simpa only [Nat.zero_add, q_zero, q_one, n_zero, n_one, one_mul, sub_zero]
          using transition 0
      | succ p ih =>
        rw [show p + 1 + 1 = p + 2 by omega, q_step, n_step]
        have tr := transition (p + 1)
        calc
          (D (p + 1) * Q (p + 1) -
              C (v (p + 1)) * X ^ (k p + k (p + 1) + 2) * Q p) * F 0 -
              (D (p + 1) * N (p + 1) -
                C (v (p + 1)) * X ^ (k p + k (p + 1) + 2) * N p) =
              D (p + 1) * (Q (p + 1) * F 0 - N (p + 1)) -
                C (v (p + 1)) * X ^ (k p + k (p + 1) + 2) *
                  (Q p * F 0 - N p) := by ring
          _ = X ^ (k p + 2) *
              (D (p + 1) * F (p + 1) - C (v (p + 1)) * X ^ k (p + 1)) *
                (Q p * F 0 - N p) := by
            rw [ih, show k p + k (p + 1) + 2 = k p + 2 + k (p + 1) by omega]
            rw [pow_add]
            ring
          _ = X ^ (k (p + 1) + 2) * F (p + 2) *
              (Q (p + 1) * F 0 - N (p + 1)) := by
            rw [tr, ih]
            ring
    intro p
    induction p with
    | zero =>
      refine ⟨G 0, ?_, ?_⟩
      · simpa only [q_zero, n_zero, one_mul, sub_zero, s_zero, mul_zero, zero_add]
          using tail 0
      · rw [leading, h_zero]
    | succ p ih =>
      obtain ⟨R, hR, hc⟩ := ih
      refine ⟨G (p + 1) * R, ?_, ?_⟩
      · rw [error_step, hR, tail, s_step]
        have he : 2 * (s p + k p + 1) + k (p + 1) =
            (k p + 2) + k (p + 1) + (2 * s p + k p) := by omega
        rw [he, pow_add, pow_add]
        ring
      · rw [map_mul, leading, hc, h_step]
        ring
  have bounds : ∀ p, constantCoeff (Q p) = 1 ∧
        (∀ r, s p < r → coeff r (Q p) = 0) ∧
        (∀ r, s p ≤ r → coeff r (N p) = 0) := by
    classical
    have convolution (U V : PowerSeries ℤ) (r : ℕ) :
        coeff r (U * V) = ∑ x ∈ Finset.antidiagonal r, coeff x.1 U * coeff x.2 V :=
      coeff_mul r U V
    intro p
    induction p using Nat.strong_induction_on with
    | h p ih =>
      cases p with
      | zero =>
        refine ⟨by simp [q_zero], ?_, ?_⟩
        · intro r hr; simp [q_zero, s_zero] at *; omega
        · intro r hr; simp [n_zero]
      | succ p =>
        cases p with
        | zero =>
          refine ⟨by simp [q_one, d_zero], ?_, ?_⟩
          · intro r hr
            rw [q_one]
            exact d_support 0 r (by rw [s_step, s_zero] at hr; omega)
          · intro r hr
            rw [n_one]
            simp only [coeff_C_mul_X_pow]
            rw [if_neg (by rw [s_step, s_zero] at hr; omega)]
        | succ p =>
          change constantCoeff (Q (p+2)) = 1 ∧
            (∀ r, s (p+2) < r → coeff r (Q (p+2)) = 0) ∧
            (∀ r, s (p+2) ≤ r → coeff r (N (p+2)) = 0)
          obtain ⟨hq0, hqs, hns⟩ := ih p (by omega)
          obtain ⟨hq10, hq1s, hn1s⟩ := ih (p+1) (by omega)
          have hs1 := s_step p
          have hs2 : s (p+2) = s (p+1)+k (p+1)+1 := by
            simpa only [Nat.add_assoc] using s_step (p+1)
          have he : k p + k (p+1) + 2 + s p = s (p+2) := by omega
          refine ⟨?_, ?_, ?_⟩
          · rw [q_step]
            simp [d_zero, hq10]
          · intro r hr
            rw [q_step, map_sub]
            have ha : coeff r (D (p+1)*Q (p+1)) = 0 := by
              rw [convolution]
              apply Finset.sum_eq_zero
              intro x hx
              have hxsum := Finset.mem_antidiagonal.mp hx
              by_cases hd : k (p+1)+1 < x.1
              · rw [d_support _ _ hd, zero_mul]
              · rw [hq1s _ (by omega), mul_zero]
            rw [ha]
            rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
            split_ifs with hle
            · rw [hqs _ (by omega)]; ring
            · ring
          · intro r hr
            rw [n_step, map_sub]
            have ha : coeff r (D (p+1)*N (p+1)) = 0 := by
              rw [convolution]
              apply Finset.sum_eq_zero
              intro x hx
              have hxsum := Finset.mem_antidiagonal.mp hx
              by_cases hd : k (p+1)+1 < x.1
              · rw [d_support _ _ hd, zero_mul]
              · rw [hn1s _ (by omega), mul_zero]
            rw [ha]
            rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
            split_ifs with hle
            · rw [hns _ (by omega)]; ring
            · ring
  let F (p : ℕ) := if p = 0 then -Fs 0 else Fs (p % 3)
  let G (p : ℕ) := if p = 0 then -Gs 0 else Gs (p % 3)
  have tail (p : ℕ) : F p = X ^ k p * G p := by
    rw [(data p).1]
    by_cases hp : p = 0
    · subst p
      have he := (hcycle 0 (by omega)).1
      simpa [F, G, kd] using congrArg Neg.neg he
    · simpa [F, G, hp, kd] using (hcycle (p % 3) (Nat.mod_lt p (by omega))).1
  have leading (p : ℕ) : constantCoeff (G p) = v p := by
    rw [(data p).2.1]
    by_cases hp : p = 0
    · subst p
      simp [G, (hcycle 0 (by omega)).2.1, bd]
    · simp only [G, if_neg hp]
      simpa [bd] using (hcycle (p % 3) (Nat.mod_lt p (by omega))).2.1
  have transition (p : ℕ) : D p * F p - C (v p) * X ^ k p =
      X ^ (k p + 2) * F (p + 1) * F p := by
    rw [(data p).1, (data p).2.1, (data p).2.2]
    by_cases hp : p = 0
    · subst p
      have he := (hcycle 0 (by omega)).2.2
      norm_num [F, next, Dd, kd, bd] at he ⊢
      linear_combination -he
    · have he := (hcycle (p % 3) (Nat.mod_lt p (by omega))).2.2
      have hn : next (p % 3) = (p + 1) % 3 := by simp [next, Nat.add_mod]
      simpa [F, hp, show p + 1 ≠ 0 by omega, Dd, kd, bd, hn] using he
  refine ⟨F, ?_, bounds, approximation k s v h D F G Q N s_zero s_step h_zero h_step
    tail leading transition q_zero q_one n_zero n_one q_step n_step⟩
  have he := root_eq 0
  norm_num [A, B, C₀, F] at he ⊢
  linear_combination -he

end D5.S3.Combinatorics.MetallicHankel.MetallicHankelUnboundedGolden
