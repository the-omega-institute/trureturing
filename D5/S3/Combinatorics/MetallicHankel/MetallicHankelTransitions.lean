/- GID: D5/S3/Combinatorics/MetallicHankel/MetallicHankelTransitions
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MetallicHankel/MetallicHankelTransitions
   mirror-E: none(waiver:finite-continuant-approximation)
   anchors: [mathlib/module/Mathlib.RingTheory.Henselian]
   utility: none
   digest: Finite continuant induction proves the leading error of quadratic-series tails. -/

import D5.S3.Combinatorics.MetallicHankel.MetallicHankelData
import Mathlib.RingTheory.Henselian

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MetallicHankel.MetallicHankelTransitions

open PowerSeries MetallicHankelData

set_option maxHeartbeats 4000000 in
/-- The concrete quadratic cycle gives integral metallic continuant approximations. -/
theorem metallic_approximation (n : ℕ) (hn : 2 ≤ n)
    (state : ℕ → TailState) (state_zero : state 0 = .v₂)
    (state_step : ∀ p, state (p + 1) = nextState n (state p))
    (k s : ℕ → ℕ) (v h : ℕ → ℤ) (D Q N : ℕ → PowerSeries ℤ)
    (data : ∀ p, k p = (fractionData n (state p)).1 ∧
      v p = (if p = 0 then 1 else (fractionData n (state p)).2.1) ∧
      D p = (fractionData n (state p)).2.2)
    (s_zero : s 0 = 0) (s_step : ∀ p, s (p + 1) = s p + k p + 1)
    (h_zero : h 0 = v 0) (h_step : ∀ p, h (p + 1) = h p * v (p + 1))
    (q_zero : Q 0 = 1) (q_one : Q 1 = D 0)
    (n_zero : N 0 = 0) (n_one : N 1 = C (v 0) * X ^ k 0)
    (q_step : ∀ p, Q (p + 2) = D (p + 1) * Q (p + 1) -
      C (v (p + 1)) * X ^ (k p + k (p + 1) + 2) * Q p)
    (n_step : ∀ p, N (p + 2) = D (p + 1) * N (p + 1) -
      C (v (p + 1)) * X ^ (k p + k (p + 1) + 2) * N p) :
    ∃ F : ℕ → PowerSeries ℤ,
      X ^ (n + 2) * F 0 ^ 2 + (quadraticData n .v₂).2.1 * F 0 = X ^ (n - 1) ∧
      (∀ p, constantCoeff (Q p) = 1 ∧
        (∀ r, s p < r → coeff r (Q p) = 0) ∧
        (∀ r, s p ≤ r → coeff r (N p) = 0)) ∧
      ∀ p, ∃ R : PowerSeries ℤ,
        Q p * F 0 - N p = X ^ (2 * s p + k p) * R ∧ constantCoeff R = h p := by
  classical
  have cycle :
      ∃ Fs Gs : TailState → PowerSeries ℤ, ∀ z, validState n z →
        X * (quadraticData n z).2.2 * Fs z ^ 2 + (quadraticData n z).2.1 * Fs z =
          -(quadraticData n z).1 ∧
        Fs z = X ^ (fractionData n z).1 * Gs z ∧
        constantCoeff (Gs z) = (fractionData n z).2.1 ∧
        (fractionData n z).2.2 * Fs z - C (fractionData n z).2.1 *
          X ^ (fractionData n z).1 =
        X ^ ((fractionData n z).1 + 2) * Fs (nextState n z) * Fs z := by
    classical
    clear state state_zero state_step k s v h D Q N data s_zero s_step
      h_zero h_step q_zero q_one n_zero n_one q_step n_step
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
    have constants : ∀ z, validState n z →
        constantCoeff ((quadraticData n z).2.1) = 1 ∧
        constantCoeff ((fractionData n z).2.2) = 1 := by
      intro z hz
      have hn0 : n ≠ 0 := by omega
      have hn1 : n-1 ≠ 0 := by omega
      cases z with
      | u₀ i | u₁ i | u₂ i | w₀ i | w₁ i | w₂ i =>
        dsimp [validState] at hz
        have hni : n-i ≠ 0 := by omega
        have hni1 : n-i-1 ≠ 0 := by omega
        simp [quadraticData, fractionData, hn0, hn1, hni, hni1] <;>
          split_ifs <;> simp [hn0, hn1]
      | v₀ | v₁ | v₂ | v₃ =>
        simp [quadraticData, fractionData, hn0, hn1]
    have raw : ∀ z, validState n z → ∀ G : PowerSeries ℤ,
        let A := (quadraticData n z).1
        let B := (quadraticData n z).2.1
        let C₀ := (quadraticData n z).2.2
        let A₁ := (quadraticData n (nextState n z)).1
        let B₁ := (quadraticData n (nextState n z)).2.1
        let C₁ := (quadraticData n (nextState n z)).2.2
        let k := (fractionData n z).1
        let v := (fractionData n z).2.1
        let D := (fractionData n z).2.2
        A * (D - X ^ (k+2) * G)^2 + B * PowerSeries.C v * X^k *
          (D-X^(k+2)*G) + X*C₀*(PowerSeries.C v * X^k)^2 =
          PowerSeries.C v * X^(2*k+2) * (A₁+B₁*G+X*C₁*G^2) := by
      intro z hz G
      let I := invOfUnit (1-X : PowerSeries ℤ) 1
      have hI : (1-X : PowerSeries ℤ)*I=1 := by simp [I]
      cases z with
      | u₀ i =>
        dsimp [validState] at hz
        dsimp [quadraticData, fractionData, nextState]
        obtain ⟨t, rfl⟩ : ∃ t, n = i + (t + 2) := ⟨n-i-2, by omega⟩
        have h1 : i+(t+2)-i = t+2 := by omega
        have h2 : i+(t+2)-i-1 = t+1 := by omega
        simp only [h2, h1, two_mul, pow_add, pow_succ, map_neg, map_one]
        have h3 : i+t+1-i = t+1 := by omega
        try simp only [h3, Nat.add_assoc, Nat.add_sub_cancel_left, pow_add, pow_succ]
        clear hz hn h1 h2 h3
        grind only
      | u₁ i =>
        dsimp [validState] at hz
        dsimp [quadraticData, fractionData, nextState]
        by_cases hb : i = n-2
        · simp only [hb, if_pos, if_neg, if_true, if_false]
          subst i
          obtain ⟨t, rfl⟩ : ∃ t, n = t + 2 := ⟨n-2, by omega⟩
          simp only [Nat.add_sub_cancel_right, Nat.add_sub_add_right,
            two_mul, pow_add, pow_succ, map_neg, map_one, pow_zero]
          try simp only [Nat.add_assoc, Nat.add_sub_cancel_left, pow_add, pow_succ]
          clear hz hn
          grind only
        · simp only [hb, if_pos, if_neg, if_true, if_false]
          obtain ⟨t, rfl⟩ : ∃ t, n = i + (t + 3) := ⟨n-i-3, by omega⟩
          have h1 : i+(t+3)-i = t+3 := by omega
          have h2 : i+(t+3)-i-1 = t+2 := by omega
          simp only [h2, h1, two_mul, pow_add, pow_succ, map_neg, map_one]
          have h3 : i+t+2-i = t+2 := by omega
          try simp only [h3, Nat.add_assoc, Nat.add_sub_cancel_left, pow_add, pow_succ]
          clear hz hn h1 h2 h3 hb
          grind only
      | u₂ i =>
        dsimp [validState] at hz
        dsimp [quadraticData, fractionData, nextState]
        by_cases hb : i = n-2
        · simp only [hb, if_pos, if_neg, if_true, if_false]
          subst i
          obtain ⟨t, rfl⟩ : ∃ t, n = t + 2 := ⟨n-2, by omega⟩
          simp only [Nat.add_sub_cancel_right, Nat.add_sub_add_right,
            two_mul, pow_add, pow_succ, map_neg, map_one, pow_zero]
          try simp only [Nat.add_assoc, Nat.add_sub_cancel_left, pow_add, pow_succ]
          clear hz hn
          grind only
        · simp only [hb, if_pos, if_neg, if_true, if_false]
          obtain ⟨t, rfl⟩ : ∃ t, n = i + (t + 3) := ⟨n-i-3, by omega⟩
          have h1 : i+(t+3)-i = t+3 := by omega
          have h2 : i+(t+3)-i-1 = t+2 := by omega
          simp only [h2, h1, two_mul, pow_add, pow_succ, map_neg, map_one]
          have h3 : i+t+2-i = t+2 := by omega
          try simp only [h3, Nat.add_assoc, Nat.add_sub_cancel_left, pow_add, pow_succ]
          clear hz hn h1 h2 h3 hb
          grind only
      | v₀ =>
        dsimp [validState] at hz
        dsimp [quadraticData, fractionData, nextState]
        obtain ⟨t, rfl⟩ : ∃ t, n = t + 2 := ⟨n-2, by omega⟩
        simp only [Nat.add_sub_cancel_right, Nat.add_sub_add_right,
          two_mul, pow_add, pow_succ, map_neg, map_one, pow_zero]
        try simp only [Nat.add_assoc, Nat.add_sub_cancel_left, pow_add, pow_succ]
        clear hz hn
        grind only
      | v₁ =>
        dsimp [validState] at hz
        dsimp [quadraticData, fractionData, nextState]
        obtain ⟨t, rfl⟩ : ∃ t, n = t + 2 := ⟨n-2, by omega⟩
        simp only [Nat.add_sub_cancel_right, Nat.add_sub_add_right,
          two_mul, pow_add, pow_succ, map_neg, map_one, pow_zero]
        try simp only [Nat.add_assoc, Nat.add_sub_cancel_left, pow_add, pow_succ]
        clear hz hn
        grind only
      | v₂ =>
        dsimp [validState] at hz
        dsimp [quadraticData, fractionData, nextState]
        obtain ⟨t, rfl⟩ : ∃ t, n = t + 2 := ⟨n-2, by omega⟩
        simp only [Nat.add_sub_cancel_right, Nat.add_sub_add_right,
          two_mul, pow_add, pow_succ, map_neg, map_one, pow_zero]
        try simp only [Nat.add_assoc, Nat.add_sub_cancel_left, pow_add, pow_succ]
        clear hz hn
        grind only
      | v₃ =>
        dsimp [validState] at hz
        dsimp [quadraticData, fractionData, nextState]
        obtain ⟨t, rfl⟩ : ∃ t, n = t + 2 := ⟨n-2, by omega⟩
        simp only [Nat.add_sub_cancel_right, Nat.add_sub_add_right,
          two_mul, pow_add, pow_succ, map_neg, map_one, pow_zero]
        try simp only [Nat.add_assoc, Nat.add_sub_cancel_left, pow_add, pow_succ]
        clear hz hn
        grind only
      | w₀ i =>
        dsimp [validState] at hz
        dsimp [quadraticData, fractionData, nextState]
        by_cases hb : i = n-2
        · simp only [hb, if_pos, if_neg, if_true, if_false]
          subst i
          obtain ⟨t, rfl⟩ : ∃ t, n = t + 2 := ⟨n-2, by omega⟩
          simp only [Nat.add_sub_cancel_right, Nat.add_sub_add_right,
            two_mul, pow_add, pow_succ, map_neg, map_one, pow_zero]
          try simp only [Nat.add_assoc, Nat.add_sub_cancel_left, pow_add, pow_succ]
          clear hz hn
          grind only
        · simp only [hb, if_pos, if_neg, if_true, if_false]
          obtain ⟨t, rfl⟩ : ∃ t, n = i + (t + 2) := ⟨n-i-2, by omega⟩
          have h1 : i+(t+2)-i = t+2 := by omega
          have h2 : i+(t+2)-i-1 = t+1 := by omega
          simp only [h2, h1, two_mul, pow_add, pow_succ, map_neg, map_one]
          have h3 : i+t+1-i = t+1 := by omega
          try simp only [h3, Nat.add_assoc, Nat.add_sub_cancel_left, pow_add, pow_succ]
          clear hz hn h1 h2 h3 hb
          grind only
      | w₁ i =>
        dsimp [validState] at hz
        dsimp [quadraticData, fractionData, nextState]
        obtain ⟨t, rfl⟩ : ∃ t, n = i + (t + 2) := ⟨n-i-2, by omega⟩
        have h1 : i+(t+2)-i = t+2 := by omega
        have h2 : i+(t+2)-i-1 = t+1 := by omega
        simp only [h2, h1, two_mul, pow_add, pow_succ, map_neg, map_one]
        have h3 : i+t+1-i = t+1 := by omega
        try simp only [h3, Nat.add_assoc, Nat.add_sub_cancel_left, pow_add, pow_succ]
        clear hz hn h1 h2 h3
        grind only
      | w₂ i =>
        dsimp [validState] at hz
        dsimp [quadraticData, fractionData, nextState]
        obtain ⟨t, rfl⟩ : ∃ t, n = i + (t + 3) := ⟨n-i-3, by omega⟩
        have h1 : i+(t+3)-i = t+3 := by omega
        have h2 : i+(t+3)-i-1 = t+2 := by omega
        simp only [h2, h1, two_mul, pow_add, pow_succ, map_neg, map_one]
        have h3 : i+t+2-i = t+2 := by omega
        try simp only [h3, Nat.add_assoc, Nat.add_sub_cancel_left, pow_add, pow_succ]
        clear hz hn h1 h2 h3
        grind only
    have next_valid : ∀ z, validState n z → validState n (nextState n z) := by
      intro z hz
      cases z <;> simp only [validState, nextState] at * <;>
        (try split_ifs) <;> (try simp only [validState]) <;> omega
    have roots : ∀ z, validState n z → ∃! F : PowerSeries ℤ,
        X * (quadraticData n z).2.2 * F ^ 2 + (quadraticData n z).2.1 * F =
          -(quadraticData n z).1 := by
      intro z hz
      exact quadratic_solution _ _ _ (constants z hz).1
    let Fs : TailState → PowerSeries ℤ := fun z =>
      if hz : validState n z then Classical.choose (roots z hz) else 0
    have root_eq (z) (hz : validState n z) :
        X * (quadraticData n z).2.2 * Fs z ^ 2 + (quadraticData n z).2.1 * Fs z =
          -(quadraticData n z).1 := by
      dsimp only [Fs]
      rw [dif_pos hz]
      exact (Classical.choose_spec (roots z hz)).1
    have unique (z) (hz : validState n z) (U : PowerSeries ℤ)
        (hU : X * (quadraticData n z).2.2 * U ^ 2 + (quadraticData n z).2.1 * U =
          -(quadraticData n z).1) : U = Fs z := by
      dsimp only [Fs]
      rw [dif_pos hz]
      exact (Classical.choose_spec (roots z hz)).2 U hU
    let K : TailState → PowerSeries ℤ := fun z =>
      (fractionData n z).2.2 - X ^ ((fractionData n z).1 + 2) * Fs (nextState n z)
    let J : TailState → PowerSeries ℤ := fun z => invOfUnit (K z) 1
    let Gs : TailState → PowerSeries ℤ := fun z => C (fractionData n z).2.1 * J z
    refine ⟨Fs, Gs, ?_⟩
    intro z hz
    have hK0 : constantCoeff (K z) = 1 := by
      simp [K, (constants z hz).2]
    have hKI : K z * J z = 1 := mul_invOfUnit (K z) 1 (by simpa using hK0)
    let H := C (fractionData n z).2.1 * X ^ (fractionData n z).1 * J z
    have hHroot : X * (quadraticData n z).2.2 * H ^ 2 +
        (quadraticData n z).2.1 * H = -(quadraticData n z).1 := by
      have hr := raw z hz (Fs (nextState n z))
      have he := root_eq (nextState n z) (next_valid z hz)
      dsimp only at hr
      have hnew : (quadraticData n (nextState n z)).1 +
          (quadraticData n (nextState n z)).2.1 * Fs (nextState n z) +
          X * (quadraticData n (nextState n z)).2.2 * Fs (nextState n z) ^ 2 = 0 := by
        linear_combination he
      rw [hnew, mul_zero] at hr
      have hHK : H * K z = C (fractionData n z).2.1 * X ^ (fractionData n z).1 := by
        dsimp only [H]
        calc
          _ = (C (fractionData n z).2.1 * X ^ (fractionData n z).1) *
              (K z * J z) := by ring
          _ = _ := by rw [hKI, mul_one]
      have hclear : K z ^ 2 * (X * (quadraticData n z).2.2 * H ^ 2 +
          (quadraticData n z).2.1 * H + (quadraticData n z).1) = 0 := by
        calc
          _ = (quadraticData n z).1 * K z ^ 2 +
              (quadraticData n z).2.1 * (H * K z) * K z +
              X * (quadraticData n z).2.2 * (H * K z) ^ 2 := by ring
          _ = 0 := by rw [hHK]; simpa only [K, mul_assoc] using hr
      have hu : IsUnit (K z) := by
        rw [isUnit_iff_constantCoeff, hK0]
        exact isUnit_one
      have hh := (hu.pow 2).mul_right_injective (show K z ^ 2 *
          (X * (quadraticData n z).2.2 * H ^ 2 + (quadraticData n z).2.1 * H +
            (quadraticData n z).1) = K z ^ 2 * 0 by simpa using hclear)
      linear_combination hh
    have hH : H = Fs z := unique z hz H hHroot
    refine ⟨root_eq z hz, ?_, ?_, ?_⟩
    · rw [← hH]
      dsimp only [H, Gs]
      ring
    · simp [Gs, J]
    · have hFK : Fs z * K z = C (fractionData n z).2.1 * X ^ (fractionData n z).1 := by
        rw [← hH]
        dsimp only [H]
        grind only
      dsimp only [K] at hFK
      grind only
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
  obtain ⟨Fs, Gs, hcycle⟩ := cycle
  have next_valid : ∀ z, validState n z → validState n (nextState n z) := by
    intro z hz
    cases z <;> simp only [validState, nextState] at * <;>
      (try split_ifs) <;> (try simp only [validState]) <;> omega
  have valid : ∀ p, validState n (state p) := by
    intro p
    induction p with
    | zero => simp [state_zero, validState]
    | succ p ih => rw [state_step]; exact next_valid _ ih
  have d_zero : ∀ p, constantCoeff (D p) = 1 := by
    intro p
    rw [(data p).2.2]
    exact ((cycle_data n hn).2.2.2.2.2 (state p) (valid p)).1
  have d_support : ∀ p r, k p + 1 < r → coeff r (D p) = 0 := by
    intro p r hr
    rw [(data p).2.2]
    apply ((cycle_data n hn).2.2.2.2.2 (state p) (valid p)).2 r
    simpa only [← (data p).1] using hr
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
            simp [d_zero, hq10, show k p+k (p+1)+2 ≠ 0 by omega]
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
  let F : ℕ → PowerSeries ℤ := fun p => if p = 0 then -Fs .v₂ else Fs (state p)
  let G : ℕ → PowerSeries ℤ := fun p => if p = 0 then -Gs .v₂ else Gs (state p)
  have tail : ∀ p, F p = X ^ k p * G p := by
    intro p
    obtain ⟨hk, hv, hd⟩ := data p
    by_cases hp : p = 0
    · subst p
      have ht := (hcycle .v₂ trivial).2.1
      rw [state_zero] at hk
      simp only [F, G, if_pos rfl, hk]
      rw [ht]
      ring
    · simp only [F, G, if_neg hp, hk]
      exact (hcycle _ (valid p)).2.1
  have leading : ∀ p, constantCoeff (G p) = v p := by
    intro p
    obtain ⟨hk, hv, hd⟩ := data p
    by_cases hp : p = 0
    · subst p
      have hl := (hcycle .v₂ trivial).2.2.1
      simp [G, hl, hv, fractionData]
    · simpa only [G, if_neg hp, hv] using (hcycle _ (valid p)).2.2.1
  have transition : ∀ p, D p * F p - C (v p) * X ^ k p =
      X ^ (k p + 2) * F (p + 1) * F p := by
    intro p
    obtain ⟨hk, hv, hd⟩ := data p
    by_cases hp : p = 0
    · subst p
      have ht := (hcycle .v₂ trivial).2.2.2
      have hs1 : state 1 = nextState n .v₂ := by simpa [state_zero] using state_step 0
      rw [state_zero] at hk hv hd
      simp only [F, if_pos rfl, show (1 : ℕ) ≠ 0 by omega, if_neg, hs1,
        hk, hv, hd, nextState, fractionData, Nat.zero_add, if_true, if_false, map_one]
      simp only [fractionData, nextState, map_neg, map_one] at ht
      linear_combination -ht
    · have ht := (hcycle _ (valid p)).2.2.2
      simpa only [F, if_neg hp, if_neg (show p + 1 ≠ 0 by omega),
        hk, hv, hd, state_step] using ht
  refine ⟨F, ?_, bounds, approximation k s v h D F G Q N s_zero s_step h_zero h_step
    tail leading transition q_zero q_one n_zero n_one q_step n_step⟩
  have he := (hcycle .v₂ trivial).1
  simp only [quadraticData] at he
  simp only [F, if_pos rfl, quadraticData]
  have hx : (X : PowerSeries ℤ) ^ (n + 2) = X * X ^ (n + 1) := by
    rw [show n+2 = 1+(n+1) by omega, pow_add, pow_one]
  rw [hx]
  linear_combination -he

end D5.S3.Combinatorics.MetallicHankel.MetallicHankelTransitions
