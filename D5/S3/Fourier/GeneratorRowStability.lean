/- GID: D5/S3/Fourier/GeneratorRowStability
   generality: G
   mirror-B: D5/B/S3/Fourier/GeneratorRowStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cyclic generator-row correction and equal-amplitude source-energy stability. -/

import D5.S3.Fourier.FullBispectrumStability
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic

namespace D5.S3.Fourier.GeneratorRowStability

open Finset
open scoped BigOperators ComplexConjugate
open FullBispectrumStability (cyclic_parseval dft_translation unit_mul_conj)

noncomputable section

private lemma unit_chord_phase (r : ℂ) (hr : ‖r‖ = 1)
    (hd : ‖r - 1‖ ≤ (1 : ℝ) / 4) :
    ∃ θ : ℝ, θ ∈ Set.Ioc (-Real.pi) Real.pi ∧
      Complex.exp (↑θ * Complex.I) = r ∧
      |θ| ≤ 8 * ‖r - 1‖ / Real.sqrt 63 := by
  obtain ⟨θ, hθ, hθr⟩ := Complex.norm_eq_one_iff'.mp hr
  have hchord : ‖r - 1‖ = ‖2 * Real.sin (θ / 2)‖ := by
    rw [← hθr]
    simpa [mul_comm] using Complex.norm_exp_I_mul_ofReal_sub_one θ
  have hθabs : |θ| ≤ Real.pi := abs_le.2 ⟨hθ.1.le, hθ.2⟩
  let u : ℝ := |θ| / 2
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu_le : u ≤ Real.pi / 2 := by
    dsimp [u]
    nlinarith [hθabs]
  have hu_lt : u < Real.pi / 2 := by
    by_contra hn
    have heq : u = Real.pi / 2 := le_antisymm hu_le (le_of_not_gt hn)
    have hθeq : |θ| = Real.pi := by dsimp [u] at heq; linarith
    have hs : Real.sin u = 1 := by rw [heq, Real.sin_pi_div_two]
    have hsin : ‖2 * Real.sin (θ / 2)‖ = 2 := by
      rcases le_total 0 θ with hpos | hneg
      · have : θ / 2 = u := by dsimp [u]; rw [abs_of_nonneg hpos]
        rw [this, hs]
        norm_num
      · have hθhalf : θ / 2 = -u := by
          dsimp [u]
          rw [abs_of_nonpos hneg]
          ring
        rw [hθhalf, Real.sin_neg]
        have htmp : 2 * -Real.sin u = -(2 * Real.sin u) := by ring
        rw [htmp, norm_neg, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.sin u)]
        nlinarith [hs]
    rw [hchord, hsin] at hd
    norm_num at hd
  have hsin_nonneg : 0 ≤ Real.sin u :=
    Real.sin_nonneg_of_mem_Icc ⟨hu0, hu_le.trans (by nlinarith [Real.pi_pos])⟩
  have hsin_chord : ‖r - 1‖ = 2 * Real.sin u := by
    rw [hchord]
    rcases le_total 0 θ with hpos | hneg
    · have hθhalf : θ / 2 = u := by dsimp [u]; rw [abs_of_nonneg hpos]
      rw [hθhalf, Real.norm_of_nonneg (mul_nonneg (by norm_num) hsin_nonneg)]
    · have hθhalf : θ / 2 = -u := by
        dsimp [u]
        rw [abs_of_nonpos hneg]
        ring
      rw [hθhalf, Real.sin_neg]
      have htmp : 2 * -Real.sin u = -(2 * Real.sin u) := by ring
      rw [htmp, norm_neg, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.sin u)]
  have hsin_le : Real.sin u ≤ (1 : ℝ) / 8 := by
    nlinarith [hd, hsin_chord]
  have hcos_nonneg : 0 ≤ Real.cos u :=
    Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [Real.pi_pos], hu_le⟩
  have hcos_sq : (Real.sqrt 63 / 8 : ℝ) ^ 2 ≤ (Real.cos u) ^ 2 := by
    have hsquare : (Real.sin u) ^ 2 ≤ ((1 : ℝ) / 8) ^ 2 :=
      (sq_le_sq₀ hsin_nonneg (by norm_num)).2 hsin_le
    have hsqrt : (Real.sqrt 63 / 8 : ℝ) ^ 2 = (63 : ℝ) / 64 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 63)]
      norm_num
    rw [hsqrt]
    nlinarith [Real.sin_sq_add_cos_sq u]
  have hcos : Real.sqrt 63 / 8 ≤ Real.cos u := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt 63 / 8 := by positivity
    nlinarith
  have htan := Real.le_tan hu0 hu_lt
  rw [Real.tan_eq_sin_div_cos] at htan
  have hcos_pos : 0 < Real.cos u := lt_of_lt_of_le (by positivity) hcos
  have hmul : u * (Real.sqrt 63 / 8) ≤ Real.sin u := by
    have htan' : u * Real.cos u ≤ Real.sin u := (le_div_iff₀ hcos_pos).mp htan
    exact (mul_le_mul_of_nonneg_left hcos hu0).trans htan'
  have hu_bound : u ≤ 8 * Real.sin u / Real.sqrt 63 := by
    apply (le_div_iff₀ (by positivity)).2
    nlinarith [hmul]
  have hθbound : |θ| ≤ 16 * Real.sin u / Real.sqrt 63 := by
    calc
      |θ| = 2 * (|θ| / 2) := by ring
      _ ≤ 2 * (8 * Real.sin u / Real.sqrt 63) :=
        mul_le_mul_of_nonneg_left hu_bound (by norm_num)
      _ = 16 * Real.sin u / Real.sqrt 63 := by ring
  have hsin_chord' : ‖r - 1‖ = 2 * Real.sin u := hsin_chord
  have hsqrtpos : 0 < Real.sqrt 63 := by positivity
  refine ⟨θ, hθ, hθr, ?_⟩
  calc
    |θ| ≤ 16 * Real.sin u / Real.sqrt 63 := hθbound
    _ = 8 * (2 * Real.sin u) / Real.sqrt 63 := by ring
    _ = 8 * ‖r - 1‖ / Real.sqrt 63 := by rw [← hsin_chord']

private noncomputable def chosenAngle (r : ℂ) : ℝ :=
  if h : ‖r‖ = 1 ∧ ‖r - 1‖ ≤ (1 : ℝ) / 4 then
    Classical.choose (unit_chord_phase r h.1 h.2)
  else 0

private lemma chosenAngle_spec (r : ℂ) (hr : ‖r‖ = 1)
    (hd : ‖r - 1‖ ≤ (1 : ℝ) / 4) :
    chosenAngle r ∈ Set.Ioc (-Real.pi) Real.pi ∧
      Complex.exp (↑(chosenAngle r) * Complex.I) = r ∧
      |chosenAngle r| ≤ 8 * ‖r - 1‖ / Real.sqrt 63 := by
  rw [chosenAngle]
  split_ifs with h
  · exact Classical.choose_spec (unit_chord_phase r h.1 h.2)
  · exact False.elim (h ⟨hr, hd⟩)

private lemma real_sum_abs_le {N : ℕ} (θ : ZMod N → ℝ) (ω : ℝ)
    (_hω : 0 ≤ ω) (hθ : ∀ k, |θ k| ≤ ω) (s : Finset ℕ) :
    |∑ j ∈ s, θ (j : ZMod N)| ≤ (s.card : ℝ) * ω := by
  calc
    |∑ j ∈ s, θ (j : ZMod N)| = ‖∑ j ∈ s, θ (j : ZMod N)‖ := rfl
    _ ≤ ∑ j ∈ s, ‖θ (j : ZMod N)‖ := norm_sum_le s _
    _ ≤ ∑ _j ∈ s, ω := by
      apply Finset.sum_le_sum
      intro j hj
      exact hθ (j : ZMod N)
    _ = (s.card : ℝ) * ω := by simp [mul_comm]

private lemma phase_recurrence {N : ℕ} [NeZero N] (z : ZMod N → ℂ)
    (θ : ZMod N → ℝ) (hz : ∀ k, ‖z k‖ = 1)
    (hr : ∀ k, Complex.exp (↑(θ k) * Complex.I) =
      z k * z 1 * conj (z (k + 1))) (k : ZMod N) :
    z (k + 1) = z k * z 1 * Complex.exp (-(↑(θ k) * Complex.I)) := by
  have hk := unit_mul_conj (z (k + 1)) (hz (k + 1))
  have he : Complex.exp (↑(θ k) * Complex.I) *
      Complex.exp (-(↑(θ k) * Complex.I)) = 1 := by
    rw [← Complex.exp_add]
    simp
  have hk' : conj (z (k + 1)) * z (k + 1) = 1 := by
    rw [mul_comm]
    exact hk
  calc
    z (k + 1) = z (k + 1) * 1 := by rw [mul_one]
    _ = z (k + 1) *
        (Complex.exp (↑(θ k) * Complex.I) *
          Complex.exp (-(↑(θ k) * Complex.I))) := by rw [he, mul_one]
    _ = z (k + 1) *
        (z k * z 1 * conj (z (k + 1))) *
          Complex.exp (-(↑(θ k) * Complex.I)) := by rw [hr k]; ring
    _ = z k * z 1 * Complex.exp (-(↑(θ k) * Complex.I)) := by
      have hprod : z (k + 1) * (z k * z 1 * conj (z (k + 1))) = z k * z 1 := by
        calc
          _ = z k * z 1 * (z (k + 1) * conj (z (k + 1))) := by ring
          _ = z k * z 1 := by rw [hk, mul_one]
      rw [hprod]

private lemma shifted_sum_abs_le {N : ℕ} (θ : ZMod N → ℝ) (ω : ℝ)
    (_hω : 0 ≤ ω) (hθ : ∀ k, |θ k| ≤ ω) (a l : ℕ) :
    |∑ j ∈ Finset.range l, θ ((a + j : ℕ) : ZMod N)| ≤ (l : ℝ) * ω := by
  calc
    |∑ j ∈ Finset.range l, θ ((a + j : ℕ) : ZMod N)| =
        ‖∑ j ∈ Finset.range l, θ ((a + j : ℕ) : ZMod N)‖ := rfl
    _ ≤ ∑ j ∈ Finset.range l, ‖θ ((a + j : ℕ) : ZMod N)‖ :=
      norm_sum_le (Finset.range l) _
    _ ≤ ∑ _j ∈ Finset.range l, ω := by
      apply Finset.sum_le_sum
      intro j hj
      exact hθ _
    _ = (l : ℝ) * ω := by simp [mul_comm]

private lemma cyclic_phase_correction_of_angles {N : ℕ} [NeZero N]
    (z : ZMod N → ℂ) (θ : ZMod N → ℝ) (ω : ℝ)
    (hz0 : z 0 = 1) (hz : ∀ k, ‖z k‖ = 1)
    (hθ0 : θ 0 = 0) (hr : ∀ k, Complex.exp (↑(θ k) * Complex.I) =
      z k * z 1 * conj (z (k + 1))) (hω : 0 ≤ ω)
    (hθ : ∀ k, |θ k| ≤ ω) :
    ∃ q : ℂ, q ^ N = 1 ∧ ∀ k,
      ‖z k - q ^ k.val‖ ≤ (N - 1 : ℝ) * ω / 2 := by
  let S : ℝ := ∑ j ∈ Finset.range N, θ (j : ZMod N)
  have hseq : ∀ n : ℕ,
      z (n : ZMod N) = z 1 ^ n *
        Complex.exp (-(Complex.I * (∑ j ∈ Finset.range n, θ (j : ZMod N) : ℂ))) := by
    intro n
    induction n with
    | zero => simp [hz0]
    | succ n ih =>
        have hh := phase_recurrence z θ hz hr (n : ZMod N)
        have hsum := Finset.sum_range_succ (fun j : ℕ => θ (j : ZMod N)) n
        calc
          z ((n + 1 : ℕ) : ZMod N) = z ((n : ZMod N) + 1) := by norm_num
          _ = z (n : ZMod N) * z 1 *
              Complex.exp (-(↑(θ (n : ZMod N)) * Complex.I)) := hh
          _ = (z 1 ^ n * Complex.exp (-(Complex.I *
              (∑ j ∈ Finset.range n, θ (j : ZMod N) : ℂ))) * z 1) *
              Complex.exp (-(↑(θ (n : ZMod N)) * Complex.I)) := by rw [ih]
          _ = z 1 ^ n * z 1 *
              (Complex.exp (-(Complex.I *
                (∑ j ∈ Finset.range n, θ (j : ZMod N) : ℂ))) *
                Complex.exp (-(↑(θ (n : ZMod N)) * Complex.I))) := by ring
          _ = z 1 ^ n * z 1 * Complex.exp (-(Complex.I *
              ((∑ j ∈ Finset.range n, θ (j : ZMod N) : ℂ) +
                ↑(θ (n : ZMod N))))) := by
            rw [← Complex.exp_add]
            congr 2
            ring
          _ = z 1 ^ (n + 1) * Complex.exp (-(Complex.I *
              (∑ j ∈ Finset.range (n + 1), θ (j : ZMod N) : ℂ))) := by
            rw [pow_succ]
            congr 2
            rw [Finset.sum_range_succ]
  have hclosure : z 1 ^ N * Complex.exp (-(Complex.I * (S : ℂ))) = 1 := by
    have hh := hseq N
    rw [ZMod.natCast_self, hz0] at hh
    simpa [S] using hh.symm
  let q : ℂ := z 1 * Complex.exp (Complex.I * (-(S / N : ℝ) : ℂ))
  have hscale : (N : ℂ) * (Complex.I * (-(S / N : ℝ) : ℂ)) =
      -(Complex.I * (S : ℂ)) := by
    push_cast
    field_simp [NeZero.ne N]
  have hq : q ^ N = 1 := by
    dsimp [q]
    rw [mul_pow, ← Complex.exp_nat_mul, hscale, hclosure]
  refine ⟨q, hq, ?_⟩
  intro k
  let n := k.val
  have hn : n < N := ZMod.val_lt k
  have hkn : (n : ZMod N) = k := ZMod.natCast_zmod_val k
  have hqpow : q ^ n = z 1 ^ n *
      Complex.exp (Complex.I * (-(n : ℝ) * (S / N) : ℂ)) := by
    dsimp [q]
    rw [mul_pow, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring_nf
  have hS : S = (∑ j ∈ Finset.range n, θ (j : ZMod N)) +
      ∑ j ∈ Finset.range (N - n), θ ((n + j : ℕ) : ZMod N) := by
    dsimp [S]
    have hsplit := Finset.sum_range_add (fun j : ℕ => θ (j : ZMod N)) n (N - n)
    simpa [show n + (N - n) = N by omega] using hsplit
  have hθbound :
      |(n : ℝ) * S / N - ∑ j ∈ Finset.range n, θ (j : ZMod N)| ≤
        (N - 1 : ℝ) * ω / 2 := by
    by_cases hn0 : n = 0
    · simp [hn0]
      have hN1 : (1 : ℝ) ≤ N := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
      nlinarith
    · have hnle : n ≤ N := by omega
      have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
      have hB := shifted_sum_abs_le θ ω hω hθ n (N - n)
      have hA :
          |∑ j ∈ Finset.range n, θ (j : ZMod N)| ≤ (n - 1 : ℝ) * ω := by
        have hmem : 0 ∈ Finset.range n := Finset.mem_range.mpr (Nat.pos_of_ne_zero hn0)
        calc
          |∑ j ∈ Finset.range n, θ (j : ZMod N)| =
              |(∑ j ∈ (Finset.range n).erase 0, θ (j : ZMod N)) + θ 0| := by
                simpa only [Nat.cast_zero] using congrArg abs
                  (Finset.sum_erase_add (Finset.range n)
                    (fun j => θ (j : ZMod N)) hmem).symm
          _ = |∑ j ∈ (Finset.range n).erase 0, θ (j : ZMod N)| := by rw [hθ0, add_zero]
          _ ≤ (((Finset.range n).erase 0).card : ℝ) * ω :=
            real_sum_abs_le θ ω hω hθ ((Finset.range n).erase 0)
          _ = (n - 1 : ℝ) * ω := by
            rw [Finset.card_erase_of_mem hmem, Finset.card_range]
            rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn0)]
            norm_num
      have hphi_eq :
          (n : ℝ) * S / N - ∑ j ∈ Finset.range n, θ (j : ZMod N) =
            (n : ℝ) / N *
                (∑ j ∈ Finset.range (N - n), θ ((n + j : ℕ) : ZMod N)) -
              ((N - n : ℕ) : ℝ) / N *
                (∑ j ∈ Finset.range n, θ (j : ZMod N)) := by
        rw [hS]
        rw [Nat.cast_sub hnle]
        field_simp [hNpos.ne']
        ring
      have hdisc :
          2 * ((N - n : ℕ) : ℝ) * (2 * (n : ℝ) - 1) ≤
            (N : ℝ) * ((N : ℝ) - 1) := by
        rw [Nat.cast_sub hnle]
        by_cases hc : 2 * n ≤ N
        · have hcR : 2 * (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hc
          have h₁ : 2 * (n : ℝ) - (N : ℝ) ≤ 0 := by linarith
          have h₂ : 2 * (n : ℝ) - (N : ℝ) - 1 ≤ 0 := by linarith
          have hp : 0 ≤ (2 * (n : ℝ) - (N : ℝ)) *
              (2 * (n : ℝ) - (N : ℝ) - 1) :=
            mul_nonneg_of_nonpos_of_nonpos h₁ h₂
          nlinarith
        · have hc' : N + 1 ≤ 2 * n := by omega
          have hcR : (N : ℝ) + 1 ≤ 2 * (n : ℝ) := by exact_mod_cast hc'
          have h₁ : 0 ≤ 2 * (n : ℝ) - (N : ℝ) := by linarith
          have h₂ : 0 ≤ 2 * (n : ℝ) - (N : ℝ) - 1 := by linarith
          have hp : 0 ≤ (2 * (n : ℝ) - (N : ℝ)) *
              (2 * (n : ℝ) - (N : ℝ) - 1) := mul_nonneg h₁ h₂
          nlinarith
      rw [hphi_eq]
      calc
        |(n : ℝ) / N *
              (∑ j ∈ Finset.range (N - n), θ ((n + j : ℕ) : ZMod N)) -
            ((N - n : ℕ) : ℝ) / N *
              (∑ j ∈ Finset.range n, θ (j : ZMod N))| ≤
          |(n : ℝ) / N *
              (∑ j ∈ Finset.range (N - n), θ ((n + j : ℕ) : ZMod N))| +
            |((N - n : ℕ) : ℝ) / N *
              (∑ j ∈ Finset.range n, θ (j : ZMod N))| := by
                have hh := abs_sub_le
                  ((n : ℝ) / N *
                    (∑ j ∈ Finset.range (N - n), θ ((n + j : ℕ) : ZMod N)))
                  0 (((N - n : ℕ) : ℝ) / N *
                    (∑ j ∈ Finset.range n, θ (j : ZMod N)))
                simpa [abs_neg, sub_eq_add_neg] using hh
        _ = (n : ℝ) / N *
              |∑ j ∈ Finset.range (N - n), θ ((n + j : ℕ) : ZMod N)| +
            ((N - n : ℕ) : ℝ) / N *
              |∑ j ∈ Finset.range n, θ (j : ZMod N)| := by
                rw [abs_mul, abs_mul, abs_div, abs_div]
                have hnR : 0 ≤ (n : ℝ) := by positivity
                have hNmR : 0 ≤ ((N - n : ℕ) : ℝ) := by positivity
                simp [abs_of_nonneg hnR, abs_of_nonneg hNmR,
                  abs_of_pos hNpos]
        _ ≤ (n : ℝ) / N * ((N - n : ℕ) : ℝ) * ω +
            ((N - n : ℕ) : ℝ) / N * ((n : ℝ) - 1) * ω := by
              apply add_le_add
              · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hB
                  (div_nonneg (Nat.cast_nonneg n) hNpos.le)
              · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hA
                  (div_nonneg (Nat.cast_nonneg (N - n)) hNpos.le)
        _ = ((N - n : ℕ) : ℝ) * (2 * (n : ℝ) - 1) / N * ω := by
              field_simp [hNpos.ne']
              ring
        _ ≤ (N - 1 : ℝ) * ω / 2 := by
              have hcoef :
                  ((N - n : ℕ) : ℝ) * (2 * (n : ℝ) - 1) / N ≤
                    (N - 1 : ℝ) / 2 := by
                apply (div_le_iff₀ hNpos).mpr
                nlinarith [hdisc]
              simpa only [div_mul_eq_mul_div] using mul_le_mul_of_nonneg_right hcoef hω
  have hbound_n : ‖z (n : ZMod N) - q ^ n‖ ≤ (N - 1 : ℝ) * ω / 2 := by
    rw [hseq n, hqpow]
    have hexp : Complex.exp (-(Complex.I *
        (∑ j ∈ Finset.range n, θ (j : ZMod N) : ℂ))) =
        Complex.exp (Complex.I *
          ((n : ℝ) * S / N - ∑ j ∈ Finset.range n, θ (j : ZMod N))) *
          Complex.exp (Complex.I * (-(n : ℝ) * (S / N) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    have hdiff : z 1 ^ n *
        (Complex.exp (Complex.I *
            ((n : ℝ) * S / N - ∑ j ∈ Finset.range n, θ (j : ZMod N))) *
          Complex.exp (Complex.I * (-(n : ℝ) * (S / N) : ℂ))) -
          z 1 ^ n * Complex.exp (Complex.I * (-(n : ℝ) * (S / N) : ℂ)) =
        (z 1 ^ n * Complex.exp (Complex.I * (-(n : ℝ) * (S / N) : ℂ))) *
          (Complex.exp (Complex.I *
            ((n : ℝ) * S / N - ∑ j ∈ Finset.range n, θ (j : ZMod N))) - 1) := by ring
    rw [hdiff, norm_mul, norm_mul, norm_pow, hz 1, one_pow]
    have hnormB : ‖Complex.exp (Complex.I * (-(n : ℝ) * (S / N) : ℂ))‖ = 1 := by
      convert Complex.norm_exp_I_mul_ofReal (-(n : ℝ) * (S / N)) using 1
      push_cast
      ring
    rw [hnormB]
    simp only [one_mul]
    have hh := Real.norm_exp_I_mul_ofReal_sub_one_le.trans hθbound
    have harg :
        (↑((n : ℝ) * S / N -
          ∑ j ∈ Finset.range n, θ (j : ZMod N)) : ℂ) =
          (n : ℝ) * (S : ℂ) / N -
            ↑(∑ j ∈ Finset.range n, θ (j : ZMod N)) := by
      push_cast
      ring
    rw [harg] at hh
    exact hh
  simpa only [hkn] using hbound_n

/-- Complete cyclic correction for an explicit real lift of every generator defect. -/
theorem complete_cycle_phase_correction {N : ℕ} [NeZero N]
    (z : ZMod N → ℂ) (θ : ZMod N → ℝ) (ω : ℝ)
    (hz0 : z 0 = 1) (hz : ∀ k, ‖z k‖ = 1) (hθ0 : θ 0 = 0)
    (hr : ∀ k, Complex.exp (↑(θ k) * Complex.I) =
      z k * z 1 * conj (z (k + 1)))
    (hω : 0 ≤ ω) (hθ : ∀ k, |θ k| ≤ ω) :
    ∃ t : ZMod N, ∀ k,
      ‖z k - ZMod.stdAddChar (-(k * t))‖ ≤ (N - 1 : ℝ) * ω / 2 := by
  obtain ⟨q, hq, hqbound⟩ :=
    cyclic_phase_correction_of_angles z θ ω hz0 hz hθ0 hr hω hθ
  let χ : AddChar (ZMod N) ℂ := AddChar.zmodChar N hq
  let t : ZMod N := -(FinitePoisson.characterEquiv (m := N)).symm χ
  have ht (k : ZMod N) : χ k = ZMod.stdAddChar (-(k * t)) := by
    have h := DFunLike.congr_fun
      ((FinitePoisson.characterEquiv (m := N)).apply_symm_apply χ) k
    simpa only [FinitePoisson.characterEquiv_apply, FinitePoisson.character_apply,
      t, mul_neg, neg_neg, mul_comm] using h.symm
  refine ⟨t, fun k => ?_⟩
  rw [← ht k]
  exact hqbound k

private lemma cyclic_phase_correction_of_chords {N : ℕ} [NeZero N]
    (z : ZMod N → ℂ) (δ : ℝ) (hz0 : z 0 = 1) (hz : ∀ k, ‖z k‖ = 1)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 4)
    (hd : ∀ k, ‖z k * z 1 * conj (z (k + 1)) - 1‖ ≤ δ) :
    ∃ t : ZMod N, ∀ k,
      ‖z k - ZMod.stdAddChar (-(k * t))‖ ≤
        4 * (N - 1 : ℝ) * δ / Real.sqrt 63 := by
  let r : ZMod N → ℂ := fun k => z k * z 1 * conj (z (k + 1))
  let θ : ZMod N → ℝ := fun k => chosenAngle (r k)
  have hrunit (k : ZMod N) : ‖r k‖ = 1 := by
    dsimp [r]
    simp only [norm_mul, Complex.norm_conj, hz, mul_one]
  have hr0 : r 0 = 1 := by
    dsimp [r]
    rw [hz0, zero_add, one_mul, unit_mul_conj (z 1) (hz 1)]
  have hθspec (k : ZMod N) :
      chosenAngle (r k) ∈ Set.Ioc (-Real.pi) Real.pi ∧
        Complex.exp (↑(chosenAngle (r k)) * Complex.I) = r k ∧
        |chosenAngle (r k)| ≤ 8 * ‖r k - 1‖ / Real.sqrt 63 := by
    apply chosenAngle_spec (r k) (hrunit k)
    exact (hd k).trans hδsmall
  have hθ0 : θ 0 = 0 := by
    have hh : |θ 0| ≤ 0 := by
      have hs0 := hθspec 0
      have hs0' := hs0.2.2
      rw [hr0] at hs0'
      change |chosenAngle (r 0)| ≤ 0
      rw [hr0]
      simpa using hs0'
    exact abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))
  have hω : 0 ≤ 8 * δ / Real.sqrt 63 := by positivity
  have hθ (k : ZMod N) : |θ k| ≤ 8 * δ / Real.sqrt 63 := by
    have hh := (hθspec k).2.2
    dsimp [θ] at hh ⊢
    apply hh.trans
    gcongr
    exact hd k
  have hr (k : ZMod N) : Complex.exp (↑(θ k) * Complex.I) =
      z k * z 1 * conj (z (k + 1)) := by
    exact (hθspec k).2.1
  obtain ⟨t, ht⟩ := complete_cycle_phase_correction z θ
    (8 * δ / Real.sqrt 63) hz0 hz hθ0 hr hω hθ
  refine ⟨t, fun k => ?_⟩
  have hfactor :
      (N - 1 : ℝ) * (8 * δ / Real.sqrt 63) / 2 =
        4 * (N - 1 : ℝ) * δ / Real.sqrt 63 := by
    ring
  exact (ht k).trans_eq hfactor

/-- The non-DC source energy in the unnormalized cyclic Fourier convention. -/
def sourceEnergy {N : ℕ} [NeZero N] (f : ZMod N → ℂ) : ℝ :=
  (1 / (N : ℝ)) * ∑ k ∈ (Finset.univ : Finset (ZMod N)).erase 0,
    ‖ZMod.dft f k‖ ^ 2

theorem equal_amplitude_signal_energy_stability
    {N : ℕ} [NeZero N] (f g : ZMod N → ℂ) (m ε : ℝ)
    (hm : 0 < m) (hε : 0 ≤ ε) (hεsmall : ε ≤ m ^ 3 / 4)
    (hdc : ZMod.dft f 0 = ZMod.dft g 0)
    (hF : ∀ k, m ≤ ‖ZMod.dft f k‖)
    (hAmp : ∀ k, ‖ZMod.dft g k‖ = ‖ZMod.dft f k‖)
    (hgen : ∀ k,
      ‖ZMod.dft g k * ZMod.dft g 1 * conj (ZMod.dft g (k + 1)) -
        ZMod.dft f k * ZMod.dft f 1 * conj (ZMod.dft f (k + 1))‖ ≤ ε) :
    ∃ t : ZMod N,
      ∑ x, ‖g x - f (x - t)‖ ^ 2 ≤
        16 * (N - 1 : ℝ) ^ 2 * ε ^ 2 * sourceEnergy f /
          (63 * m ^ 6) := by
  let F : ZMod N → ℂ := ZMod.dft f
  let J : ZMod N → ℂ := ZMod.dft g
  let z : ZMod N → ℂ := fun k => J k / F k
  have hFnz (k : ZMod N) : F k ≠ 0 := by
    have hpos : 0 < ‖F k‖ := lt_of_lt_of_le hm (by simpa [F] using hF k)
    exact norm_pos_iff.mp hpos
  have hFpos (k : ZMod N) : 0 < ‖F k‖ :=
    lt_of_lt_of_le hm (by simpa [F] using hF k)
  have hzF (k : ZMod N) : J k = z k * F k := by
    dsimp [z]
    field_simp [hFnz k]
  have hzunit (k : ZMod N) : ‖z k‖ = 1 := by
    dsimp [z]
    rw [norm_div, hAmp k]
    exact div_self (ne_of_gt (hFpos k))
  have hz0 : z 0 = 1 := by
    dsimp [z, F, J]
    rw [← hdc]
    exact div_self (hFnz 0)
  let D : ℝ := ‖F 1‖ * m ^ 2
  have hD : 0 < D := mul_pos (hFpos 1) (sq_pos_of_pos hm)
  have hDlower : m ^ 3 ≤ D := by
    dsimp [D]
    have h := mul_le_mul_of_nonneg_right (hF 1) (sq_nonneg m)
    simpa [F, pow_succ, mul_comm] using h
  let δ : ℝ := ε / D
  have hm3 : 0 < m ^ 3 := by positivity
  have hδ0 : 0 ≤ δ := by
    dsimp [δ]
    exact div_nonneg hε hD.le
  have hδle : δ ≤ ε / m ^ 3 :=
    div_le_div_of_nonneg_left hε hm3 hDlower
  have hδsmall : δ ≤ 1 / 4 := by
    apply hδle.trans
    apply (div_le_iff₀ hm3).2
    nlinarith [hεsmall]
  have hzdefect (k : ZMod N) :
      ‖z k * z 1 * conj (z (k + 1)) - 1‖ ≤ δ := by
    let P : ℂ := F k * F 1 * conj (F (k + 1))
    have hfac :
        J k * J 1 * conj (J (k + 1)) -
            F k * F 1 * conj (F (k + 1)) =
          P * (z k * z 1 * conj (z (k + 1)) - 1) := by
      rw [hzF k, hzF 1, hzF (k + 1)]
      dsimp [P]
      simp only [map_mul]
      ring
    have hPlower : D ≤ ‖P‖ := by
      dsimp [D, P]
      rw [norm_mul, norm_mul, Complex.norm_conj]
      calc
        ‖F 1‖ * m ^ 2 = m * ‖F 1‖ * m := by ring
        _ ≤ ‖F k‖ * ‖F 1‖ * ‖F (k + 1)‖ := by
          gcongr
          · exact (by simpa [F] using hF k)
          · exact (by simpa [F] using hF (k + 1))
    have hprod : D *
        ‖z k * z 1 * conj (z (k + 1)) - 1‖ ≤ ε := by
      calc
        D * ‖z k * z 1 * conj (z (k + 1)) - 1‖ ≤
            ‖P‖ * ‖z k * z 1 * conj (z (k + 1)) - 1‖ :=
          mul_le_mul_of_nonneg_right hPlower (norm_nonneg _)
        _ = ‖P * (z k * z 1 * conj (z (k + 1)) - 1)‖ :=
          (norm_mul _ _).symm
        _ = ‖J k * J 1 * conj (J (k + 1)) -
            F k * F 1 * conj (F (k + 1))‖ := by rw [hfac]
        _ ≤ ε := by simpa [F, J] using hgen k
    apply (le_div_iff₀ hD).2
    simpa [δ, mul_comm] using hprod
  obtain ⟨t, htphase⟩ :=
    cyclic_phase_correction_of_chords z δ hz0 hzunit hδ0 hδsmall hzdefect
  refine ⟨t, ?_⟩
  let C : ZMod N → ℂ := fun k => ZMod.stdAddChar (-(k * t))
  have hresfactor (k : ZMod N) :
      J k - C k * F k = (z k - C k) * F k := by
    rw [hzF k]
    ring
  have hphase (k : ZMod N) :
      ‖z k - C k‖ ≤ 4 * (N - 1 : ℝ) * δ / Real.sqrt 63 := by
    simpa [C] using htphase k
  let A : ℝ := 4 * (N - 1 : ℝ) * δ / Real.sqrt 63
  have hN1 : (1 : ℝ) ≤ N := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hN0 : 0 < (N : ℝ) := by linarith
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (sub_nonneg.mpr hN1)) hδ0) (Real.sqrt_nonneg _)
  have hA2 : A ^ 2 = 16 * (N - 1 : ℝ) ^ 2 * δ ^ 2 / 63 := by
    dsimp [A]
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 63)]
    ring
  have hresbound (k : ZMod N) :
      ‖J k - C k * F k‖ ^ 2 ≤
        (16 * (N - 1 : ℝ) ^ 2 * δ ^ 2 / 63) * ‖F k‖ ^ 2 := by
    rw [hresfactor, norm_mul]
    have hh := (sq_le_sq₀ (norm_nonneg (z k - C k))
      hA0).2
        (hphase k)
    change ‖z k - C k‖ ^ 2 ≤ A ^ 2 at hh
    rw [hA2] at hh
    simpa [mul_pow] using mul_le_mul_of_nonneg_right hh (sq_nonneg ‖F k‖)
  have hzero : ‖J 0 - C 0 * F 0‖ ^ 2 = 0 := by
    have hC0 : C 0 = 1 := by simp [C]
    rw [hC0, hzF 0, hz0]
    simp
  have hsum :
      ∑ k ∈ (Finset.univ : Finset (ZMod N)).erase 0,
          ‖J k - C k * F k‖ ^ 2 ≤
        (16 * (N - 1 : ℝ) ^ 2 * δ ^ 2 / 63) *
          ∑ k ∈ (Finset.univ : Finset (ZMod N)).erase 0, ‖F k‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    exact hresbound k
  have hdftres (k : ZMod N) :
      ZMod.dft (fun x => g x - f (x - t)) k = J k - C k * F k := by
    dsimp [J, F, C]
    rw [show (fun x => g x - f (x - t)) = g - (fun x => f (x - t)) by rfl]
    rw [map_sub]
    change ZMod.dft g k - ZMod.dft (fun x => f (x - t)) k = _
    rw [dft_translation]
  rw [cyclic_parseval]
  rw [Fintype.expect_eq_sum_div_card, ZMod.card]
  rw [show (∑ x : ZMod N, ‖ZMod.dft (fun x => g x - f (x - t)) x‖ ^ 2) =
      ‖J 0 - C 0 * F 0‖ ^ 2 +
        ∑ k ∈ (Finset.univ : Finset (ZMod N)).erase 0,
          ‖J k - C k * F k‖ ^ 2 by
    simp_rw [hdftres]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ 0)]
    ring]
  rw [hzero, zero_add]
  calc
    _ ≤ ((16 * (N - 1 : ℝ) ^ 2 * δ ^ 2 / 63) *
        ∑ k ∈ (Finset.univ : Finset (ZMod N)).erase 0, ‖F k‖ ^ 2) / N :=
      div_le_div_of_nonneg_right hsum hN0.le
    _ ≤ ((16 * (N - 1 : ℝ) ^ 2 * (ε / m ^ 3) ^ 2 / 63) *
        ∑ k ∈ (Finset.univ : Finset (ZMod N)).erase 0, ‖F k‖ ^ 2) / N := by
      gcongr
    _ = _ := by
      dsimp [sourceEnergy, F]
      field_simp [hN0.ne', hm.ne']

end
end D5.S3.Fourier.GeneratorRowStability
