/- GID: D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaSecond/Entropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite binomial entropy bounds from the maximum binomial term. -/

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Finset

namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy

private def term (m : ℕ) (p : ℝ) (j : ℕ) : ℝ :=
  (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j)

private lemma term_succ (m j : ℕ) (p : ℝ) (hj : j < m) :
    term m p (j + 1) * ((j + 1 : ℕ) : ℝ) * (1 - p) =
      term m p j * ((m - j : ℕ) : ℝ) * p := by
  have hc : (m.choose (j + 1) : ℝ) * (j + 1 : ℕ) =
      (m.choose j : ℝ) * (m - j : ℕ) := by
    exact_mod_cast Nat.choose_succ_right_eq m j
  have hd : m - j = m - (j + 1) + 1 := by omega
  dsimp only [term]
  have hp : p ^ (j + 1) = p ^ j * p := pow_succ p j
  have hq : (1 - p) ^ (m - j) = (1 - p) ^ (m - (j + 1)) * (1 - p) := by
    rw [hd, pow_succ]
  rw [hp, hq]
  linear_combination p ^ j * p * (1 - p) ^ (m - (j + 1)) * (1 - p) * hc

private lemma term_maximum (m a : ℕ) (ha : a ≤ m) (ha0 : 0 < a) (ham : a < m)
    (j : ℕ) (hj : j ≤ m) :
    term m ((a : ℝ) / m) j ≤ term m ((a : ℝ) / m) a := by
  have hm : (0 : ℝ) < m := by exact_mod_cast ha0.trans ham
  have hap : (0 : ℝ) < a := by exact_mod_cast ha0
  have haR : (a : ℝ) < m := by exact_mod_cast ham
  let p : ℝ := (a : ℝ) / m
  have hp : 0 < p := div_pos hap hm
  have hp1 : 0 < 1 - p := sub_pos.mpr ((div_lt_one hm).mpr haR)
  have hnonneg (i : ℕ) : 0 ≤ term m p i := by unfold term; positivity
  have hrelation (i : ℕ) (hi : i < m) := term_succ m i p hi
  have hcoeff (i : ℕ) (hi : i ≤ m) :
      ((m - i : ℕ) : ℝ) * p - (i + 1 : ℕ) * (1 - p) =
        (a : ℝ) - i - 1 + p := by
    rw [Nat.cast_sub hi, Nat.cast_add, Nat.cast_one]
    dsimp only [p]
    field_simp
    <;> ring
  have hup (i : ℕ) (hi : i < a) : term m p i ≤ term m p (i + 1) := by
    have him : i < m := hi.trans ham
    have hle : ((i + 1 : ℕ) : ℝ) * (1 - p) ≤ ((m - i : ℕ) : ℝ) * p := by
      have hh : (i : ℝ) + 1 ≤ a := by exact_mod_cast hi
      have := hcoeff i him.le
      linarith
    have hh := mul_le_mul_of_nonneg_left hle (hnonneg i)
    have hr := hrelation i him
    have hd : 0 < ((i + 1 : ℕ) : ℝ) * (1 - p) := by positivity
    apply (mul_le_mul_iff_left₀ hd).mp
    nlinarith only [hh, hr]
  have hdown (i : ℕ) (hai : a ≤ i) (him : i < m) :
      term m p (i + 1) ≤ term m p i := by
    have hle : ((m - i : ℕ) : ℝ) * p ≤ ((i + 1 : ℕ) : ℝ) * (1 - p) := by
      have hh : (a : ℝ) ≤ i := by exact_mod_cast hai
      have := hcoeff i him.le
      have : p < 1 := by linarith
      linarith
    have hh := mul_le_mul_of_nonneg_left hle (hnonneg i)
    have hr := hrelation i him
    have hd : 0 < ((i + 1 : ℕ) : ℝ) * (1 - p) := by positivity
    apply (mul_le_mul_iff_left₀ hd).mp
    nlinarith only [hh, hr]
  change term m p j ≤ term m p a
  rcases le_total j a with hja | haj
  · have hh : ∀ b, j ≤ b → b ≤ a → term m p j ≤ term m p b := by
      intro b hb
      induction b, hb using Nat.le_induction with
      | base => exact fun _ => le_rfl
      | succ b hb ih =>
        intro hba
        exact (ih (by omega)).trans (hup b (by omega))
    exact hh a hja le_rfl
  · have hh : ∀ b, a ≤ b → b ≤ m → term m p b ≤ term m p a := by
      intro b hb
      induction b, hb using Nat.le_induction with
      | base => exact fun _ => le_rfl
      | succ b hb ih =>
        intro hbm
        exact (hdown b hb (by omega)).trans (ih (by omega))
    exact hh j haj hj

/-- A finite binomial coefficient dominates its entropy exponential, with only
the exact maximum-term loss `log (m+1)`. -/
theorem log_choose_ge_binEntropy (m a : ℕ) (ha : a ≤ m) :
    (m : ℝ) * binEntropy ((a : ℝ) / m) - log ((m : ℝ) + 1) ≤
      log (m.choose a : ℝ) := by
  by_cases ha0 : a = 0
  · subst a
    simp only [Nat.cast_zero, zero_div, binEntropy_zero, mul_zero, zero_sub,
      Nat.choose_zero_right, Nat.cast_one, log_one]
    exact neg_nonpos.mpr (log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) m]))
  by_cases ham : a = m
  · subst a
    have hm : (m : ℝ) ≠ 0 := by exact_mod_cast ha0
    simp only [div_self hm, binEntropy_one, mul_zero, zero_sub, Nat.choose_self,
      Nat.cast_one, log_one]
    exact neg_nonpos.mpr (log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) m]))
  have ha0' : 0 < a := Nat.pos_of_ne_zero ha0
  have ham' : a < m := lt_of_le_of_ne ha ham
  have hm : (0 : ℝ) < m := by exact_mod_cast ha0'.trans ham'
  have haR : (0 : ℝ) < a := by exact_mod_cast ha0'
  have haRm : (a : ℝ) < m := by exact_mod_cast ham'
  let p : ℝ := (a : ℝ) / m
  have hp : 0 < p := div_pos haR hm
  have hp1 : 0 < 1 - p := sub_pos.mpr ((div_lt_one hm).mpr haRm)
  have hchoose : (0 : ℝ) < m.choose a := by exact_mod_cast Nat.choose_pos ha
  have hterm : 0 < term m p a := by unfold term; positivity
  have hsum : (∑ j ∈ range (m + 1), term m p j) = 1 := by
    have h := add_pow p (1 - p) m
    simp only [show p + (1 - p) = 1 by ring, one_pow] at h
    calc
      _ = ∑ j ∈ range (m + 1), p ^ j * (1 - p) ^ (m - j) * (m.choose j : ℝ) := by
        apply sum_congr rfl
        intro j hj
        dsimp only [term]
        ring
      _ = 1 := h.symm
  have hmax : 1 ≤ ((m : ℝ) + 1) * term m p a := by
    calc
      1 = ∑ j ∈ range (m + 1), term m p j := hsum.symm
      _ ≤ ∑ _j ∈ range (m + 1), term m p a := by
        apply sum_le_sum
        intro j hj
        exact term_maximum m a ha ha0' ham' j (by simpa using (mem_range.mp hj))
      _ = _ := by simp
  have hlog := log_le_log (by norm_num : (0 : ℝ) < 1) hmax
  have hlogterm : log (term m p a) = log (m.choose a : ℝ) - (m : ℝ) * binEntropy p := by
    dsimp only [term]
    rw [log_mul (mul_pos hchoose (pow_pos hp _)).ne' (pow_pos hp1 _).ne',
      log_mul hchoose.ne' (pow_pos hp _).ne', log_pow, log_pow,
      binEntropy, log_inv, log_inv, Nat.cast_sub ha]
    have hmp : (m : ℝ) * p = a := by dsimp only [p]; field_simp
    linear_combination -(log p - log (1 - p)) * hmp
  rw [log_one, log_mul (by positivity : (m : ℝ) + 1 ≠ 0) hterm.ne', hlogterm] at hlog
  change (m : ℝ) * binEntropy p - log ((m : ℝ) + 1) ≤ _
  linarith

end D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
