import D5.S3.Analytic.Laplace.ExponentialHankelPositivity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Set MeasureTheory Matrix
open D5.S3.Analytic.Laplace.ExponentialHankelPositivity

noncomputable section

example (U b : ℝ) (hb : 0 < b) (f : ℝ → ℝ)
    (hc : ContinuousOn f (Ioi U)) (hf : IntegrableOn f (Ioi U)) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      Matrix.PosSemidef (fun i j : Fin (N + 1) =>
        C * Real.exp (-b * U) / (b + (i.val : ℝ) + (j.val : ℝ)) -
          ∫ u in Ioi U, f u * Real.exp (-((i.val + j.val : ℕ) : ℝ) * (u - U)))) ↔
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Ioi U, f u ≤ C * Real.exp (-b * u) := by
  have he : IntegrableOn (fun u : ℝ => Real.exp (-b * u)) (Ioi U) :=
    integrableOn_exp_mul_Ioi (by linarith : -b < 0) U
  have hce : Continuous (fun u : ℝ => Real.exp (-b * u)) := by fun_prop
  have heM := (exponential_hankel_positivity U _ hce.continuousOn he).1
  have hfM := (exponential_hankel_positivity U f hc hf).1
  have hval (k : ℕ) :
      (∫ u in Ioi U, Real.exp (-b * u) * Real.exp (-(k : ℝ) * (u - U))) =
        Real.exp (-b * U) / (b + k) := by
    have heq : (fun u : ℝ => Real.exp (-b * u) * Real.exp (-(k : ℝ) * (u - U))) =
        fun u => Real.exp ((k : ℝ) * U) * Real.exp (-(b + k) * u) := by
      funext u
      simp only [← Real.exp_add]
      congr 1
      ring
    rw [heq, integral_const_mul,
      integral_exp_mul_Ioi (by have := show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k; linarith : -(b + k) < 0) U,
      neg_div_neg_eq, ← mul_div_assoc, ← Real.exp_add]
    congr 1
    congr 1
    ring
  have hfixed (C : ℝ) :
      (∀ N : ℕ,
        Matrix.PosSemidef (fun i j : Fin (N + 1) =>
          C * Real.exp (-b * U) / (b + (i.val : ℝ) + (j.val : ℝ)) -
            ∫ u in Ioi U, f u * Real.exp (-((i.val + j.val : ℕ) : ℝ) * (u - U)))) ↔
      ∀ u ∈ Ioi U, f u ≤ C * Real.exp (-b * u) := by
    have hg : IntegrableOn (fun u => C * Real.exp (-b * u) - f u) (Ioi U) :=
      (he.const_mul C).sub hf
    have hgc : ContinuousOn (fun u => C * Real.exp (-b * u) - f u) (Ioi U) :=
      (continuous_const.mul hce).continuousOn.sub hc
    have hm (N : ℕ) : exponentialHankel U (fun u => C * Real.exp (-b * u) - f u) N =
        fun i j : Fin (N + 1) =>
          C * Real.exp (-b * U) / (b + (i.val : ℝ) + (j.val : ℝ)) -
            ∫ u in Ioi U, f u * Real.exp (-((i.val + j.val : ℕ) : ℝ) * (u - U)) := by
      ext i j
      let k := i.val + j.val
      change (∫ u in Ioi U, (C * Real.exp (-b * u) - f u) *
        Real.exp (-(k : ℝ) * (u - U))) = _
      calc
        _ = ∫ u in Ioi U, C * (Real.exp (-b * u) *
            Real.exp (-(k : ℝ) * (u - U))) - f u * Real.exp (-(k : ℝ) * (u - U)) := by
          apply integral_congr_ae
          filter_upwards [] with u
          ring
        _ = C * (∫ u in Ioi U, Real.exp (-b * u) * Real.exp (-(k : ℝ) * (u - U))) -
            ∫ u in Ioi U, f u * Real.exp (-(k : ℝ) * (u - U)) := by
          rw [integral_sub ((heM k).const_mul C) (hfM k), integral_const_mul]
        _ = _ := by
          rw [hval k]
          simp only [k, Nat.cast_add]
          ring
    simpa only [hm, sub_nonneg] using
      (exponential_hankel_positivity U _ hgc hg).2.2.symm
  constructor
  · rintro ⟨C, hC, hN⟩
    exact ⟨C, hC, (hfixed C).mp hN⟩
  · rintro ⟨C, hC, hcap⟩
    exact ⟨C, hC, (hfixed C).mpr hcap⟩
