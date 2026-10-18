/- GID: D5/S3/Zeros/CriticalPoints/BorceaNonunivalenceRadius
   generality: G
   mirror-B: D5/B/S3/Zeros/CriticalPoints/BorceaNonunivalenceRadius
   mirror-E: none(waiver:open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.Polynomial.Basic]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Zeros/CriticalPoints/BorceaNonunivalenceRadius.conjecture; result=D5/S3/Zeros/CriticalPoints/BorceaNonunivalenceRadius.result; claim=D5/S3/Zeros/CriticalPoints/BorceaNonunivalenceRadius.conjecture
   digest: The root-moment nonunivalence radius conjecture is false. -/

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! A closed-disk counterexample to the root-moment nonunivalence radius. -/

set_option autoImplicit false

namespace D5.S3.Zeros.CriticalPoints.BorceaNonunivalenceRadius

open Polynomial

/-- The `p`-th root moment of the zeros of `F` about `c`, zeros counted with multiplicity. -/
noncomputable def rootMoment (F : ℂ[X]) (p : ℝ) (c : ℂ) : ℝ :=
  ((F.roots.map (fun z => ‖z - c‖ ^ p)).sum / F.natDegree) ^ (1 / p)
/-- Borcea's `σ_p(F)`: the infimum over centres of the root moment. -/
noncomputable def sigma (F : ℂ[X]) (p : ℝ) : ℝ := ⨅ c : ℂ, rootMoment F p c

def conjecture : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ F : ℂ[X], F.natDegree = n → F.eval 0 = 0 →
    ∀ p : ℝ, 1 ≤ p → ∀ r : ℝ, sigma F p * Real.sin (Real.pi / n) < r →
      ¬ Set.InjOn (fun z => F.eval z) (Metric.closedBall (0 : ℂ) r)

private noncomputable def omega : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩
private noncomputable def omega' : ℂ := ⟨-1 / 2, -(Real.sqrt 3 / 2)⟩

private theorem omega_sum : omega + omega' = -1 := by
  apply Complex.ext <;> norm_num [omega, omega']

private theorem omega_mul : omega * omega' = 1 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  apply Complex.ext <;> simp [omega, omega', Complex.mul_re, Complex.mul_im]
  all_goals nlinarith

private theorem omega_norm : ‖omega‖ = 1 := by
  have h : omega = (UpperHalfPlane.ρ : ℂ) := by
    apply Complex.ext <;> rfl
  rw [h]
  exact UpperHalfPlane.norm_ρ

private theorem omega'_norm : ‖omega'‖ = 1 := by
  have h : omega' = starRingEnd ℂ omega := by
    apply Complex.ext <;> simp [omega, omega']
  rw [h, Complex.norm_conj, omega_norm]

private theorem factorization : (X - X ^ 4 : ℂ[X]) =
    -(X * (X - C 1) * (X - C omega) * (X - C omega')) := by
  have ha : (C omega + C omega' : ℂ[X]) = -1 := by
    rw [← map_add, omega_sum]; simp
  have hb : (C omega * C omega' : ℂ[X]) = 1 := by
    rw [← map_mul, omega_mul]; simp
  have hq : (X - C omega) * (X - C omega') = (X ^ 2 + X + 1 : ℂ[X]) := by
    linear_combination -X * ha + hb
  calc
    (X - X ^ 4 : ℂ[X]) = -(X * (X - C 1) * (X ^ 2 + X + 1)) := by simp only [map_one]; ring
    _ = _ := by rw [← hq]; ring

private theorem explicit_roots : (X - X ^ 4 : ℂ[X]).roots = {0, 1, omega, omega'} := by
  rw [factorization, roots_neg,
    roots_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero X_ne_zero (X_sub_C_ne_zero _))
      (X_sub_C_ne_zero _)) (X_sub_C_ne_zero _)),
    roots_mul (mul_ne_zero (mul_ne_zero X_ne_zero (X_sub_C_ne_zero _)) (X_sub_C_ne_zero _)),
    roots_mul (mul_ne_zero X_ne_zero (X_sub_C_ne_zero _)),
    roots_X, roots_X_sub_C, roots_X_sub_C, roots_X_sub_C]
  rfl

private theorem degree_four : (X - X ^ 4 : ℂ[X]).natDegree = 4 := by
  rw [natDegree_sub_eq_right_of_natDegree_lt]
  · simp
  · simp

private theorem sigma_bound : sigma (X - X ^ 4) 1 ≤ 3 / 4 := by
  have hb : BddBelow (Set.range (rootMoment (X - X ^ 4) 1)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨c, rfl⟩
    apply Real.rpow_nonneg
    apply div_nonneg
    · exact Multiset.sum_nonneg (by
        intro x hx
        obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp hx
        exact Real.rpow_nonneg (norm_nonneg _) _)
    · exact Nat.cast_nonneg _
  calc
    sigma (X - X ^ 4) 1 ≤ rootMoment (X - X ^ 4) 1 0 := ciInf_le hb 0
    _ = 3 / 4 := by
      simp [rootMoment, explicit_roots, degree_four, omega_norm, omega'_norm]
      <;> norm_num

private theorem radius_bound : sigma (X - X ^ 4) 1 * Real.sin (Real.pi / 4) < 5 / 8 := by
  rw [Real.sin_pi_div_four]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  have ht : Real.sqrt 2 < 5 / 3 := by nlinarith
  calc
    sigma (X - X ^ 4) 1 * (Real.sqrt 2 / 2) ≤ (3 / 4) * (Real.sqrt 2 / 2) :=
      mul_le_mul_of_nonneg_right sigma_bound (by positivity)
    _ < 5 / 8 := by nlinarith

private theorem injective_disk :
    Set.InjOn (fun z : ℂ => (X - X ^ 4 : ℂ[X]).eval z)
      (Metric.closedBall 0 (5 / 8)) := by
  intro z hz w hw he
  have hz' : ‖z‖ ≤ (5 / 8 : ℝ) := by simpa using hz
  have hw' : ‖w‖ ≤ (5 / 8 : ℝ) := by simpa using hw
  have hn : ‖z ^ 3 + z ^ 2 * w + z * w ^ 2 + w ^ 3‖ < 1 := by
    calc
      ‖z ^ 3 + z ^ 2 * w + z * w ^ 2 + w ^ 3‖ ≤
          ‖z ^ 3‖ + ‖z ^ 2 * w‖ + ‖z * w ^ 2‖ + ‖w ^ 3‖ := by
        calc
          _ ≤ ‖z ^ 3 + z ^ 2 * w + z * w ^ 2‖ + ‖w ^ 3‖ := norm_add_le _ _
          _ ≤ (‖z ^ 3 + z ^ 2 * w‖ + ‖z * w ^ 2‖) + ‖w ^ 3‖ := by
            gcongr; exact norm_add_le _ _
          _ ≤ _ := by gcongr; exact norm_add_le _ _
      _ ≤ (5 / 8 : ℝ) ^ 3 + (5 / 8) ^ 2 * (5 / 8) +
          (5 / 8) * (5 / 8) ^ 2 + (5 / 8) ^ 3 := by
        simp only [norm_pow, norm_mul]
        gcongr
      _ < 1 := by norm_num
  have he' : z - z ^ 4 = w - w ^ 4 := by simpa using he
  have hf : (z - w) * (1 - (z ^ 3 + z ^ 2 * w + z * w ^ 2 + w ^ 3)) = 0 := by
    linear_combination he'
  rcases mul_eq_zero.mp hf with h | h
  · exact sub_eq_zero.mp h
  · have hsum : z ^ 3 + z ^ 2 * w + z * w ^ 2 + w ^ 3 = 1 := (sub_eq_zero.mp h).symm
    rw [hsum, norm_one] at hn
    exact (lt_irrefl _ hn).elim

theorem result : ¬ conjecture := by
  intro h
  exact h 4 (by norm_num) (X - X ^ 4) degree_four (by simp) 1 (by norm_num)
    (5 / 8) radius_bound injective_disk

end D5.S3.Zeros.CriticalPoints.BorceaNonunivalenceRadius
