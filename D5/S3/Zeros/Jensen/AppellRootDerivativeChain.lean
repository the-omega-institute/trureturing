/- GID: D5/S3/Zeros/Jensen/AppellRootDerivativeChain
   generality: G
   mirror-B: D5/B/S3/Zeros/Jensen/AppellRootDerivativeChain
   mirror-E: none(waiver:conditional-polynomial-estimate)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Derivative]
   utility: none
   digest: A strict operator row budget bounds the derivative chain at each actual root. -/

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Zeros.Jensen.AppellRootDerivativeChain

open Polynomial
open scoped BigOperators

private def jet (P : ℂ[X]) (β : ℂ) (j : ℕ) : ℂ :=
  (derivative^[j] P).eval β

private theorem jet_tail {q : ℕ} {P : ℂ[X]} (hdeg : P.natDegree = q)
    (β : ℂ) {j : ℕ} (hj : q < j) : jet P β j = 0 := by
  simp [jet, iterate_derivative_eq_zero (hdeg ▸ hj)]

private theorem jet_top_ne_zero {q : ℕ} {P : ℂ[X]} (hq : 1 ≤ q)
    (hdeg : P.natDegree = q) (β : ℂ) : jet P β q ≠ 0 := by
  have hp : P ≠ 0 := by
    intro h
    simp [h] at hdeg
    omega
  have hc := eq_C_of_natDegree_le_zero
    (show (derivative^[q] P).natDegree ≤ 0 by
      simpa [hdeg] using natDegree_iterate_derivative P q)
  have hl : P.coeff q ≠ 0 := by
    simpa [← hdeg] using (leadingCoeff_ne_zero.mpr hp)
  rw [jet, hc, eval_C, coeff_iterate_derivative]
  simpa [Nat.descFactorial_self, nsmul_eq_mul] using
    mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero q) : (q.factorial : ℂ) ≠ 0) hl

private theorem ode_jet_recurrence {q : ℕ} {P : ℂ[X]} {β σ : ℂ} {g : ℕ → ℂ}
    (hode : C (σ ^ 2) * P.derivative.derivative - X * P.derivative + C (q : ℂ) * P =
      ∑ m ∈ Finset.Ico 2 q, C (g m) * (derivative^[m + 1] P))
    {k : ℕ} (hk : k ≤ q) :
    σ ^ 2 * jet P β (k + 2) = β * jet P β (k + 1) -
      ((q - k : ℕ) : ℂ) * jet P β k +
        ∑ m ∈ Finset.Ico 2 q, g m * jet P β (k + m + 1) := by
  have hi (n : ℕ) : derivative^[k] (derivative^[n] P) = derivative^[k + n] P :=
    (Function.iterate_add_apply derivative k n P).symm
  have hd := congrArg (fun p : ℂ[X] => (derivative^[k] p).eval β) hode
  rw [iterate_map_add derivative, iterate_derivative_sub] at hd
  rw [mul_comm X P.derivative, iterate_derivative_derivative_mul_X] at hd
  simp only [iterate_derivative_C_mul, iterate_derivative_sum, eval_add, eval_sub,
    eval_mul, eval_C, eval_X, nsmul_eq_mul, eval_natCast, eval_finsetSum, hi] at hd
  change σ ^ 2 * (derivative^[k] P.derivative.derivative).eval β -
    (jet P β (k + 1) * β + (k : ℂ) * jet P β k) + (q : ℂ) * jet P β k =
      ∑ m ∈ Finset.Ico 2 q, g m * (derivative^[k + (m + 1)] P).eval β at hd
  have htwo : derivative^[k] P.derivative.derivative = derivative^[k + 2] P := by
    exact hi 2
  rw [htwo] at hd
  simp only [← Nat.add_assoc] at hd
  rw [Nat.cast_sub hk]
  dsimp [jet] at *
  linear_combination hd

/-- A row of the differentiated equation bounds a higher jet by the same whole-chain maximum. -/
private theorem higher_jet_bound {q k : ℕ} {P : ℂ[X]} {β σ : ℂ} {a M : ℝ} {g : ℕ → ℂ}
    (hσ : σ ≠ 0) (ha : 0 < a)
    (hb : ∀ j : ℕ, ‖jet P β j‖ ≤ M * a ^ j)
    (hrec : σ ^ 2 * jet P β (k + 2) = β * jet P β (k + 1) -
      ((q - k : ℕ) : ℂ) * jet P β k +
        ∑ m ∈ Finset.Ico 2 q, g m * jet P β (k + m + 1)) :
    ‖jet P β (k + 2)‖ / a ^ (k + 2) ≤
      (‖β‖ / (‖σ‖ ^ 2 * a) + (q : ℝ) / (‖σ‖ ^ 2 * a ^ 2) +
        ∑ m ∈ Finset.Ico 2 q, ‖g m‖ * a ^ (m - 1) / ‖σ‖ ^ 2) * M := by
  have hs : 0 < ‖σ‖ ^ 2 := pow_pos (norm_pos_iff.mpr hσ) _
  have hM : 0 ≤ M := by
    simpa using (norm_nonneg (jet P β 0)).trans (hb 0)
  have hcoef : ‖((q - k : ℕ) : ℂ)‖ ≤ (q : ℝ) := by
    rw [Complex.norm_natCast]
    exact_mod_cast Nat.sub_le q k
  have hn : ‖σ‖ ^ 2 * ‖jet P β (k + 2)‖ ≤
      ‖β‖ * (M * a ^ (k + 1)) + (q : ℝ) * (M * a ^ k) +
        ∑ m ∈ Finset.Ico 2 q, ‖g m‖ * (M * a ^ (k + m + 1)) := by
    calc
      ‖σ‖ ^ 2 * ‖jet P β (k + 2)‖ = ‖σ ^ 2 * jet P β (k + 2)‖ := by
        rw [norm_mul, norm_pow]
      _ ≤ ‖β * jet P β (k + 1) - ((q - k : ℕ) : ℂ) * jet P β k‖ +
          ‖∑ m ∈ Finset.Ico 2 q, g m * jet P β (k + m + 1)‖ := by
        rw [hrec]; exact norm_add_le _ _
      _ ≤ (‖β‖ * ‖jet P β (k + 1)‖ + ‖((q - k : ℕ) : ℂ)‖ * ‖jet P β k‖) +
          ∑ m ∈ Finset.Ico 2 q, ‖g m‖ * ‖jet P β (k + m + 1)‖ := by
        simpa only [norm_mul] using add_le_add
          (norm_sub_le (β * jet P β (k + 1)) (((q - k : ℕ) : ℂ) * jet P β k))
          (norm_sum_le (Finset.Ico 2 q) (fun m => g m * jet P β (k + m + 1)))
      _ ≤ _ := by
        apply add_le_add
        · exact add_le_add (mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _))
            (mul_le_mul hcoef (hb _) (norm_nonneg _) (by positivity))
        · exact Finset.sum_le_sum fun m _ =>
            mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _)
  have hfirst : ‖β‖ * (M * a ^ (k + 1)) =
      (‖β‖ / (‖σ‖ ^ 2 * a)) * M * (‖σ‖ ^ 2 * a ^ (k + 2)) := by
    rw [pow_succ, pow_succ]
    field_simp
    ring
  have hsecond : (q : ℝ) * (M * a ^ k) =
      ((q : ℝ) / (‖σ‖ ^ 2 * a ^ 2)) * M * (‖σ‖ ^ 2 * a ^ (k + 2)) := by
    rw [pow_succ, pow_succ]
    field_simp
    ring
  have hterm (m : ℕ) (hm : m ∈ Finset.Ico 2 q) :
      ‖g m‖ * (M * a ^ (k + m + 1)) =
        (‖g m‖ * a ^ (m - 1) / ‖σ‖ ^ 2) * M * (‖σ‖ ^ 2 * a ^ (k + 2)) := by
    have hm2 : 2 ≤ m := (Finset.mem_Ico.mp hm).1
    rw [show k + m + 1 = (k + 2) + (m - 1) by omega, pow_add]
    field_simp
  rw [hfirst, hsecond, Finset.sum_congr rfl hterm,
    ← Finset.sum_mul, ← Finset.sum_mul] at hn
  have hf := (div_le_iff₀ (pow_pos ha (k + 2))).mpr
    ((mul_le_mul_iff_right₀ hs).mp (show ‖σ‖ ^ 2 * ‖jet P β (k + 2)‖ ≤
      ‖σ‖ ^ 2 * ((‖β‖ / (‖σ‖ ^ 2 * a) + (q : ℝ) / (‖σ‖ ^ 2 * a ^ 2) +
        ∑ m ∈ Finset.Ico 2 q, ‖g m‖ * a ^ (m - 1) / ‖σ‖ ^ 2) * M * a ^ (k + 2)) by
      calc
        _ ≤ _ := hn
        _ = _ := by ring))
  exact hf

/-- The actual polynomial operator equation and a strict row budget control the derivative chain
at an actual root, including degree one. No monicity or realness of sigma is required. -/
theorem actual_root_derivative_chain
    {q : ℕ} {P : ℂ[X]} {β σ : ℂ} {a : ℝ} {g : ℕ → ℂ}
    (hq : 1 ≤ q) (hdeg : P.natDegree = q) (hroot : P.eval β = 0)
    (hσ : σ ≠ 0) (ha : 0 < a)
    (hode : C (σ ^ 2) * P.derivative.derivative - X * P.derivative + C (q : ℂ) * P =
      ∑ m ∈ Finset.Ico 2 q, C (g m) * (derivative^[m + 1] P))
    (hrow : ‖β‖ / (‖σ‖ ^ 2 * a) + (q : ℝ) / (‖σ‖ ^ 2 * a ^ 2) +
      (∑ m ∈ Finset.Ico 2 q, ‖g m‖ * a ^ (m - 1) / ‖σ‖ ^ 2) < 1) :
    P.derivative.eval β ≠ 0 ∧ ∀ m : ℕ, 1 ≤ m → m ≤ q →
      ‖(derivative^[m] P).eval β / P.derivative.eval β‖ ≤ a ^ (m - 1) := by
  classical
  let f : ℕ → ℝ := fun j => ‖jet P β j‖ / a ^ j
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.range (q + 1)) f
    ⟨0, by simp⟩
  have hjq : j ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have htop : 0 < f q := div_pos (norm_pos_iff.mpr (jet_top_ne_zero hq hdeg β))
    (pow_pos ha _)
  have hpos : 0 < f j := htop.trans_le (hmax q (by simp))
  have hbound (n : ℕ) : ‖jet P β n‖ ≤ f j * a ^ n := by
    by_cases hn : n ≤ q
    · exact (div_le_iff₀ (pow_pos ha n)).mp (hmax n (by simp [hn]))
    · rw [jet_tail hdeg β (by omega : q < n)]
      rw [norm_zero]
      positivity
  have hj0 : j ≠ 0 := by
    intro heq
    subst j
    simp [f, jet, hroot] at hpos
  have hj1 : j = 1 := by
    by_contra hne
    have hj2 : 2 ≤ j := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj2
    have hb := higher_jet_bound hσ ha hbound
      (ode_jet_recurrence hode (by omega : k ≤ q))
    have hlt := mul_lt_mul_of_pos_right hrow hpos
    rw [Nat.add_comm k 2] at hb
    change f (2 + k) ≤ _ at hb
    rw [one_mul] at hlt
    linarith
  subst j
  have hd : ‖jet P β 1‖ > 0 :=
    (div_pos_iff_of_pos_right (pow_pos ha 1)).mp hpos
  have hdne : jet P β 1 ≠ 0 := norm_pos_iff.mp hd
  have hder : jet P β 1 = P.derivative.eval β := rfl
  refine ⟨hder ▸ hdne, fun m hm hmq => ?_⟩
  rw [← hder, norm_div]
  apply (div_le_iff₀ hd).mpr
  have hb := (div_le_iff₀ (pow_pos ha m)).mp (hmax m (by simp [hmq]))
  have he : f 1 * a ^ m = a ^ (m - 1) * ‖jet P β 1‖ := by
    dsimp [f]
    conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
    field_simp [ha.ne']
    ring
  exact he ▸ hb

end D5.S3.Zeros.Jensen.AppellRootDerivativeChain
