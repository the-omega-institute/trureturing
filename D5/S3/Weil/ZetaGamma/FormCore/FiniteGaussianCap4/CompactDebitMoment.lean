/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/CompactDebitMoment
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Actual signed compact debit moments reduce to the proved H and J integrals. -/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactHalfMoment
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.IntegerExpMoment
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.Cap4CompactMultiplier
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace FiniteGaussianCap475
open MeasureTheory Set

/-- The actual moment of the signed compact multiplier; this is an integral,
not the algebraic expression which will be proved to equal it. -/
def debitMoment (m : ℕ) : ℝ :=
  ∫ x : ℝ in 0..6,
    x ^ (7 / 2 : ℝ) * FiniteGaussianCap4.compactDebit x *
      Real.exp (-2 * x) * x ^ m

private theorem half_product (m : ℕ) {x : ℝ} (hx : 0 < x) :
    x ^ (7 / 2 : ℝ) * x ^ 2 * x ^ m = x ^ ((m : ℝ) + 11 / 2) := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_natCast x m,
    ← Real.rpow_add hx, ← Real.rpow_add hx]
  congr 1
  norm_num <;> ring

private theorem tail_products {x : ℝ} (hx : 0 < x) :
    x ^ (7 / 2 : ℝ) * (x / Real.pi) ^ (5 / 2 : ℝ) =
        x ^ 6 / (Real.pi ^ 2 * Real.sqrt Real.pi) ∧
    x ^ (7 / 2 : ℝ) * (x / Real.pi) ^ (-7 / 2 : ℝ) =
        Real.pi ^ 3 * Real.sqrt Real.pi := by
  have hp5 : Real.pi ^ (5 / 2 : ℝ) =
      Real.pi ^ 2 * Real.sqrt Real.pi := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast Real.pi 2,
      ← Real.rpow_add Real.pi_pos]
    norm_num
  have hp7 : Real.pi ^ (7 / 2 : ℝ) =
      Real.pi ^ 3 * Real.sqrt Real.pi := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast Real.pi 3,
      ← Real.rpow_add Real.pi_pos]
    norm_num
  constructor
  · calc
      x ^ (7 / 2 : ℝ) * (x / Real.pi) ^ (5 / 2 : ℝ) =
          (x ^ (7 / 2 : ℝ) * x ^ (5 / 2 : ℝ)) /
            Real.pi ^ (5 / 2 : ℝ) := by
        rw [Real.div_rpow hx.le Real.pi_pos.le]
        ring
      _ = x ^ 6 / (Real.pi ^ 2 * Real.sqrt Real.pi) := by
        rw [← Real.rpow_add hx, hp5]
        norm_num
  · calc
      x ^ (7 / 2 : ℝ) * (x / Real.pi) ^ (-7 / 2 : ℝ) =
          (x ^ (7 / 2 : ℝ) * x ^ (-7 / 2 : ℝ)) /
            Real.pi ^ (-7 / 2 : ℝ) := by
        rw [Real.div_rpow hx.le Real.pi_pos.le]
        ring
      _ = Real.pi ^ (7 / 2 : ℝ) := by
        rw [← Real.rpow_add hx,
          show (7 / 2 : ℝ) + -7 / 2 = 0 by norm_num,
          Real.rpow_zero,
          show (-7 / 2 : ℝ) = -(7 / 2 : ℝ) by ring,
          Real.rpow_neg Real.pi_pos.le]
        simp
      _ = _ := hp7

private theorem debit_integrand_below (m : ℕ) {x : ℝ}
    (hx : 0 < x) (hx6 : x < 6) (hxpi : x ≤ Real.pi) :
    x ^ (7 / 2 : ℝ) * FiniteGaussianCap4.compactDebit x *
        Real.exp (-2 * x) * x ^ m =
      (x ^ ((m : ℝ) + 11 / 2) * Real.exp (-2 * x)) / 10 := by
  simp only [FiniteGaussianCap4.compactDebit, if_pos (show 0 < x ∧ x < 6 from ⟨hx, hx6⟩),
    FiniteGaussianCap4.capWeight, if_neg (not_lt_of_ge hxpi), sub_zero]
  calc
    x ^ (7 / 2 : ℝ) * (x ^ 2 / 10) * Real.exp (-2 * x) * x ^ m =
        (x ^ (7 / 2 : ℝ) * x ^ 2 * x ^ m) * Real.exp (-2 * x) / 10 := by ring
    _ = _ := by rw [half_product m hx]

private theorem debit_integrand_above (m : ℕ) {x : ℝ}
    (hx : Real.pi < x) (hx6 : x < 6) :
    x ^ (7 / 2 : ℝ) * FiniteGaussianCap4.compactDebit x *
        Real.exp (-2 * x) * x ^ m =
      (x ^ ((m : ℝ) + 11 / 2) * Real.exp (-2 * x)) / 10 -
        (x ^ (m + 6) * Real.exp (-2 * x)) /
          (Real.pi ^ 2 * Real.sqrt Real.pi) +
        (4 * Real.pi ^ 3 * Real.sqrt Real.pi) *
          (x ^ m * Real.exp (-2 * x)) := by
  have hx0 : 0 < x := Real.pi_pos.trans hx
  obtain ⟨h5, h7⟩ := tail_products hx0
  simp only [FiniteGaussianCap4.compactDebit, if_pos (show 0 < x ∧ x < 6 from ⟨hx0, hx6⟩),
    FiniteGaussianCap4.capWeight, if_pos hx]
  calc
    x ^ (7 / 2 : ℝ) *
        (x ^ 2 / 10 - ((x / Real.pi) ^ (5 / 2 : ℝ) -
          4 * (x / Real.pi) ^ (-7 / 2 : ℝ))) * Real.exp (-2 * x) * x ^ m =
      (x ^ (7 / 2 : ℝ) * x ^ 2 * x ^ m) * Real.exp (-2 * x) / 10 -
        (x ^ (7 / 2 : ℝ) * (x / Real.pi) ^ (5 / 2 : ℝ)) *
          (x ^ m * Real.exp (-2 * x)) +
        4 * (x ^ (7 / 2 : ℝ) * (x / Real.pi) ^ (-7 / 2 : ℝ)) *
          (x ^ m * Real.exp (-2 * x)) := by ring
    _ = _ := by
      rw [half_product m hx0, h5, h7]
      simp only [pow_add]
      ring

/-- Genuine integrability and the signed moment identity. The jump at pi and
the support endpoints are handled on open intervals and hence have no effect
on either integrability or the integral. No matrix enclosure is assumed. -/
theorem debitMoment_formula (m : ℕ) :
    IntervalIntegrable (fun x : ℝ =>
      x ^ (7 / 2 : ℝ) * FiniteGaussianCap4.compactDebit x *
        Real.exp (-2 * x) * x ^ m) volume 0 6 ∧
    debitMoment m = H m / 10 -
      J (m + 6) / (Real.pi ^ 2 * Real.sqrt Real.pi) +
      (4 * Real.pi ^ 3 * Real.sqrt Real.pi) * J m := by
  let f : ℝ → ℝ := fun x =>
    x ^ (7 / 2 : ℝ) * FiniteGaussianCap4.compactDebit x *
      Real.exp (-2 * x) * x ^ m
  let h : ℝ → ℝ := fun x =>
    x ^ ((m : ℝ) + 11 / 2) * Real.exp (-2 * x)
  let j : ℕ → ℝ → ℝ := fun n x => x ^ n * Real.exp (-2 * x)
  let d : ℝ := Real.pi ^ 2 * Real.sqrt Real.pi
  let c : ℝ := 4 * Real.pi ^ 3 * Real.sqrt Real.pi
  have hpi6 : Real.pi ≤ (6 : ℝ) := by linarith [Real.pi_lt_four]
  have hh : Continuous h := by
    dsimp only [h]
    exact (Real.continuous_rpow_const (by positivity)).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hj (n : ℕ) : Continuous (j n) := by dsimp only [j]; fun_prop
  have helo : (Ioo (0 : ℝ) Real.pi).EqOn f (fun x => h x / 10) := by
    intro x hx
    exact debit_integrand_below m hx.1 (hx.2.trans_le hpi6) hx.2.le
  have hehi : (Ioo Real.pi (6 : ℝ)).EqOn f
      (fun x => h x / 10 - j (m + 6) x / d + c * j m x) := by
    intro x hx
    exact debit_integrand_above m hx.1 hx.2
  have hilo : IntervalIntegrable f volume 0 Real.pi := by
    apply ((hh.intervalIntegrable 0 Real.pi).div_const 10).congr_uIoo
    rw [uIoo_of_le Real.pi_pos.le]
    exact helo.symm
  have hih0 : IntervalIntegrable (fun x => h x / 10) volume Real.pi 6 :=
    (hh.intervalIntegrable Real.pi 6).div_const 10
  have hij6 : IntervalIntegrable (fun x => j (m + 6) x / d) volume Real.pi 6 :=
    ((hj (m + 6)).intervalIntegrable Real.pi 6).div_const d
  have hij : IntervalIntegrable (fun x => c * j m x) volume Real.pi 6 :=
    ((hj m).intervalIntegrable Real.pi 6).const_mul c
  have hihi : IntervalIntegrable f volume Real.pi 6 := by
    apply ((hih0.sub hij6).add hij).congr_uIoo
    rw [uIoo_of_le hpi6]
    exact hehi.symm
  refine ⟨hilo.trans hihi, ?_⟩
  change (∫ x in (0 : ℝ)..6, f x) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals hilo hihi,
    intervalIntegral.integral_congr_Ioo_of_le Real.pi_pos.le helo,
    intervalIntegral.integral_congr_Ioo_of_le hpi6 hehi,
    intervalIntegral.integral_div,
    intervalIntegral.integral_add (hih0.sub hij6) hij,
    intervalIntegral.integral_sub hih0 hij6,
    intervalIntegral.integral_div, intervalIntegral.integral_div,
    intervalIntegral.integral_const_mul]
  have hjoin : (∫ x : ℝ in (0 : ℝ)..Real.pi, h x) +
      (∫ x : ℝ in Real.pi..6, h x) = (∫ x : ℝ in (0 : ℝ)..6, h x) :=
    intervalIntegral.integral_add_adjacent_intervals
      (hh.intervalIntegrable 0 Real.pi) (hh.intervalIntegrable Real.pi 6)
  change (∫ x in (0 : ℝ)..Real.pi, h x) +
    (∫ x in Real.pi..6, h x) = H m at hjoin
  change (∫ x in (0 : ℝ)..Real.pi, h x) / 10 +
    ((∫ x in Real.pi..6, h x) / 10 - J (m + 6) / d + c * J m) = _
  dsimp only [d, c]
  linear_combination (1 / 10 : ℝ) * hjoin

end FiniteGaussianCap475
