/- GID: D5/S3/Arith/Robin/ActualRobinClockCovariance
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ActualRobinClockCovariance
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Literal finite Robin kernels have ordered activation and exact support. -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.BigOperators.Module
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

/-!
The kernels below are the literal clipped finite kernels, including noninteger
clocks. No covariance, range, monotonicity or convexity envelope is a premise.
The nonlinear relative activation calculation is consumed by the actual
centered covariance theorem. This is an analytic component for arbitrary
clocks, not a realization theorem for the largest equality-inclusive CA sample.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
open scoped BigOperators

namespace D5.S3.Arith.Robin.ActualRobinClockCovariance

/-- The exact reciprocal logarithmic kernel. -/
def g (t : ℝ) : ℝ := 1 / (t * Real.log t)

/-- Literal finite definition: all integer layers from 2 through floor A. -/
def W (A x : ℝ) : ℝ :=
  ∑ k ∈ Icc 2 ⌊A⌋₊, Real.log (k : ℝ) * max (g ((k : ℝ) * x) - g A) 0

private def ambientW (b A x : ℝ) : ℝ :=
  ∑ k ∈ Icc 2 ⌊b⌋₊, Real.log (k : ℝ) * max (g ((k : ℝ) * x) - g A) 0

private theorem g_antitone {s t : ℝ} (hs : 1 < s) (hst : s ≤ t) : g t ≤ g s := by
  have hs0 : 0 < s := by linarith
  have hl : 0 < Real.log s := Real.log_pos hs
  have hlog : Real.log s ≤ Real.log t := Real.log_le_log hs0 hst
  exact one_div_le_one_div_of_le (mul_pos hs0 hl)
    (mul_le_mul hst hlog hl.le (by linarith))

private theorem layer_zero {A x : ℝ} {k : ℕ}
    (hA : 1 < A) (hx : 1 ≤ x) (hk : A ≤ (k : ℝ)) :
    max (g ((k : ℝ) * x) - g A) 0 = 0 := by
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hAx : A ≤ (k : ℝ) * x := hk.trans (by nlinarith)
  exact max_eq_right (sub_nonpos.mpr (g_antitone hA hAx))

private theorem ambient_eq {b A x : ℝ} (hA : 1 < A) (hAb : A ≤ b)
    (hx : 1 ≤ x) : ambientW b A x = W A x := by
  unfold ambientW W
  symm
  apply sum_subset
  · intro k hk
    exact mem_Icc.mpr ⟨(mem_Icc.mp hk).1,
      (mem_Icc.mp hk).2.trans (Nat.floor_mono hAb)⟩
  · intro k hk hnot
    have hfloor : ⌊A⌋₊ < k := by
      have hk2 := (mem_Icc.mp hk).1
      simp only [mem_Icc, not_and, not_le] at hnot
      exact hnot hk2
    rw [layer_zero hA hx (Nat.lt_of_floor_lt hfloor).le, mul_zero]

private theorem clipped_difference {p u v : ℝ} (hvu : v ≤ u) :
    max (p-v) 0 - max (p-u) 0 = min (max (p-v) 0) (u-v) := by
  by_cases hpv : p ≤ v
  · rw [max_eq_right (by linarith : p-v ≤ 0),
      max_eq_right (by linarith : p-u ≤ 0), min_eq_left (by linarith)]
    ring
  · by_cases hpu : p ≤ u
    · rw [max_eq_left (by linarith : 0 ≤ p-v),
        max_eq_right (by linarith : p-u ≤ 0), min_eq_left (by linarith)]
      ring
    · rw [max_eq_left (by linarith : 0 ≤ p-v),
        max_eq_left (by linarith : 0 ≤ p-u), min_eq_right (by linarith)]
      ring

/-- The exact relative activation, in a common finite ambient family. -/
private theorem relative_activation {b A A' x : ℝ}
    (hA' : 1 < A') (horder : A' ≤ A) (hAb : A ≤ b) (hx : 1 ≤ x) :
    W A x - W A' x =
      ∑ k ∈ Icc 2 ⌊b⌋₊, Real.log (k : ℝ) *
        min (max (g ((k : ℝ)*x) - g A) 0) (g A' - g A) := by
  rw [← ambient_eq (hA'.trans_le horder) hAb hx,
    ← ambient_eq hA' (horder.trans hAb) hx]
  unfold ambientW
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro k _
  rw [← mul_sub, clipped_difference (g_antitone hA' horder)]

private theorem W_clock_mono {A A' x : ℝ}
    (hA' : 1 < A') (horder : A' ≤ A) (hx : 1 ≤ x) : W A' x ≤ W A x := by
  rw [← sub_nonneg]
  rw [relative_activation hA' horder le_rfl hx]
  apply sum_nonneg
  intro k hk
  have hk1 : 1 ≤ (k : ℝ) := by
    have hk1n : 1 ≤ k := (by
      exact le_trans (by norm_num) (mem_Icc.mp hk).1)
    exact_mod_cast hk1n
  exact mul_nonneg (Real.log_nonneg hk1)
    (le_min (le_max_right _ _) (sub_nonneg.mpr (g_antitone hA' horder)))

private theorem relative_decreasing {A A' x y : ℝ}
    (hA' : 1 < A') (horder : A' ≤ A) (hx : 1 ≤ x) (hxy : x ≤ y) :
    W A y - W A' y ≤ W A x - W A' x := by
  rw [relative_activation hA' horder le_rfl hx,
    relative_activation hA' horder le_rfl (hx.trans hxy)]
  apply sum_le_sum
  intro k hk
  have hk2 : 2 ≤ (k : ℝ) := by exact_mod_cast (mem_Icc.mp hk).1
  have hk1 : 1 ≤ (k : ℝ) := by linarith
  apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg hk1)
  apply min_le_min_right
  apply max_le_max_right
  apply sub_le_sub_right
  apply g_antitone
  · nlinarith
  · exact mul_le_mul_of_nonneg_left hxy (by positivity)

private theorem W_support {A x : ℝ} (hA : 1 < A) (_hx : 1 ≤ x)
    (hAx : A ≤ 2 * x) : W A x = 0 := by
  unfold W
  apply sum_eq_zero
  intro k hk
  have hk2 : 2 ≤ (k : ℝ) := by exact_mod_cast (mem_Icc.mp hk).1
  have hAx' : A ≤ (k : ℝ)*x := by nlinarith
  rw [max_eq_right (sub_nonpos.mpr (g_antitone hA hAx')), mul_zero]

/-- Unnormalized centered covariance; the empty sample has covariance zero. -/
def centeredCovariance {m : ℕ} (f h : Fin m → ℝ) : ℝ :=
  ∑ i, (f i - (∑ j, f j)/(m : ℝ)) * (h i - (∑ j, h j)/(m : ℝ))

/-- Covariance of the literal clock kernels, without external normalization. -/
def Gamma {m : ℕ} (A : Fin m → ℝ) (x y : ℝ) : ℝ :=
  centeredCovariance (fun i => W (A i) x) (fun i => W (A i) y)

private theorem cov_formula {m : ℕ} (f h : Fin m → ℝ) :
    centeredCovariance f h = (∑ i, f i*h i) - (∑ i, f i)*(∑ i, h i)/(m : ℝ) := by
  by_cases hm : m = 0
  · subst m
    simp [centeredCovariance]
  · have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    unfold centeredCovariance
    simp_rw [sub_mul, mul_sub]
    simp only [sum_sub_distrib, sum_mul, mul_sum, sum_const,
      card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hr : (∑ x, ∑ i, f i * h x) =
        (∑ i, f i) * (∑ x, h x) := by
      simp_rw [← Finset.sum_mul]
      rw [Finset.mul_sum]
    have hleft : (∑ x, f x * ((∑ j, h j) / (m : ℝ))) =
        (∑ x, f x) * ((∑ j, h j) / (m : ℝ)) := by
      rw [← Finset.sum_mul]
    have hright : (∑ x, ((∑ j, f j) / (m : ℝ)) * h x) =
        ((∑ j, f j) / (m : ℝ)) * (∑ x, h x) := by
      rw [← Finset.mul_sum]
    rw [hr, hleft, hright]
    field_simp
    <;> ring

private theorem cov_nonneg {m : ℕ} (f h : Fin m → ℝ) (hmono : Monovary f h) :
    0 ≤ centeredCovariance f h := by
  by_cases hm : m = 0
  · subst m
    simp [centeredCovariance]
  · have hm' : 0 < (m : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hm)
    rw [cov_formula, sub_nonneg, div_le_iff₀ hm']
    simpa only [Fintype.card_fin, mul_comm] using hmono.sum_mul_sum_le_card_mul_sum

private theorem cov_sub_left {m : ℕ} (f f' h : Fin m → ℝ) :
    centeredCovariance (fun i => f i-f' i) h =
      centeredCovariance f h - centeredCovariance f' h := by
  simp only [cov_formula, sub_mul, sum_sub_distrib]
  ring

private theorem cov_sub_right {m : ℕ} (f h h' : Fin m → ℝ) :
    centeredCovariance f (fun i => h i-h' i) =
      centeredCovariance f h - centeredCovariance f h' := by
  simp only [cov_formula, mul_sub, sum_sub_distrib]
  ring

private theorem clock_monovary {m : ℕ} (A : Fin m → ℝ)
    (hA : ∀ i, 1 < A i) {f h : ℝ → ℝ}
    (hf : ∀ s t, 1 < s → s ≤ t → f s ≤ f t)
    (hh : ∀ s t, 1 < s → s ≤ t → h s ≤ h t) :
    Monovary (fun i => f (A i)) (fun i => h (A i)) := by
  intro i j hij
  by_cases hle : A i ≤ A j
  · exact hf _ _ (hA i) hle
  · have hji : A j ≤ A i := le_of_not_ge hle
    exact False.elim ((not_lt_of_ge (hh _ _ (hA j) hji)) hij)

private theorem gamma_nonneg {m : ℕ} (A : Fin m → ℝ) (hA : ∀ i, 1 < A i)
    {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) : 0 ≤ Gamma A x y := by
  apply cov_nonneg
  exact clock_monovary A hA
    (fun _ _ hs hst => W_clock_mono hs hst hx)
    (fun _ _ hs hst => W_clock_mono hs hst hy)

private theorem gamma_decreasing {m : ℕ} (A : Fin m → ℝ) (hA : ∀ i, 1 < A i)
    {x y z : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) (hz : 0 ≤ z) :
    Gamma A y (y+z) ≤ Gamma A x (x+z) := by
  have hxz : 1 ≤ x+z := by linarith
  have hy : 1 ≤ y := hx.trans hxy
  have hyz : 1 ≤ y+z := by linarith
  have h1 : 0 ≤ centeredCovariance (fun i => W (A i) x-W (A i) y)
      (fun i => W (A i) (x+z)) := by
    apply cov_nonneg
    refine clock_monovary A hA
      (f := fun s => W s x - W s y)
      (h := fun s => W s (x+z)) ?_ ?_
    · intro s t hs hst
      have h := relative_decreasing hs hst hx hxy
      linarith
    · exact fun _ _ hs hst => W_clock_mono hs hst hxz
  have h2 : 0 ≤ centeredCovariance (fun i => W (A i) y)
      (fun i => W (A i) (x+z)-W (A i) (y+z)) := by
    apply cov_nonneg
    refine clock_monovary A hA
      (f := fun s => W s y)
      (h := fun s => W s (x+z) - W s (y+z)) ?_ ?_
    · exact fun _ _ hs hst => W_clock_mono hs hst hy
    · intro s t hs hst
      have h := relative_decreasing hs hst hxz (by linarith : x+z ≤ y+z)
      linarith
  rw [cov_sub_left] at h1
  rw [cov_sub_right] at h2
  unfold Gamma
  linarith

/-- Actual covariance signs and variation, and literal support, including m=0.
The decreasing differences follow from relative activation, not convexity of U. -/
theorem actual_clock_covariance {m : ℕ} (A : Fin m → ℝ)
    (hA : ∀ i, 1 < A i) {b x y z : ℝ} (hAb : ∀ i, A i ≤ b)
    (hx : 1 ≤ x) (hxy : x ≤ y) (hz : 0 ≤ z) :
    0 ≤ Gamma A x (x+z) ∧
    0 ≤ Gamma A x (x+z) - Gamma A y (y+z) ∧
    (b ≤ 2*y → Gamma A y (y+z) = 0) := by
  refine ⟨gamma_nonneg A hA hx (by linarith),
    sub_nonneg.mpr (gamma_decreasing A hA hx hxy hz), ?_⟩
  intro hby
  unfold Gamma centeredCovariance
  have hzero : ∀ i, W (A i) y = 0 :=
    fun i => W_support (hA i) (hx.trans hxy) ((hAb i).trans hby)
  simp only [hzero, sum_const_zero, zero_div, sub_self, zero_mul, sum_const_zero]

end D5.S3.Arith.Robin.ActualRobinClockCovariance

#print axioms D5.S3.Arith.Robin.ActualRobinClockCovariance.actual_clock_covariance
