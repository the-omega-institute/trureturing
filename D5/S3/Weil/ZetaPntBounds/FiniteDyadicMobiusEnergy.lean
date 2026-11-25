/- GID: D5/S3/Weil/ZetaPntBounds/FiniteDyadicMobiusEnergy
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaPntBounds/FiniteDyadicMobiusEnergy
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: The finite rational dyadic Möbius shell energy gives a cofinal criterion for RH. -/

import D5.S3.Weil.ZetaPntBounds.ReciprocalMoebiusDyadicShell
import D5.S3.Weil.ZetaPntBounds.MobiusShortAverage
import D5.S3.Weil.Mertens.Cryptids.VonMangoldtCount.Foundation
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Tactic

/-!
# Finite dyadic Möbius energy

At an integer cutoff the absolute shell mass is a finite sum over unit cells.
The energy has rational coefficients and counts pairs of overlapping shells.
Finite Abel summation gives the upper estimate from a zero-free half-plane.
The uniform zeta-zero obstruction gives the converse.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset Filter MeasureTheory
open scoped BigOperators Topology

namespace D5.S3.Weil.ZetaPntBounds.FiniteDyadicMobiusEnergy

open D5.S3.Arith.MoebiusLogarithmic
  (reciprocalSum abs_reciprocalSum_le_one)
open D5.S3.Weil.ZetaPntBounds.MobiusShortAverage
  (ordinary_mobius_prefix_of_zero_free)
open D5.S3.Weil.ZetaPntBounds.ReciprocalMoebiusFloorInverse
  (bounded_intervalIntegrable measurable_reciprocalSum dyadicReciprocalMoebiusShell_lower)
open ConjectureMachines.Semantics.Riemann.VonMangoldtCount
  (zero_lt_re_of_isNontrivialZetaZero)

def mobiusReciprocal (n : ℕ) : ℚ :=
  (ArithmeticFunction.moebius n : ℚ) / n

/-- The reciprocal Möbius sum on the integer shell `j / 2 < n ≤ j`. -/
def d (j : ℕ) : ℚ :=
  ∑ n ∈ Ioc (j / 2) j, mobiusReciprocal n

/-- The rational energy on the cells with left endpoints `1 ≤ j < P`. -/
def energy (P : ℕ) : ℚ :=
  ∑ j ∈ Ico 1 P, (d j) ^ 2

/-- The number of cells below `P` containing both terms of the pair. -/
def bandWeight (P m n : ℕ) : ℕ :=
  min P (2 * min m n) - max m n

private theorem cast_d (j : ℕ) :
    (d j : ℝ) = ∑ n ∈ Ioc (j / 2) j, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) := by
  simp only [d, mobiusReciprocal, Rat.cast_sum, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]

private theorem energy_nonneg (P : ℕ) : 0 ≤ energy P :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem shell_eq_d_on_cell {j : ℕ} {u : ℝ}
    (hu : u ∈ Set.Ico (j : ℝ) ((j : ℝ) + 1)) :
    reciprocalSum u - reciprocalSum (u / 2) = (d j : ℝ) := by
  have hf : ⌊u⌋₊ = j := (Nat.floor_eq_iff ((Nat.cast_nonneg j).trans hu.1)).2 hu
  have hf₂ : ⌊u / 2⌋₊ = j / 2 := by rw [Nat.floor_div_ofNat u 2, hf]
  simp only [reciprocalSum, hf, hf₂, cast_d]
  have h := Finset.sum_Ioc_consecutive
    (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) / (n : ℝ))
    (Nat.zero_le (j / 2)) (show j / 2 ≤ j by omega)
  linarith only [h]

private theorem shellAbs_intervalIntegrable {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => |reciprocalSum u - reciprocalSum (u / 2)|) volume a b := by
  refine bounded_intervalIntegrable (C := 2) hab
    (measurable_reciprocalSum.sub
      (measurable_reciprocalSum.comp (measurable_id.div_const 2))).abs ?_
  intro u _
  rw [abs_abs]
  exact (abs_sub _ _).trans
    (by linarith [abs_reciprocalSum_le_one u, abs_reciprocalSum_le_one (u / 2)])

/-- Each unit cell contributes exactly the absolute value of its rational shell. -/
theorem shell_mass_eq_sum_abs {P : ℕ} (hP : 1 ≤ P) :
    (∫ u in (1 : ℝ)..(P : ℝ), |reciprocalSum u - reciprocalSum (u / 2)|) =
      ∑ j ∈ Ico 1 P, |(d j : ℝ)| := by
  let f : ℝ → ℝ := fun u => |reciprocalSum u - reciprocalSum (u / 2)|
  have hcells := intervalIntegral.sum_integral_adjacent_intervals_Ico
    (μ := volume) (f := f) (a := fun j : ℕ => (j : ℝ)) hP
    (fun j _ => shellAbs_intervalIntegrable (by exact_mod_cast Nat.le_succ j))
  change (∫ u in (1 : ℝ)..(P : ℝ), f u) = _
  calc
    _ = ∑ j ∈ Ico 1 P, ∫ u in (j : ℝ)..((j : ℝ) + 1), f u := by
      simpa only [Nat.cast_one, Nat.cast_add] using hcells.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      have hle : (j : ℝ) ≤ (j : ℝ) + 1 := by linarith
      calc
        _ = ∫ _u in (j : ℝ)..((j : ℝ) + 1), |(d j : ℝ)| := by
          apply intervalIntegral.integral_congr_Ioo_of_le hle
          intro u hu
          exact congrArg abs (shell_eq_d_on_cell ⟨hu.1.le, hu.2⟩)
        _ = _ := by simp only [intervalIntegral.integral_const, add_sub_cancel_left, one_smul]

/-- The exact finite Cauchy–Schwarz bound uses the number `P - 1` of cells. -/
theorem shell_mass_sq_le {P : ℕ} (hP : 1 ≤ P) :
    (∫ u in (1 : ℝ)..(P : ℝ), |reciprocalSum u - reciprocalSum (u / 2)|) ^ 2 ≤
      ((P - 1 : ℕ) : ℝ) * (energy P : ℝ) := by
  rw [shell_mass_eq_sum_abs hP]
  simpa only [Nat.card_Ico, sq_abs, energy, Rat.cast_sum, Rat.cast_pow] using
    (sq_sum_le_card_mul_sum_sq (s := Ico 1 P) (f := fun j => |(d j : ℝ)|))

/-- The rational kernel expansion counts simultaneous membership of each pair. -/
theorem energy_eq_banded_sum (P : ℕ) :
    energy P = ∑ m ∈ Ico 1 P, ∑ n ∈ Ico 1 P,
      (bandWeight P m n : ℚ) * (mobiusReciprocal m * mobiusReciprocal n) := by
  classical
  let cells := Ico 1 P
  let term (j n : ℕ) : ℚ := if n ∈ Ioc (j / 2) j then mobiusReciprocal n else 0
  have hd (j : ℕ) (hj : j ∈ cells) : d j = ∑ n ∈ cells, term j n := by
    change (∑ n ∈ Ioc (j / 2) j, mobiusReciprocal n) =
      ∑ n ∈ cells, if n ∈ Ioc (j / 2) j then mobiusReciprocal n else 0
    rw [← Finset.sum_filter]
    apply Finset.sum_congr ?_ (fun _ _ => rfl)
    ext n
    have hjP := (Finset.mem_Ico.mp hj).2
    simp only [cells, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ico]
    omega
  have hpair (m n : ℕ) (hm : m ∈ cells) :
      (∑ j ∈ cells, term j m * term j n) =
        (bandWeight P m n : ℚ) * (mobiusReciprocal m * mobiusReciprocal n) := by
    have hset :
        cells.filter (fun j => m ∈ Ioc (j / 2) j ∧ n ∈ Ioc (j / 2) j) =
          Ico (max m n) (min P (2 * min m n)) := by
      ext j
      have hm₁ := (Finset.mem_Ico.mp hm).1
      simp only [cells, Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ioc,
        mul_min, max_le_iff, lt_min_iff]
      omega
    calc
      _ = ∑ j ∈ cells, if m ∈ Ioc (j / 2) j ∧ n ∈ Ioc (j / 2) j then
          mobiusReciprocal m * mobiusReciprocal n else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hmj : m ∈ Ioc (j / 2) j <;> by_cases hnj : n ∈ Ioc (j / 2) j <;>
          simp only [term, hmj, hnj, true_and, false_and, and_true, and_false,
            if_true, if_false, mul_zero, zero_mul]
      _ = _ := by
        rw [← Finset.sum_filter, hset, Finset.sum_const, nsmul_eq_mul, Nat.card_Ico, bandWeight]
  calc
    energy P = ∑ j ∈ cells, ∑ m ∈ cells, ∑ n ∈ cells, term j m * term j n := by
      change (∑ j ∈ cells, (d j)^2) = _
      apply Finset.sum_congr rfl
      intro j hj
      rw [hd j hj, pow_two, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun _ _ => Finset.mul_sum _ _ _)
    _ = ∑ m ∈ cells, ∑ j ∈ cells, ∑ n ∈ cells, term j m * term j n := Finset.sum_comm
    _ = ∑ m ∈ cells, ∑ n ∈ cells, ∑ j ∈ cells, term j m * term j n :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := Finset.sum_congr rfl (fun m hm =>
      Finset.sum_congr rfl (fun n _ => hpair m n hm))

theorem bandWeight_eq_zero_of_separated {P m n : ℕ}
    (h : 2 * min m n ≤ max m n) : bandWeight P m n = 0 :=
  Nat.sub_eq_zero_of_le ((min_le_right P (2 * min m n)).trans h)

-- The reciprocal weight is nonnegative everywhere. Its monotonicity is needed
-- only at the interior indices, which are positive even for a shell starting at zero.
private theorem finite_abel_bound (f w : ℕ → ℝ) {a b : ℕ} (hab : a < b) {B : ℝ}
    (hprefix : ∀ n ≤ b, |∑ k ∈ range (n + 1), f k| ≤ B)
    (hw : ∀ n, 0 ≤ w n) (hdec : ∀ n, a < n → w (n + 1) ≤ w n) :
    |∑ n ∈ Ioc a b, w n * f n| ≤ 2 * B * w (a + 1) := by
  let S (n : ℕ) : ℝ := ∑ k ∈ range (n + 1), f k
  let Δ (n : ℕ) : ℝ := w n - w (n + 1)
  have hΔ (n : ℕ) (hn : n ∈ Ioc a (b - 1)) : 0 ≤ Δ n :=
    sub_nonneg.mpr (hdec n (Finset.mem_Ioc.mp hn).1)
  have hset : Ioc a (b - 1) = Ico (a + 1) b := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  have htel : (∑ n ∈ Ioc a (b - 1), Δ n) = w (a + 1) - w b := by
    rw [hset]
    simpa only [Δ, neg_sub_neg] using
      (Finset.sum_Ico_sub (fun n => -w n) (show a + 1 ≤ b by omega))
  have habel := Finset.sum_Ioc_by_parts w f hab
  simp only [smul_eq_mul] at habel
  change (∑ n ∈ Ioc a b, w n * f n) =
    w b * S b - w (a + 1) * S a -
      ∑ n ∈ Ioc a (b - 1), (w (n + 1) - w n) * S n at habel
  have hsign : (∑ n ∈ Ioc a (b - 1), (w (n + 1) - w n) * S n) =
      -(∑ n ∈ Ioc a (b - 1), Δ n * S n) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun n _ => by dsimp only [Δ]; ring)
  have hterm (v : ℕ) (n : ℕ) (hn : n ≤ b) : |w v * S n| ≤ w v * B := by
    rw [abs_mul, abs_of_nonneg (hw v)]
    exact mul_le_mul_of_nonneg_left (hprefix n hn) (hw v)
  have hsum : |∑ n ∈ Ioc a (b - 1), Δ n * S n| ≤ (w (a + 1) - w b) * B := by
    rw [← htel, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
    intro n hn
    rw [abs_mul, abs_of_nonneg (hΔ n hn)]
    exact mul_le_mul_of_nonneg_left (hprefix n (by have := (Finset.mem_Ioc.mp hn).2; omega))
      (hΔ n hn)
  rw [habel, hsign, sub_neg_eq_add]
  calc
    _ ≤ |w b * S b| + |w (a + 1) * S a| + |∑ n ∈ Ioc a (b - 1), Δ n * S n| :=
      (abs_add_le _ _).trans (add_le_add_left (abs_sub _ _) _)
    _ ≤ w b * B + w (a + 1) * B + (w (a + 1) - w b) * B :=
      add_le_add (add_le_add (hterm b b le_rfl) (hterm (a + 1) a hab.le)) hsum
    _ = _ := by ring

private theorem abs_d_le_of_prefix {D α : ℝ} (hD : 0 ≤ D) (hα : 0 ≤ α)
    (hprefix : ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Icc 1 N, (ArithmeticFunction.moebius n : ℝ)| ≤ D * (N : ℝ)^α)
    {j : ℕ} (hj : 1 ≤ j) :
    |(d j : ℝ)| ≤ 4 * D * (j : ℝ)^(α - 1) := by
  let a := j / 2
  let f : ℕ → ℝ := fun n => (ArithmeticFunction.moebius n : ℝ)
  let w (n : ℕ) : ℝ := 1 / (n : ℝ)
  have haj : a < j := Nat.div_lt_self (by omega) (by decide)
  have hj₀ : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hB : 0 ≤ D * (j : ℝ)^α := mul_nonneg hD (Real.rpow_nonneg hj₀.le _)
  have hM (N : ℕ) (hNj : N ≤ j) :
      |∑ n ∈ range (N + 1), f n| ≤ D * (j : ℝ)^α := by
    have hset : range (N + 1) = Icc 1 N ∪ {0} := by
      ext n
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton]
      omega
    rw [hset, Finset.sum_union (by simp)]
    simp only [Finset.sum_singleton, f, ArithmeticFunction.map_zero, Int.cast_zero, add_zero]
    by_cases hN : 1 ≤ N
    · exact (hprefix N hN).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg N) (by exact_mod_cast hNj) hα) hD)
    · have hN₀ : N = 0 := by omega
      simpa [hN₀] using hB
  have hw (n : ℕ) : 0 ≤ w n := one_div_nonneg.mpr (Nat.cast_nonneg n)
  have hdec (n : ℕ) (hn : a < n) : w (n + 1) ≤ w n := by
    dsimp only [w]
    exact one_div_le_one_div_of_le (by exact_mod_cast (show 0 < n by omega))
      (by exact_mod_cast Nat.le_succ n)
  have hhalf : (j : ℝ) ≤ 2 * ((a + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show j ≤ 2 * (a + 1) by dsimp only [a]; omega)
  have hwle : w (a + 1) ≤ 2 / (j : ℝ) := by
    have h := one_div_le_one_div_of_le (show 0 < (j : ℝ) / 2 by positivity)
      (show (j : ℝ) / 2 ≤ ((a + 1 : ℕ) : ℝ) by linarith)
    simpa only [w, one_div_div, div_one] using h
  have hd : (d j : ℝ) = ∑ n ∈ Ioc a j, w n * f n := by
    rw [cast_d]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    change (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) =
      (1 / (n : ℝ)) * (ArithmeticFunction.moebius n : ℝ)
    rw [one_div, div_eq_mul_inv, mul_comm]
  rw [hd]
  calc
    _ ≤ 2 * (D * (j : ℝ)^α) * w (a + 1) := finite_abel_bound f w haj hM hw hdec
    _ ≤ 2 * (D * (j : ℝ)^α) * (2 / (j : ℝ)) :=
      mul_le_mul_of_nonneg_left hwle (mul_nonneg (by norm_num) hB)
    _ = _ := by rw [Real.rpow_sub hj₀, Real.rpow_one]; ring

private theorem sum_cell_rpow_le {t : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1) (P : ℕ) :
    (∑ j ∈ Ico 1 P, (j : ℝ)^(t - 1)) ≤ (P : ℝ)^t / t := by
  let g : ℝ → ℝ := fun x => x^(t - 1)
  have hanti : AntitoneOn g (Set.Ioc (0 : ℝ) (0 + (P : ℝ))) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (sub_nonpos.mpr ht₁)).mono
      (fun _ hx => hx.1)
  have hint : IntervalIntegrable g volume 0 (0 + (P : ℝ)) :=
    intervalIntegral.intervalIntegrable_rpow' (show -1 < t - 1 by linarith)
  have hP : (0 : ℝ) ≤ 0 + (P : ℝ) := by positivity
  have hfi : IntegrableOn g (Set.Icc (0 : ℝ) (0 + (P : ℝ))) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hP).1 hint
  have hcmp := hanti.sum_le_integral_of_integrableOn hfi
  have hshift : (∑ j ∈ range P, g ((j + 1 : ℕ) : ℝ)) = ∑ j ∈ Ico 1 (P + 1), g (j : ℝ) := by
    simpa only [Nat.Ico_zero_eq_range, zero_add] using
      (Finset.sum_Ico_add' (fun j : ℕ => g (j : ℝ)) 0 P 1)
  change (∑ j ∈ Ico 1 P, g (j : ℝ)) ≤ _
  calc
    _ ≤ ∑ j ∈ Ico 1 (P + 1), g (j : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        simp only [Finset.mem_Ico] at hj ⊢
        omega
      · intro j _ _
        exact Real.rpow_nonneg (Nat.cast_nonneg j) _
    _ = ∑ j ∈ range P, g ((j + 1 : ℕ) : ℝ) := hshift.symm
    _ ≤ ∫ x in (0 : ℝ)..(P : ℝ), g x := by simpa only [zero_add] using hcmp
    _ = _ := by
      dsimp only [g]
      rw [integral_rpow (Or.inl (show -1 < t - 1 by linarith)),
        sub_add_cancel, Real.zero_rpow ht.ne', sub_zero]

private theorem eventually_lt_nat_rpow {t : ℝ} (ht : 0 < t) (C : ℝ) :
    ∀ᶠ P : ℕ in atTop, C < (P : ℝ)^t := by
  have hcast : Tendsto (fun P : ℕ => (P : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  exact ((tendsto_rpow_atTop ht).comp hcast).eventually (eventually_gt_atTop C)

private theorem eventually_energy_le (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ P : ℕ in atTop, (energy P : ℝ) ≤ (P : ℝ)^ε := by
  have hzero (z : ℂ) (hz : (1 / 2 : ℝ) < z.re) (hz₁ : z ≠ 1) : riemannZeta z ≠ 0 := by
    intro hζ
    have hnt : ¬ ∃ n : ℕ, z = -2 * (n + 1) := by
      rintro ⟨n, rfl⟩
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      norm_num [Complex.mul_re, Complex.add_re, Complex.add_im] at hz
      linarith
    exact hz.ne (hRH z hζ hnt hz₁).symm
  let δ := min (ε / 4) (1 / 4)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ₁ : 2 * δ ≤ 1 := by
    have h : δ ≤ 1 / 4 := min_le_right _ _
    linarith
  have hgap : 0 < ε - 2 * δ := by
    have h : δ ≤ ε / 4 := min_le_left _ _
    linarith
  obtain ⟨D, hD, hprefix⟩ := ordinary_mobius_prefix_of_zero_free
    (θ := (1 / 2 : ℝ)) le_rfl (by norm_num) hzero hδ
  let K : ℝ := (4 * D)^2 / (2 * δ)
  have hsq (j : ℕ) (hj : 1 ≤ j) :
      (d j : ℝ)^2 ≤ (4 * D)^2 * (j : ℝ)^(2 * δ - 1) := by
    have hj₀ : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
    have h := abs_d_le_of_prefix hD.le (show 0 ≤ 1 / 2 + δ by positivity) hprefix hj
    calc
      _ = |(d j : ℝ)|^2 := (sq_abs _).symm
      _ ≤ (4 * D * (j : ℝ)^((1 / 2 : ℝ) + δ - 1))^2 :=
        pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = _ := by
        have he : ((1 / 2 : ℝ) + δ - 1) * ((2 : ℕ) : ℝ) = 2 * δ - 1 := by
          norm_num
          ring
        rw [mul_pow, ← Real.rpow_mul_natCast hj₀.le, he]
  have hbound (P : ℕ) : (energy P : ℝ) ≤ K * (P : ℝ)^(2 * δ) := by
    simp only [energy, Rat.cast_sum, Rat.cast_pow]
    calc
      _ ≤ ∑ j ∈ Ico 1 P, (4 * D)^2 * (j : ℝ)^(2 * δ - 1) :=
        Finset.sum_le_sum (fun j hj => hsq j (Finset.mem_Ico.mp hj).1)
      _ = (4 * D)^2 * ∑ j ∈ Ico 1 P, (j : ℝ)^(2 * δ - 1) := (Finset.mul_sum _ _ _).symm
      _ ≤ (4 * D)^2 * ((P : ℝ)^(2 * δ) / (2 * δ)) :=
        mul_le_mul_of_nonneg_left (sum_cell_rpow_le (by positivity) hδ₁ P) (sq_nonneg _)
      _ = _ := by dsimp only [K]; ring
  filter_upwards [eventually_lt_nat_rpow hgap K, eventually_ge_atTop (1 : ℕ)] with P hKP hP
  have hP₀ : 0 < (P : ℝ) := by exact_mod_cast (show 0 < P by omega)
  refine (hbound P).trans
    ((mul_le_mul_of_nonneg_right hKP.le (Real.rpow_nonneg hP₀.le _)).trans_eq ?_)
  rw [← Real.rpow_add hP₀, sub_add_cancel]

private theorem zero_obstruction_coefficient_pos {rho : ℂ} (h₀ : 0 < rho.re) (h₁ : rho.re < 1) :
    0 < rho.re * ‖1 - (2 : ℂ) ^ (1 - rho)‖ ^ (2 : ℕ) / ‖rho * (rho - 1)‖ := by
  have hpow : 1 < ‖(2 : ℂ) ^ (1 - rho)‖ := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact Real.one_lt_rpow (by norm_num) (by rw [Complex.sub_re, Complex.one_re]; linarith)
  have hnum : 0 < ‖1 - (2 : ℂ) ^ (1 - rho)‖ := by
    apply norm_pos_iff.mpr
    intro he
    rw [← sub_eq_zero.mp he, norm_one] at hpow
    exact (lt_irrefl (1 : ℝ)) hpow
  have hz₀ : rho ≠ 0 := by
    intro he
    simp [he] at h₀
  have hz₁ : rho ≠ 1 := by
    intro he
    simp [he] at h₁
  exact div_pos (mul_pos h₀ (pow_pos hnum _))
    (norm_pos_iff.mpr (mul_ne_zero hz₀ (sub_ne_zero.mpr hz₁)))

private theorem no_right_strip_zero
    (hcofinal : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ P : ℕ,
      N ≤ P ∧ (energy P : ℝ) ≤ (P : ℝ)^ε)
    {rho : ℂ} (hr : (1 / 2 : ℝ) < rho.re) (h₁ : rho.re < 1) (hz : riemannZeta rho = 0) :
    False := by
  let ε := rho.re - (1 / 2 : ℝ)
  let γ := (1 + ε) / 2
  let c := rho.re * ‖1 - (2 : ℂ) ^ (1 - rho)‖ ^ (2 : ℕ) / ‖rho * (rho - 1)‖
  have hε : 0 < ε := sub_pos.mpr hr
  have hγ : 0 ≤ γ := by dsimp only [γ]; positivity
  have hgap : 0 < rho.re - γ := by dsimp only [γ, ε]; linarith
  have h₀ : 0 < rho.re := by linarith
  have hc : 0 < c := zero_obstruction_coefficient_pos h₀ h₁
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_lt_nat_rpow hgap (2 / c))
  obtain ⟨P, hNP, hE⟩ := hcofinal ε hε (max N 1)
  have hP : 1 ≤ P := (le_max_right N 1).trans hNP
  have hP₁ : 1 ≤ (P : ℝ) := by exact_mod_cast hP
  have hP₀ : 0 < (P : ℝ) := zero_lt_one.trans_le hP₁
  let L := ∫ u in (1 : ℝ)..(P : ℝ), |reciprocalSum u - reciprocalSum (u / 2)|
  have hLsq : L^2 ≤ ((P : ℝ)^γ)^2 := by
    calc
      _ ≤ ((P - 1 : ℕ) : ℝ) * (energy P : ℝ) := shell_mass_sq_le hP
      _ ≤ (P : ℝ) * (P : ℝ)^ε := mul_le_mul
        (by exact_mod_cast (show P - 1 ≤ P by omega)) hE
        (Rat.cast_nonneg.mpr (energy_nonneg P)) hP₀.le
      _ = (P : ℝ)^(1 + ε) := by rw [Real.rpow_add hP₀, Real.rpow_one]
      _ = _ := by
        have he : 1 + ε = γ * ((2 : ℕ) : ℝ) := by
          dsimp only [γ]
          norm_num
        rw [he, Real.rpow_mul_natCast hP₀.le]
  have hL : L ≤ (P : ℝ)^γ := le_of_sq_le_sq hLsq (Real.rpow_nonneg hP₀.le _)
  have hlower : c * (P : ℝ)^rho.re ≤ 1 + L :=
    dyadicReciprocalMoebiusShell_lower hP₁ h₀ h₁ hz
  have hupper : 1 + L ≤ 2 * (P : ℝ)^γ := by
    linarith [Real.one_le_rpow hP₁ hγ]
  have hlarge : 2 < c * (P : ℝ)^(rho.re - γ) := by
    have h := (div_lt_iff₀ hc).mp (hN P ((le_max_left N 1).trans hNP))
    simpa only [mul_comm] using h
  have hstrict : 2 * (P : ℝ)^γ < c * (P : ℝ)^rho.re := by
    have h := mul_lt_mul_of_pos_right hlarge (Real.rpow_pos_of_pos hP₀ γ)
    rwa [mul_assoc, ← Real.rpow_add hP₀, sub_add_cancel] at h
  exact (not_lt_of_ge (hlower.trans hupper)) hstrict

/-- RH holds exactly when the energy is at most `P ^ ε` at cofinally many
integer cutoffs for each positive real `ε`. -/
theorem riemannHypothesis_iff_cofinal_energy :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ P : ℕ,
      N ≤ P ∧ (energy P : ℝ) ≤ (P : ℝ)^ε := by
  constructor
  · intro hRH ε hε N
    obtain ⟨M, hM⟩ := eventually_atTop.mp (eventually_energy_le hRH hε)
    exact ⟨max N M, le_max_left _ _, hM _ (le_max_right _ _)⟩
  · intro h rho hz hnt hz₁
    have h₀ : 0 < rho.re := zero_lt_re_of_isNontrivialZetaZero ⟨hz, hnt, hz₁⟩
    have h₁ : rho.re < 1 :=
      lt_of_not_ge (fun hge => riemannZeta_ne_zero_of_one_le_re hge hz)
    have hright : rho.re ≤ 1 / 2 :=
      le_of_not_gt (fun hr => no_right_strip_zero h hr h₁ hz)
    have hleft : (1 / 2 : ℝ) ≤ rho.re := by
      by_contra! hr
      have hnoNeg (n : ℕ) : rho ≠ -(n : ℂ) := by
        intro he
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        have hre := congrArg Complex.re he
        simp only [Complex.neg_re, Complex.natCast_re] at hre
        linarith
      have hreflect : riemannZeta (1 - rho) = 0 := by
        rw [riemannZeta_one_sub hnoNeg hz₁, hz, mul_zero]
      have hre : (1 - rho).re = 1 - rho.re := by simp only [Complex.sub_re, Complex.one_re]
      exact no_right_strip_zero h (by rw [hre]; linarith) (by rw [hre]; linarith) hreflect
    exact le_antisymm hright hleft

private theorem rpow_inv_nat_pow {P k : ℕ} (hk : 0 < k) :
    ((P : ℝ)^((k : ℝ)⁻¹))^k = (P : ℝ) := by
  have hk₀ : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg P), inv_mul_cancel₀ hk₀, Real.rpow_one]

/-- The same criterion can be tested with rational arithmetic and integer powers. -/
theorem riemannHypothesis_iff_cofinal_energy_pow :
    RiemannHypothesis ↔ ∀ k : ℕ, 0 < k → ∀ N : ℕ, ∃ P : ℕ,
      N ≤ P ∧ (energy P)^k ≤ (P : ℚ) := by
  rw [riemannHypothesis_iff_cofinal_energy]
  constructor
  · intro h k hk N
    have hkℝ : 0 < (k : ℝ) := by exact_mod_cast hk
    obtain ⟨P, hNP, hP⟩ := h ((k : ℝ)⁻¹) (inv_pos.mpr hkℝ) N
    have hE : (0 : ℝ) ≤ (energy P : ℝ) := Rat.cast_nonneg.mpr (energy_nonneg P)
    have hpow := pow_le_pow_left₀ hE hP k
    rw [rpow_inv_nat_pow hk] at hpow
    refine ⟨P, hNP, (Rat.cast_le_natCast (K := ℝ)).mp ?_⟩
    simpa only [Rat.cast_pow] using hpow
  · intro h ε hε N
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
    have hkℝ : 0 < (k : ℝ) := (one_div_pos.mpr hε).trans hk
    have hk₀ : 0 < k := by exact_mod_cast hkℝ
    have hεk : (k : ℝ)⁻¹ ≤ ε := by
      rw [← one_div, div_le_iff₀ hkℝ]
      have hmul : 1 < (k : ℝ) * ε := (div_lt_iff₀ hε).mp hk
      simpa only [mul_comm] using hmul.le
    obtain ⟨P, hNP, hP⟩ := h k hk₀ (max N 1)
    have hP₁ : 1 ≤ (P : ℝ) := by
      exact_mod_cast ((le_max_right N 1).trans hNP)
    have hpow : (energy P : ℝ)^k ≤ (P : ℝ) := by
      simpa only [Rat.cast_pow] using (Rat.cast_le_natCast (K := ℝ)).mpr hP
    have hroot : (energy P : ℝ) ≤ (P : ℝ)^((k : ℝ)⁻¹) := by
      apply le_of_pow_le_pow_left₀ (n := k) (Nat.ne_of_gt hk₀)
        (Real.rpow_nonneg (Nat.cast_nonneg P) _)
      rwa [rpow_inv_nat_pow hk₀]
    exact ⟨P, (le_max_left N 1).trans hNP, hroot.trans (Real.rpow_le_rpow_of_exponent_le hP₁ hεk)⟩

end D5.S3.Weil.ZetaPntBounds.FiniteDyadicMobiusEnergy
