/- GID: D5/S3/Arith/Robin/OriginalResidualPartialCellWeights
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/OriginalResidualPartialCellWeights
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Literal partial cells determine an affine projection with exact moments and bounds. -/

import D5.S3.Arith.Robin.ActualRobinClockCovariance
import D5.S3.Arith.Robin.MellinWeightedVariation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Matrix
open Finset MeasureTheory Set
open D5.S3.Arith.Robin.ActualRobinClockCovariance (g activationDensity density_integral)

namespace D5.S3.Arith.Robin.OriginalResidualPartialCellWeights

/-- Literal intersection with a closed unit cell; singleton intersections have zero mass. -/
def omega (a b : ℝ) (m : ℕ) : ℝ :=
  ∫ t in Icc a b ∩ Icc (m : ℝ) (m + 1), activationDensity t

/-- The positive discrete Robin weight. -/
def w (m : ℕ) : ℝ := 1 / ((m : ℝ) * (m + 1))

/-- The affine sample at the original integer index. -/
def v (N m : ℕ) : Fin 2 → ℝ := ![1, (m : ℝ) / N]

/-- The actual weighted finite Gram, without a supplied inverse. -/
def gram (N : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => ∑ m ∈ Finset.Ico N (2 * N), w m * v N m i * v N m j

/-- The original cell datum, with its separate terminal value. -/
def datum (N : ℕ) (a b : ℝ) (m : ℕ) : ℝ :=
  if m = 2 * N then 0 else Real.log N * omega a b m / w m

/-- The actual right side of the two normal equations. -/
def rhs (N : ℕ) (a b : ℝ) : Fin 2 → ℝ :=
  fun i => ∑ m ∈ Finset.Ico N (2 * N), w m * datum N a b m * v N m i

/-- Scalar determinant of the actual symmetric two by two Gram. -/
def delta (N : ℕ) : ℝ := gram N 0 0 * gram N 1 1 - gram N 0 1 ^ 2

/-- Cramer's coefficients; no sign restriction is imposed on either entry. -/
def c (N : ℕ) (a b : ℝ) : Fin 2 → ℝ :=
  ![(gram N 1 1 * rhs N a b 0 - gram N 0 1 * rhs N a b 1) / delta N,
    (gram N 0 0 * rhs N a b 1 - gram N 0 1 * rhs N a b 0) / delta N]

/-- The affine residual on the half-open integer block, and zero at its terminal endpoint. -/
def residual (N : ℕ) (a b : ℝ) (m : ℕ) : ℝ :=
  if m = 2 * N then 0 else datum N a b m - c N a b 0 - c N a b 1 * ((m : ℝ) / N)

/-- The actual projected coefficient, extended by zero outside the integer block. -/
def coeff (N : ℕ) (a b : ℝ) (m : ℕ) : ℝ :=
  if N ≤ m ∧ m < 2 * N then w m * residual N a b m else 0

/-- Absolute mass on the original block. -/
def mass (N : ℕ) (f : ℕ → ℝ) : ℝ := ∑ m ∈ Finset.Ico N (2 * N), |f m|

/-- Complete zero-extension variation, including the entering and exiting jumps. -/
def variation (N : ℕ) (f : ℕ → ℝ) : ℝ :=
  |f N| + (∑ m ∈ Finset.Ico N (2 * N - 1), |f (m + 1) - f m|) + |f (2 * N - 1)|

/-- The exact harmonic sum in the mass allowance. -/
def harmonic (N : ℕ) : ℝ := ∑ m ∈ Finset.Ico N (2 * N), 1 / ((m : ℝ) + 1)

private lemma w_pos {m : ℕ} (hm : 0 < m) : 0 < w m := by
  unfold w
  positivity

private lemma gram_entries (N : ℕ) :
    gram N 0 0 = ∑ m ∈ Finset.Ico N (2 * N), w m ∧
    gram N 0 1 = ∑ m ∈ Finset.Ico N (2 * N), w m * ((m : ℝ)/N) ∧
    gram N 1 0 = gram N 0 1 ∧
    gram N 1 1 = ∑ m ∈ Finset.Ico N (2 * N), w m * ((m : ℝ)/N)^2 := by
  simp [gram, v, pow_two, mul_assoc]

private lemma gram_quadratic (N : ℕ) (u z : ℝ) :
    (∑ m ∈ Finset.Ico N (2 * N), w m * (u + z * ((m : ℝ)/N))^2) =
      gram N 0 0 * u^2 + 2 * gram N 0 1 * u*z + gram N 1 1 * z^2 := by
  rcases gram_entries N with ⟨h00, h01, _, h11⟩
  rw [h00, h01, h11]
  simp_rw [mul_sum, sum_mul, ← sum_add_distrib]
  apply sum_congr rfl
  intro m _
  ring

private lemma gram_quadratic_pos {N : ℕ} (hN : 3 ≤ N) {u z : ℝ}
    (hn : u ≠ 0 ∨ z ≠ 0) :
    0 < ∑ m ∈ Finset.Ico N (2 * N), w m * (u + z * ((m : ℝ)/N))^2 := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hmem0 : N ∈ Finset.Ico N (2 * N) := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
  have hmem1 : N+1 ∈ Finset.Ico N (2 * N) := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hdistinct : (N : ℝ)/N ≠ ((N+1 : ℕ) : ℝ)/N := by
    intro he
    have hh := (div_left_inj' hNp.ne').mp he
    push_cast at hh
    linarith
  have hnonzero : u + z * ((N : ℝ)/N) ≠ 0 ∨
      u + z * (((N+1 : ℕ) : ℝ)/N) ≠ 0 := by
    by_contra hh
    push Not at hh
    have hz : z = 0 := by
      rcases mul_eq_zero.mp (show z * ((N : ℝ)/N - ((N+1 : ℕ) : ℝ)/N) = 0 by
        nlinarith [hh.1, hh.2]) with hz | hx
      · exact hz
      · exact (hdistinct (sub_eq_zero.mp hx)).elim
    have hu : u = 0 := by simpa [hz] using hh.1
    exact hn.elim (fun h => h hu) (fun h => h hz)
  apply sum_pos'
  · intro m hm
    exact mul_nonneg (w_pos (by have := (Finset.mem_Ico.mp hm).1; omega)).le (sq_nonneg _)
  · rcases hnonzero with hh | hh
    · exact ⟨N, hmem0, mul_pos (w_pos (by omega)) (sq_pos_of_ne_zero hh)⟩
    · exact ⟨N+1, hmem1, mul_pos (w_pos (by omega)) (sq_pos_of_ne_zero hh)⟩

private lemma delta_pos {N : ℕ} (hN : 3 ≤ N) : 0 < delta N := by
  have h00 : 0 < gram N 0 0 := by
    simpa [gram, v] using gram_quadratic_pos hN (u := 1) (z := 0) (Or.inl one_ne_zero)
  have hp := gram_quadratic_pos hN (u := -(gram N 0 1)) (z := gram N 0 0)
    (Or.inr h00.ne')
  rw [gram_quadratic] at hp
  have he : gram N 0 0 * (-gram N 0 1)^2 +
      2 * gram N 0 1 * (-gram N 0 1) * gram N 0 0 +
      gram N 1 1 * gram N 0 0 ^ 2 = gram N 0 0 * delta N := by
    unfold delta
    ring
  rw [he] at hp
  exact (mul_pos_iff_of_pos_left h00).mp hp

private lemma normal_equations {N : ℕ} (hN : 3 ≤ N) (a b : ℝ) :
    gram N 0 0 * c N a b 0 + gram N 0 1 * c N a b 1 = rhs N a b 0 ∧
    gram N 0 1 * c N a b 0 + gram N 1 1 * c N a b 1 = rhs N a b 1 := by
  have hd := (delta_pos hN).ne'
  constructor <;> simp only [c, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] <;> field_simp [hd] <;> unfold delta <;> ring

private lemma coeff_on {N m : ℕ} {a b : ℝ} (hN : 3 ≤ N)
    (hm : m ∈ Finset.Ico N (2 * N)) :
    coeff N a b m = Real.log N * omega a b m - c N a b 0 * w m -
      c N a b 1 * (w m * ((m : ℝ)/N)) := by
  have hmi := Finset.mem_Ico.mp hm
  have hne : m ≠ 2 * N := by omega
  have hw := (w_pos (m := m) (by omega)).ne'
  simp only [coeff, if_pos hmi, residual, if_neg hne, datum]
  field_simp

private lemma exact_moments {N : ℕ} (hN : 3 ≤ N) (a b : ℝ) :
    (∑ m ∈ Finset.Ico N (2 * N), coeff N a b m) = 0 ∧
    (∑ m ∈ Finset.Ico N (2 * N), (m : ℝ) * coeff N a b m) = 0 := by
  rcases normal_equations hN a b with ⟨h0, h1⟩
  rcases gram_entries N with ⟨h00, h01, _, h11⟩
  have he (m : ℕ) (hm : m ∈ Finset.Ico N (2 * N)) :
      coeff N a b m = w m * datum N a b m -
        c N a b 0 * w m - c N a b 1 * (w m * ((m : ℝ)/N)) := by
    have hmi := Finset.mem_Ico.mp hm
    simp only [coeff, if_pos hmi, residual, if_neg (show m ≠ 2 * N by omega)]
    ring
  have h0' : (∑ m ∈ Finset.Ico N (2 * N), coeff N a b m) =
      rhs N a b 0 - c N a b 0 * gram N 0 0 - c N a b 1 * gram N 0 1 := by
    rw [h00, h01]
    simp only [rhs, v, Matrix.cons_val_zero, mul_one]
    simp_rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl he
  have h1' : (∑ m ∈ Finset.Ico N (2 * N), ((m : ℝ)/N) * coeff N a b m) =
      rhs N a b 1 - c N a b 0 * gram N 0 1 - c N a b 1 * gram N 1 1 := by
    rw [h01, h11]
    simp only [rhs, v, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    simp_rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro m hm
    rw [he m hm]
    ring
  have hm0 : (∑ m ∈ Finset.Ico N (2 * N), coeff N a b m) = 0 := by linarith [h0']
  have hm1 : (∑ m ∈ Finset.Ico N (2 * N), ((m : ℝ)/N) * coeff N a b m) = 0 := by
    linarith [h1']
  refine ⟨hm0, ?_⟩
  have hNp : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  calc
    _ = (N : ℝ) * ∑ m ∈ Finset.Ico N (2 * N), ((m : ℝ)/N) * coeff N a b m := by
      rw [mul_sum]
      apply sum_congr rfl
      intro m _
      field_simp
    _ = 0 := by rw [hm1, mul_zero]

private lemma omega_endpoint {a b : ℝ} (ha : 1 < a) (m : ℕ) :
    omega a b m = if max a (m : ℝ) < min b (m + 1) then
      g (max a (m : ℝ)) - g (min b (m + 1)) else 0 := by
  unfold omega
  rw [Icc_inter_Icc]
  split_ifs with h
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h.le]
    exact density_integral (ha.trans_le (le_max_left _ _)) h.le
  · by_cases he : max a (m : ℝ) = min b (m + 1)
    · rw [he]
      simp
    · rw [Icc_eq_empty_of_lt (lt_of_le_of_ne (le_of_not_gt h) (Ne.symm he))]
      simp

private def cap (a b t : ℝ) : ℝ :=
  if t ≤ b then activationDensity (max a t) else 0

private def step (a t : ℝ) : ℝ := if t < a then activationDensity a else 0

private lemma cap_antitone {a b : ℝ} (ha : 1 < a) : Antitone (cap a b) := by
  intro s t hst
  by_cases htb : t ≤ b
  · have hsb := hst.trans htb
    simp only [cap, if_pos htb, if_pos hsb]
    have hs : 1 < max a s := ha.trans_le (le_max_left _ _)
    have hmax : max a s ≤ max a t := max_le_max_left a hst
    have hp : 0 < max a s := by linarith
    have hh := MellinWeightedVariation.scaleWeight_antitone (x := max a s)
      (y := 1) (a := max a s) (b := max a t) hs (by norm_num) hp hmax (by simp)
    rw [MellinWeightedVariation.scaleWeight_eq, MellinWeightedVariation.scaleWeight_eq,
      mul_one, mul_one] at hh
    change max a t * activationDensity (max a t) ≤
      max a s * activationDensity (max a s) at hh
    have hn := mul_le_mul_of_nonneg_right hmax
      (show 0 ≤ activationDensity (max a t) from
        MellinWeightedVariation.weight_nonneg (ha.trans_le (le_max_left a t)))
    exact (mul_le_mul_iff_right₀ hp).mp (hn.trans hh)
  · simp only [cap, if_neg htb]
    split_ifs
    · exact MellinWeightedVariation.weight_nonneg (ha.trans_le (le_max_left _ _))
    · exact le_rfl

private lemma step_antitone {a : ℝ} (ha : 1 < a) : Antitone (step a) := by
  intro s t hst
  unfold step
  split_ifs <;> try exact le_rfl
  · exact False.elim (by linarith)
  · exact MellinWeightedVariation.weight_nonneg ha

private lemma cap_sub_step {a b : ℝ} (hab : a ≤ b) (t : ℝ) :
    cap a b t - step a t = (Icc a b).indicator activationDensity t := by
  by_cases hta : t < a
  · have htb : t ≤ b := hta.le.trans hab
    simp [cap, step, hta, htb, max_eq_left hta.le, indicator_of_notMem,
      show t ∉ Icc a b by simp only [Set.mem_Icc]; intro h; linarith]
  · have hat : a ≤ t := le_of_not_gt hta
    by_cases htb : t ≤ b
    · simp [cap, step, hta, htb, hat]
    · simp [cap, step, hta, htb]

private lemma clipped_integrable {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) (s t : ℝ) :
    IntervalIntegrable ((Icc a b).indicator activationDensity) volume s t := by
  rw [← funext (cap_sub_step hab)]
  exact (cap_antitone ha).intervalIntegrable.sub (step_antitone ha).intervalIntegrable

private def cell (f : ℝ → ℝ) (m : ℕ) : ℝ := ∫ s in (0 : ℝ)..1, f ((m : ℝ) + s)

private lemma cell_antitone {f : ℝ → ℝ} (hf : Antitone f) : Antitone (cell f) := by
  intro m n hmn
  have hi (m : ℕ) : IntervalIntegrable (fun s => f ((m : ℝ)+s)) volume 0 1 :=
    (show Antitone (fun s => f ((m : ℝ)+s)) from fun x y hxy => hf (by linarith)).intervalIntegrable
  exact intervalIntegral.integral_mono_on (by norm_num) (hi n) (hi m)
    (fun s _ => hf (by
      have hr : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
      linarith))

private lemma cell_interval (f : ℝ → ℝ) (m : ℕ) :
    cell f m = ∫ t in (m : ℝ)..m+1, f t := by
  simpa [cell, add_comm, add_left_comm, add_assoc] using
    intervalIntegral.integral_comp_add_right (a := 0) (b := 1) f (m : ℝ)

private lemma omega_cell (a b : ℝ) (m : ℕ) :
    omega a b m = cell ((Icc a b).indicator activationDensity) m := by
  rw [cell_interval, intervalIntegral.integral_of_le (by linarith),
    ← integral_Icc_eq_integral_Ioc, setIntegral_indicator measurableSet_Icc]
  unfold omega
  rw [inter_comm]

private lemma omega_split {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) (m : ℕ) :
    omega a b m = cell (cap a b) m - cell (step a) m := by
  rw [omega_cell, cell_interval, cell_interval, cell_interval,
    ← intervalIntegral.integral_sub (cap_antitone ha).intervalIntegrable
      (step_antitone ha).intervalIntegrable]
  congr 1
  exact (funext (cap_sub_step hab)).symm

private lemma omega_nonneg {a b : ℝ} (ha : 1 < a) (m : ℕ) : 0 ≤ omega a b m := by
  apply setIntegral_nonneg (measurableSet_Icc.inter measurableSet_Icc)
  intro t ht
  exact MellinWeightedVariation.weight_nonneg (ha.trans_le ht.1.1)

private lemma omega_sum {N : ℕ} {a b : ℝ} (hNa : (N : ℝ) ≤ a) (hab : a ≤ b)
    (hbN : b ≤ 2 * N) (ha : 1 < a) :
    (∑ m ∈ Finset.Ico N (2 * N), omega a b m) = g a - g b := by
  have hN : N ≤ 2 * N := by omega
  have hs := intervalIntegral.sum_integral_adjacent_intervals_Ico (a := fun m : ℕ => (m : ℝ))
    (f := (Icc a b).indicator activationDensity) hN
    (fun m _ => by simpa only [Nat.cast_add, Nat.cast_one] using clipped_integrable ha hab m (m+1))
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat] at hs
  calc
    _ = ∫ t in (N : ℝ)..2 * N, (Icc a b).indicator activationDensity t := by
      simpa only [← cell_interval, ← omega_cell] using hs
    _ = ∫ t in a..b, activationDensity t := by
      rw [intervalIntegral.integral_of_le (by exact_mod_cast hN),
        ← integral_Icc_eq_integral_Ioc, setIntegral_indicator measurableSet_Icc,
        inter_eq_right.mpr (Icc_subset_Icc hNa hbN), integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hab]
    _ = _ := density_integral ha hab

private lemma telescope (f : ℕ → ℝ) {l u : ℕ} (h : l ≤ u) :
    (∑ m ∈ Finset.Ico l u, (f m - f (m+1))) = f l - f u := by
  simpa only [neg_sub_neg] using sum_Ico_sub (fun m => -f m) h

private lemma variation_difference {N : ℕ} (hN : 1 ≤ N) (F B : ℕ → ℝ)
    (hF : Antitone F) (hB : Antitone B)
    (hpos : ∀ m, N ≤ m → m < 2 * N → 0 ≤ F m - B m) :
    variation N (fun m => F m - B m) ≤ 2 * F N - 2 * B (2 * N-1) := by
  have hend : N ≤ 2 * N-1 := by omega
  have hdiff (m : ℕ) :
      |(F (m+1)-B (m+1))-(F m-B m)| ≤
        (F m-F (m+1))+(B m-B (m+1)) := by
    have hff := hF (show m ≤ m+1 by omega)
    have hbb := hB (show m ≤ m+1 by omega)
    apply abs_le.mpr
    constructor <;> linarith
  unfold variation
  rw [abs_of_nonneg (hpos N le_rfl (by omega)),
    abs_of_nonneg (hpos (2 * N-1) hend (by omega))]
  have hs := sum_le_sum (s := Finset.Ico N (2 * N-1)) (fun m _ => hdiff m)
  rw [sum_add_distrib, telescope F hend, telescope B hend] at hs
  linarith

private lemma omega_variation {N : ℕ} (hN : 3 ≤ N) {a b : ℝ}
    (ha : 1 < a) (hab : a ≤ b) :
    variation N (omega a b) ≤ 2 * activationDensity a := by
  let F := cell (cap a b)
  let B := cell (step a)
  have he : omega a b = fun m => F m-B m := funext (omega_split ha hab)
  have hv := variation_difference (N := N) (by omega) F B
    (cell_antitone (cap_antitone ha)) (cell_antitone (step_antitone ha))
    (fun m _ _ => by rw [← omega_split ha hab]; exact omega_nonneg ha m)
  have hb : 0 ≤ B (2 * N-1) := by
    apply intervalIntegral.integral_nonneg_of_forall (by norm_num)
    intro t
    dsimp [step]
    split_ifs
    · exact MellinWeightedVariation.weight_nonneg ha
    · exact le_rfl
  have hf : F N ≤ activationDensity a := by
    have hc : ∀ t, cap a b t ≤ activationDensity a := by
      intro t
      by_cases hat : a ≤ t
      · simpa only [cap, if_pos hab, max_self] using cap_antitone (b := b) ha hat
      · have hta : t ≤ a := (lt_of_not_ge hat).le
        simp [cap, hta.trans hab, max_eq_left hta]
    have hi : IntervalIntegrable (fun t => cap a b ((N : ℝ)+t)) volume 0 1 :=
      (show Antitone (fun t => cap a b ((N : ℝ)+t)) from
        fun s t hst => cap_antitone ha (by linarith)).intervalIntegrable
    have hh := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      hi intervalIntegrable_const (fun t _ => hc ((N : ℝ)+t))
    simpa [F, cell] using hh
  rw [he]
  linarith

private lemma variation_congr {N : ℕ} (hN : 1 ≤ N) {f h : ℕ → ℝ}
    (he : ∀ m ∈ Finset.Ico N (2 * N), f m = h m) : variation N f = variation N h := by
  have hs : (∑ m ∈ Finset.Ico N (2 * N-1), |f (m+1)-f m|) =
      ∑ m ∈ Finset.Ico N (2 * N-1), |h (m+1)-h m| := by
    apply sum_congr rfl
    intro m hm
    have hi := Finset.mem_Ico.mp hm
    rw [he m (Finset.mem_Ico.mpr ⟨hi.1, by omega⟩),
      he (m+1) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)]
  simp only [variation, hs, he N (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩),
    he (2 * N-1) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)]

private lemma variation_sub (N : ℕ) (f h : ℕ → ℝ) :
    variation N (fun m => f m-h m) ≤ variation N f+variation N h := by
  have hs := sum_le_sum (s := Finset.Ico N (2 * N-1)) (fun m _ =>
    show |(f (m+1)-h (m+1))-(f m-h m)| ≤
      |f (m+1)-f m|+|h (m+1)-h m| from by
      rw [show (f (m+1)-h (m+1))-(f m-h m) =
        (f (m+1)-f m)-(h (m+1)-h m) by ring]
      exact abs_sub _ _)
  rw [sum_add_distrib] at hs
  dsimp [variation]
  linarith [abs_sub (f N) (h N), abs_sub (f (2 * N-1)) (h (2 * N-1))]

private lemma variation_mul (N : ℕ) (k : ℝ) (f : ℕ → ℝ) :
    variation N (fun m => k*f m) = |k| * variation N f := by
  simp only [variation, ← mul_sub, abs_mul, ← mul_sum]
  ring

private lemma variation_antitone {N : ℕ} (hN : 1 ≤ N) (f : ℕ → ℝ)
    (hf : AntitoneOn f (Set.Ici N)) (hp : ∀ m, N ≤ m → 0 ≤ f m) :
    variation N f = 2*f N := by
  unfold variation
  rw [abs_of_nonneg (hp N le_rfl), abs_of_nonneg (hp _ (by omega))]
  have he : (∑ m ∈ Finset.Ico N (2 * N-1), |f (m+1)-f m|) =
      ∑ m ∈ Finset.Ico N (2 * N-1), (f m-f (m+1)) := by
    apply sum_congr rfl
    intro m hm
    have hi := Finset.mem_Ico.mp hm
    rw [abs_of_nonpos (sub_nonpos.mpr (hf hi.1 (by change N ≤ m+1; omega) (by omega)))]
    ring
  rw [he, telescope f (by omega)]
  ring

private def q (N m : ℕ) : ℝ := w m * ((m : ℝ)/N)

private lemma q_eq {N m : ℕ} (hN : 0 < N) (hm : 0 < m) :
    q N m = 1 / ((N : ℝ)*(m+1)) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  unfold q w
  field_simp

private lemma discrete_weights {N : ℕ} (hN : 3 ≤ N) :
    (∑ m ∈ Finset.Ico N (2 * N), w m) = 1/(2*(N : ℝ)) ∧
    (∑ m ∈ Finset.Ico N (2 * N), q N m) = harmonic N/N ∧
    variation N w = 2/((N : ℝ)*(N+1)) ∧
    variation N (q N) = 2/((N : ℝ)*(N+1)) := by
  have hn : 0 < N := by omega
  have hn' : 0 < (N : ℝ) := by exact_mod_cast hn
  have hwanti : AntitoneOn w (Set.Ici N) := by
    intro m hm n _ hmn
    have hm' : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by change N ≤ m at hm; omega)
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    exact one_div_le_one_div_of_le (by positivity)
      (by nlinarith : (m : ℝ)*(m+1) ≤ (n : ℝ)*(n+1))
  have hqanti : AntitoneOn (q N) (Set.Ici N) := by
    intro m hm n hnN hmn
    have hmp : 0 < m := by change N ≤ m at hm; omega
    have hnp : 0 < n := by change N ≤ n at hnN; omega
    rw [q_eq hn hmp, q_eq hn hnp]
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.add_le_add_right hmn 1) hn'.le
  have hwp : ∀ m, N ≤ m → 0 ≤ w m :=
    fun m hm => (w_pos (by omega)).le
  have hqp : ∀ m, N ≤ m → 0 ≤ q N m := by
    intro m hm
    rw [q_eq hn (by omega)]
    positivity
  have hsumw : (∑ m ∈ Finset.Ico N (2 * N), w m) = 1/(2*(N : ℝ)) := by
    calc
      _ = ∑ m ∈ Finset.Ico N (2 * N), ((1/(m : ℝ))-(1/((m : ℝ)+1))) := by
        apply sum_congr rfl
        intro m hm
        have hp : 0 < (m : ℝ) := by
          exact_mod_cast (show 0 < m by have := (Finset.mem_Ico.mp hm).1; omega)
        unfold w
        field_simp
        ring
      _ = 1/(N : ℝ)-1/((2 * N : ℕ) : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          telescope (fun m : ℕ => 1/(m : ℝ)) (show N ≤ 2 * N by omega)
      _ = _ := by
        push_cast
        field_simp
        ring
  have hsumq : (∑ m ∈ Finset.Ico N (2 * N), q N m) = harmonic N/N := by
    unfold harmonic
    rw [sum_div]
    apply sum_congr rfl
    intro m hm
    rw [q_eq hn (by have := (Finset.mem_Ico.mp hm).1; omega)]
    field_simp
  refine ⟨hsumw, hsumq, ?_, ?_⟩
  · rw [variation_antitone (by omega) w hwanti hwp]
    unfold w
    ring
  · rw [variation_antitone (by omega) (q N) hqanti hqp, q_eq hn hn]
    ring

private lemma coeff_variation {N : ℕ} (hN : 3 ≤ N) {a b : ℝ}
    (ha : 1 < a) (hab : a ≤ b) :
    variation N (coeff N a b) ≤ 2 * Real.log N * activationDensity a +
      2 * (|c N a b 0|+|c N a b 1|) / ((N : ℝ)*(N+1)) := by
  have hL : 0 ≤ Real.log (N : ℝ) := (Real.log_pos (by exact_mod_cast (by omega : 1 < N))).le
  have he := variation_congr (N := N) (by omega) (fun m hm => coeff_on hN hm (a := a) (b := b))
  change variation N (coeff N a b) = variation N
    (fun m => Real.log N * omega a b m-c N a b 0*w m-c N a b 1*q N m) at he
  rw [he]
  have hsub := variation_sub N
    (fun m => Real.log N*omega a b m-c N a b 0*w m) (fun m => c N a b 1*q N m)
  have hsub' := variation_sub N (fun m => Real.log N*omega a b m) (fun m => c N a b 0*w m)
  rw [variation_mul] at hsub
  rw [variation_mul, variation_mul, abs_of_nonneg hL] at hsub'
  rcases discrete_weights hN with ⟨_, _, hw, hq⟩
  rw [hw] at hsub'
  rw [hq] at hsub
  have ho := mul_le_mul_of_nonneg_left (omega_variation hN ha hab) hL
  calc
    _ ≤ Real.log N * variation N (omega a b) +
        |c N a b 0| * (2/((N : ℝ)*(N+1))) +
        |c N a b 1| * (2/((N : ℝ)*(N+1))) := by linarith
    _ ≤ Real.log N * (2*activationDensity a) +
        |c N a b 0| * (2/((N : ℝ)*(N+1))) +
        |c N a b 1| * (2/((N : ℝ)*(N+1))) := by linarith
    _ = _ := by ring

private lemma coeff_mass {N : ℕ} (hN : 3 ≤ N) {a b : ℝ}
    (hNa : (N : ℝ) ≤ a) (hab : a ≤ b) (hbN : b ≤ 2 * N) :
    mass N (coeff N a b) ≤ Real.log N * (g a-g b) +
      |c N a b 0|/(2*(N : ℝ)) + |c N a b 1| * harmonic N/N := by
  have ha : 1 < a := (show (1 : ℝ) < N by exact_mod_cast (by omega : 1 < N)).trans_le hNa
  have hL : 0 ≤ Real.log (N : ℝ) := (Real.log_pos (by exact_mod_cast (by omega : 1 < N))).le
  have hbound (m : ℕ) (hm : m ∈ Finset.Ico N (2 * N)) :
      |coeff N a b m| ≤ Real.log N * omega a b m + |c N a b 0| * w m+|c N a b 1| * q N m := by
    have hp : 0 < m := by have := (Finset.mem_Ico.mp hm).1; omega
    have hwp := (w_pos hp).le
    have hqp : 0 ≤ q N m := mul_nonneg hwp (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    rw [coeff_on hN hm]
    calc
      _ ≤ |Real.log N*omega a b m-c N a b 0*w m|+|c N a b 1*q N m| := abs_sub _ _
      _ ≤ (|Real.log N*omega a b m|+|c N a b 0*w m|)+|c N a b 1*q N m| :=
        add_le_add (abs_sub _ _) le_rfl
      _ = _ := by rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hL,
        abs_of_nonneg (omega_nonneg ha m), abs_of_nonneg hwp, abs_of_nonneg hqp]
  have hs := sum_le_sum (s := Finset.Ico N (2 * N)) hbound
  simp only [sum_add_distrib, ← mul_sum] at hs
  rcases discrete_weights hN with ⟨hw, hq, _, _⟩
  rw [omega_sum hNa hab hbN ha, hw, hq] at hs
  unfold mass
  exact hs.trans_eq (by ring)

private lemma inverse_coefficients {N : ℕ} (hN : 3 ≤ N) (a b : ℝ) :
    c N a b = (gram N)⁻¹ *ᵥ rhs N a b := by
  have hdet : (gram N).det = delta N := by
    rw [Matrix.det_fin_two, (gram_entries N).2.2.1]
    unfold delta
    ring
  have hu : IsUnit (gram N).det :=
    isUnit_iff_ne_zero.mpr (by rw [hdet]; exact (delta_pos hN).ne')
  have hn : gram N *ᵥ c N a b = rhs N a b := by
    rcases normal_equations hN a b with ⟨h0, h1⟩
    ext i
    fin_cases i
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h0
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, (gram_entries N).2.2.1] using h1
  rw [← hn, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

/-- The actual partial-cell projection, its two exact moments, and complete finite mass and BV bounds. -/
theorem or6_partialCell_variation {N : ℕ} {a b : ℝ} (hN : 3 ≤ N)
    (hNa : (N : ℝ) < a) (hab : a < b) (hbN : b < 2 * N) :
    (∀ m : ℕ, omega a b m = if max a (m : ℝ) < min b (m+1) then
      g (max a (m : ℝ))-g (min b (m+1)) else 0) ∧
    0 < delta N ∧
    c N a b = (gram N)⁻¹ *ᵥ rhs N a b ∧
    gram N *ᵥ c N a b = rhs N a b ∧
    (∑ m ∈ Finset.Ico N (2 * N), coeff N a b m) = 0 ∧
    (∑ m ∈ Finset.Ico N (2 * N), (m : ℝ)*coeff N a b m) = 0 ∧
    datum N a b (2 * N) = 0 ∧ residual N a b (2 * N) = 0 ∧ coeff N a b (2 * N) = 0 ∧
    variation N (coeff N a b) ≤ 2*Real.log N*activationDensity a +
      2*(|c N a b 0|+|c N a b 1|)/((N : ℝ)*(N+1)) ∧
    2*Real.log N*activationDensity a + 2*(|c N a b 0|+|c N a b 1|)/((N : ℝ)*(N+1)) ≤
      2*Real.log N*activationDensity N + 2*(|c N a b 0|+|c N a b 1|)/((N : ℝ)*(N+1)) ∧
    mass N (coeff N a b) ≤ Real.log N*(g a-g b)+
      |c N a b 0|/(2*(N : ℝ))+|c N a b 1| * harmonic N/N := by
  have ha : 1 < a := (show (1 : ℝ) < N by exact_mod_cast (by omega : 1 < N)).trans hNa
  have hinv := inverse_coefficients hN a b
  have hm := exact_moments hN a b
  refine ⟨omega_endpoint ha, delta_pos hN, hinv, ?_, hm.1, hm.2,
    by simp [datum], by simp [residual], by simp [coeff],
    coeff_variation hN ha hab.le, ?_, coeff_mass hN hNa.le hab.le hbN.le⟩
  · rw [hinv, Matrix.mulVec_mulVec]
    have hdet : (gram N).det = delta N := by
      rw [Matrix.det_fin_two, (gram_entries N).2.2.1]
      unfold delta
      ring
    rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (by rw [hdet]; exact (delta_pos hN).ne')),
      Matrix.one_mulVec]
  · have hd := cap_antitone (a := (N : ℝ)) (b := a)
      (by exact_mod_cast (by omega : 1 < N)) hNa.le
    simp only [cap, if_pos hNa.le, le_refl, if_true, max_self, max_eq_right hNa.le] at hd
    have hL : 0 ≤ 2*Real.log (N : ℝ) := by
      positivity [Real.log_pos (show (1 : ℝ) < N by exact_mod_cast (by omega : 1 < N))]
    exact add_le_add (mul_le_mul_of_nonneg_left hd hL) le_rfl

#print axioms or6_partialCell_variation

private lemma actualEnergy_invSquare_cell {m : ℕ} (hm : 0 < m) :
    (∫ t in (m : ℝ)..(m : ℝ) + 1, 1 / t ^ 2) = w m := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hm1R : 0 < (m : ℝ) + 1 := by linarith
  have hcell : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
  have hnonzero : ∀ t ∈ Set.uIcc (m : ℝ) ((m : ℝ) + 1), t ≠ 0 := by
    intro t ht
    rw [Set.uIcc_of_le hcell] at ht
    exact (hmR.trans_le ht.1).ne'
  have hint : IntervalIntegrable (fun t : ℝ => 1 / t ^ 2)
      volume (m : ℝ) ((m : ℝ) + 1) := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero 2 (hnonzero t ht))
  have hderiv : ∀ t ∈ Set.uIcc (m : ℝ) ((m : ℝ) + 1),
      HasDerivAt (fun t : ℝ => -t⁻¹) (1 / t ^ 2) t := by
    intro t ht
    convert! (hasDerivAt_inv (hnonzero t ht)).neg using 1 <;>
      simp only [neg_neg, one_div]
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  calc
    _ = 1 / (m : ℝ) - 1 / ((m : ℝ) + 1) := by
      simpa only [one_div, neg_sub_neg] using he
    _ = w m := by
      unfold w
      field_simp [hmR.ne', hm1R.ne']
      <;> ring

private lemma actualEnergy_density_cap {N : ℕ} (hN : 3 ≤ N)
    {t : ℝ} (hNt : (N : ℝ) ≤ t) :
    activationDensity t ≤
      ((Real.log (N : ℝ))⁻¹ + (Real.log (N : ℝ))⁻¹ ^ 2) * (1 / t ^ 2) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hLN : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have ht1 : 1 < t := hN1.trans_le hNt
  have ht0 : 0 < t := by linarith
  have hLt : 0 < Real.log t := Real.log_pos ht1
  have hlog : Real.log (N : ℝ) ≤ Real.log t :=
    Real.log_le_log (by linarith) hNt
  have hinv : (Real.log t)⁻¹ ≤ (Real.log (N : ℝ))⁻¹ := inv_anti₀ hLN hlog
  have hleft : 0 ≤ (Real.log t)⁻¹ := inv_nonneg.mpr hLt.le
  have hright : 0 ≤ (Real.log (N : ℝ))⁻¹ := inv_nonneg.mpr hLN.le
  have hsquare : (Real.log t)⁻¹ ^ 2 ≤ (Real.log (N : ℝ))⁻¹ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hinv) (add_nonneg hleft hright)]
  have hnum := add_le_add hinv hsquare
  calc
    activationDensity t = ((Real.log t)⁻¹ + (Real.log t)⁻¹ ^ 2) * (1 / t ^ 2) := by
      unfold activationDensity
      field_simp [ht0.ne', hLt.ne']
      <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hnum (by positivity)

private lemma actualEnergy_omega_cap {N m : ℕ} {a b : ℝ}
    (hN : 3 ≤ N) (ha : 1 < a) (hab : a ≤ b) (hNm : N ≤ m) :
    omega a b m ≤
      ((Real.log (N : ℝ))⁻¹ + (Real.log (N : ℝ))⁻¹ ^ 2) * w m := by
  let K : ℝ := (Real.log (N : ℝ))⁻¹ + (Real.log (N : ℝ))⁻¹ ^ 2
  have hLN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hmp : 0 < m := by omega
  have hNmR : (N : ℝ) ≤ m := by exact_mod_cast hNm
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hmp
  have hcell : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
  have hi : IntervalIntegrable (fun t : ℝ => 1 / t ^ 2)
      volume (m : ℝ) ((m : ℝ) + 1) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hcell]
    exact continuousOn_const.div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero 2 (hmR.trans_le ht.1).ne')
  rw [omega_cell, cell_interval]
  calc
    _ ≤ ∫ t in (m : ℝ)..(m : ℝ) + 1, K * (1 / t ^ 2) := by
      apply intervalIntegral.integral_mono_on hcell
        (clipped_integrable ha hab _ _) (hi.const_mul K)
      intro t ht
      by_cases habt : t ∈ Set.Icc a b
      · rw [Set.indicator_of_mem habt]
        exact actualEnergy_density_cap hN (hNmR.trans ht.1)
      · rw [Set.indicator_of_notMem habt]
        exact mul_nonneg hK (by positivity)
    _ = K * w m := by
      rw [intervalIntegral.integral_const_mul, actualEnergy_invSquare_cell hmp]

private lemma actualEnergy_datum_bounds {N m : ℕ} {a b : ℝ}
    (hN : 3 ≤ N) (hNa : (N : ℝ) ≤ a) (hab : a ≤ b)
    (hm : m ∈ Finset.Ico N (2 * N)) :
    0 ≤ datum N a b m ∧ datum N a b m ≤ 1 + 1 / Real.log (N : ℝ) := by
  have hmi := Finset.mem_Ico.mp hm
  have hne : m ≠ 2 * N := by omega
  have hmp : 0 < m := by omega
  have hw : 0 < w m := w_pos hmp
  have hLN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have ha : 1 < a :=
    (show (1 : ℝ) < N by exact_mod_cast (by omega : 1 < N)).trans_le hNa
  have hcap := actualEnergy_omega_cap hN ha hab hmi.1
  simp only [datum, if_neg hne]
  constructor
  · exact div_nonneg (mul_nonneg hLN.le (omega_nonneg ha m)) hw.le
  · apply (div_le_iff₀ hw).mpr
    calc
      Real.log (N : ℝ) * omega a b m ≤
          Real.log (N : ℝ) *
            (((Real.log (N : ℝ))⁻¹ + (Real.log (N : ℝ))⁻¹ ^ 2) * w m) :=
        mul_le_mul_of_nonneg_left hcap hLN.le
      _ = (1 + 1 / Real.log (N : ℝ)) * w m := by
        field_simp [hLN.ne']
        <;> ring

private lemma actualEnergy_le_constant {N : ℕ} (hN : 3 ≤ N)
    (a b t : ℝ) :
    (∑ m ∈ Finset.Ico N (2 * N), (coeff N a b m) ^ 2 / w m) ≤
      ∑ m ∈ Finset.Ico N (2 * N), w m * (datum N a b m - t) ^ 2 := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hmom := exact_moments hN a b
  have hcoeff (m : ℕ) (hm : m ∈ Finset.Ico N (2 * N)) :
      coeff N a b m = w m *
        (datum N a b m - c N a b 0 - c N a b 1 * ((m : ℝ) / N)) := by
    have hmi := Finset.mem_Ico.mp hm
    have hne : m ≠ 2 * N := by omega
    simp only [coeff, if_pos hmi, residual, if_neg hne]
  have hpoint (m : ℕ) (hm : m ∈ Finset.Ico N (2 * N)) :
      w m * (datum N a b m - t) ^ 2 =
        ((coeff N a b m) ^ 2 / w m +
          w m * (c N a b 0 + c N a b 1 * ((m : ℝ) / N) - t) ^ 2) +
          2 * (c N a b 0 - t) * coeff N a b m +
          (2 * c N a b 1 / (N : ℝ)) * ((m : ℝ) * coeff N a b m) := by
    have hw : w m ≠ 0 := (w_pos (by
      have := (Finset.mem_Ico.mp hm).1
      omega)).ne'
    simp only [hcoeff m hm]
    field_simp [hw, hNR]
    <;> ring
  have hsum :
      (∑ m ∈ Finset.Ico N (2 * N), w m * (datum N a b m - t) ^ 2) =
        (∑ m ∈ Finset.Ico N (2 * N), (coeff N a b m) ^ 2 / w m) +
        ∑ m ∈ Finset.Ico N (2 * N),
          w m * (c N a b 0 + c N a b 1 * ((m : ℝ) / N) - t) ^ 2 := by
    calc
      _ = ∑ m ∈ Finset.Ico N (2 * N),
          (((coeff N a b m) ^ 2 / w m +
            w m * (c N a b 0 + c N a b 1 * ((m : ℝ) / N) - t) ^ 2) +
            2 * (c N a b 0 - t) * coeff N a b m +
            (2 * c N a b 1 / (N : ℝ)) * ((m : ℝ) * coeff N a b m)) := by
        exact Finset.sum_congr rfl hpoint
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
          hmom.1, hmom.2, mul_zero, add_zero]
  have hnonneg : 0 ≤ ∑ m ∈ Finset.Ico N (2 * N),
      w m * (c N a b 0 + c N a b 1 * ((m : ℝ) / N) - t) ^ 2 := by
    apply Finset.sum_nonneg
    intro m hm
    exact mul_nonneg (w_pos (by
      have := (Finset.mem_Ico.mp hm).1
      omega)).le (sq_nonneg _)
  linarith [hsum]

/-- The original two-moment partial-cell coefficients have a uniform energy
bound supplied by the actual activation density, on the original full block. -/
theorem or6_partialCell_energy_bound {N : ℕ} {a b : ℝ} (hN : 3 ≤ N)
    (hNa : (N : ℝ) ≤ a) (hab : a ≤ b) :
    (∑ m ∈ Finset.Ico N (2 * N), (coeff N a b m) ^ 2 / w m) ≤
      (1 + 1 / Real.log (N : ℝ)) ^ 2 / (8 * (N : ℝ)) := by
  let B : ℝ := 1 + 1 / Real.log (N : ℝ)
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hmid (m : ℕ) (hm : m ∈ Finset.Ico N (2 * N)) :
      (datum N a b m - B / 2) ^ 2 ≤ B ^ 2 / 4 := by
    have hd := actualEnergy_datum_bounds hN hNa hab hm
    change 0 ≤ datum N a b m ∧ datum N a b m ≤ B at hd
    nlinarith [mul_nonneg hd.1 (sub_nonneg.mpr hd.2)]
  calc
    _ ≤ ∑ m ∈ Finset.Ico N (2 * N), w m * (datum N a b m - B / 2) ^ 2 :=
      actualEnergy_le_constant hN a b (B / 2)
    _ ≤ ∑ m ∈ Finset.Ico N (2 * N), w m * (B ^ 2 / 4) := by
      apply Finset.sum_le_sum
      intro m hm
      exact mul_le_mul_of_nonneg_left (hmid m hm)
        (w_pos (by have := (Finset.mem_Ico.mp hm).1; omega)).le
    _ = (B ^ 2 / 4) * (∑ m ∈ Finset.Ico N (2 * N), w m) := by
      rw [← Finset.sum_mul]
      ring
    _ = B ^ 2 / (8 * (N : ℝ)) := by
      rw [(discrete_weights hN).1]
      field_simp [hNR]
      <;> ring
    _ = _ := rfl

/-- Exact original projection facts consumed by the response adjoint. -/
theorem response_projection_interface {N : ℕ} (hN : 3 ≤ N) :
    (gram N 0 0 = ∑ m ∈ Finset.Ico N (2 * N), w m ∧
      gram N 0 1 = ∑ m ∈ Finset.Ico N (2 * N), w m * ((m : ℝ) / N) ∧
      gram N 1 0 = gram N 0 1 ∧
      gram N 1 1 = ∑ m ∈ Finset.Ico N (2 * N), w m * ((m : ℝ) / N) ^ 2) ∧
    0 < delta N ∧
    (∀ a b : ℝ,
      (∑ m ∈ Finset.Ico N (2 * N), coeff N a b m) = 0 ∧
      (∑ m ∈ Finset.Ico N (2 * N), (m : ℝ) * coeff N a b m) = 0) ∧
    (∀ (a b : ℝ) (m : ℕ), m ∈ Finset.Ico N (2 * N) →
      coeff N a b m = Real.log (N : ℝ) * omega a b m - c N a b 0 * w m -
        c N a b 1 * (w m * ((m : ℝ) / N))) := by
  exact ⟨gram_entries N, delta_pos hN, exact_moments hN,
    fun a b m hm => coeff_on (a := a) (b := b) hN hm⟩


end D5.S3.Arith.Robin.OriginalResidualPartialCellWeights
