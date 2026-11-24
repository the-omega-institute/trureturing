/- GID: D5/S3/Fourier/Concentration/DisjointCharacterEnvelope
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/DisjointCharacterEnvelope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A coefficient bound for disjoint products that retains the sums of the phases. -/

import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Ring.InfiniteSum

open Finset PowerSeries
open scoped PowerSeries

noncomputable section

namespace D5.S3.Fourier.Concentration.DisjointCharacterEnvelope

private def axis (z : ℂ) : ℂ⟦X⟧ := rescale z (PowerSeries.exp ℂ)

private def coeffMass (P : ℂ⟦X⟧) : ℝ := ∑' n : ℕ, ‖coeff n P‖

private def Budget (P : ℂ⟦X⟧) (b : ℝ) : Prop :=
  (Summable fun n : ℕ => ‖coeff n P‖) ∧ coeffMass P ≤ b

private theorem Budget.nonneg {P : ℂ⟦X⟧} {b : ℝ} (h : Budget P b) : 0 ≤ b :=
  (tsum_nonneg fun _ => norm_nonneg _).trans h.2

private theorem Budget.coeff_le {P : ℂ⟦X⟧} {b : ℝ} (h : Budget P b) (n : ℕ) :
    ‖coeff n P‖ ≤ b :=
  (h.1.le_tsum n fun _ _ => norm_nonneg _).trans h.2

private theorem norm_cauchy_mass (f g : ℕ → ℂ)
    (hf : Summable fun n => ‖f n‖) (hg : Summable fun n => ‖g n‖) :
    (∑' n : ℕ, ‖∑ ij ∈ antidiagonal n, f ij.1 * g ij.2‖) ≤
      (∑' n : ℕ, ‖f n‖) * ∑' n : ℕ, ‖g n‖ := by
  have hS : Summable (fun n : ℕ => ‖∑ ij ∈ antidiagonal n, f ij.1 * g ij.2‖) :=
    summable_norm_sum_mul_antidiagonal_of_summable_norm (f := f) (g := g) hf hg
  have hp : Summable (fun ij : ℕ × ℕ => ‖f ij.1‖ * ‖g ij.2‖) :=
    Summable.mul_of_nonneg (f := fun n => ‖f n‖) (g := fun n => ‖g n‖) hf hg
    (fun n => norm_nonneg (f n)) (fun n => norm_nonneg (g n))
  have hC : Summable (fun n : ℕ => ∑ ij ∈ antidiagonal n, ‖f ij.1‖ * ‖g ij.2‖) :=
    summable_sum_mul_antidiagonal_of_summable_mul
      (f := fun n => ‖f n‖) (g := fun n => ‖g n‖) hp
  calc
    _ ≤ ∑' n : ℕ, ∑ ij ∈ antidiagonal n, ‖f ij.1‖ * ‖g ij.2‖ := by
      refine hS.tsum_le_tsum (fun n => ?_) hC
      simpa only [norm_mul] using (norm_sum_le (antidiagonal n) fun ij => f ij.1 * g ij.2)
    _ = _ := (hf.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg hp).symm

private theorem Budget.mul {P Q : ℂ⟦X⟧} {a b : ℝ} (hP : Budget P a)
    (hQ : Budget Q b) : Budget (P * Q) (a * b) := by
  have hf : Summable (fun n : ℕ => ‖coeff n P‖) := hP.1
  have hg : Summable (fun n : ℕ => ‖coeff n Q‖) := hQ.1
  have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg
  have hmass : coeffMass (P * Q) ≤ coeffMass P * coeffMass Q := by
    simpa only [coeffMass, coeff_mul] using
      norm_cauchy_mass (fun n => coeff n P) (fun n => coeff n Q) hf hg
  refine ⟨?_, hmass.trans ?_⟩
  · simpa only [coeff_mul] using hs
  · exact mul_le_mul hP.2 hQ.2 (tsum_nonneg fun _ => norm_nonneg _) hP.nonneg

private theorem axis_norm_coeff (z : ℂ) (n : ℕ) :
    ‖coeff n (axis z)‖ = ‖z‖ ^ n / n.factorial := by
  rw [axis, coeff_rescale, coeff_exp, norm_mul, norm_pow]
  simp [div_eq_mul_inv]

private theorem axis_budget (z : ℂ) : Budget (axis z) (Real.exp ‖z‖) := by
  have h : HasSum (fun n : ℕ => ‖z‖ ^ n / (n.factorial : ℝ)) (Real.exp ‖z‖) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp ‖z‖
  have hs : HasSum (fun n : ℕ => ‖coeff n (axis z)‖) (Real.exp ‖z‖) := by
    simpa only [axis_norm_coeff] using h
  exact ⟨hs.summable, hs.tsum_eq.le⟩

private theorem tail_budget (z : ℂ) : Budget (1 - axis z) (Real.exp ‖z‖ - 1) := by
  have h : HasSum (fun n : ℕ => ‖z‖ ^ n / (n.factorial : ℝ)) (Real.exp ‖z‖) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp ‖z‖
  have hh := h.sub (hasSum_ite_eq (0 : ℕ) (1 : ℝ))
  have hs : HasSum (fun n : ℕ => ‖coeff n (1 - axis z)‖) (Real.exp ‖z‖ - 1) := by
    convert hh using 1
    ext n
    by_cases hn : n = 0
    · subst n
      simp only [map_sub, coeff_one, ite_true, axis, coeff_rescale, pow_zero,
        coeff_exp, Nat.factorial_zero, Nat.cast_one, div_one, map_one, one_mul, sub_self,
        norm_zero]
    · simp only [map_sub, coeff_one, ite_eq_right hn, zero_sub, norm_neg, axis_norm_coeff,
        sub_zero]
  exact ⟨hs.summable, hs.tsum_eq.le⟩

private abbrev BiSeries := PowerSeries (PowerSeries ℂ)

private def xAxis (a : ℂ) : BiSeries :=
  PowerSeries.map (PowerSeries.C (R := ℂ)) (axis a)

private def yAxis (a : ℂ) : BiSeries :=
  PowerSeries.C (axis a)

private theorem axis_add (a b : ℂ) : axis (a + b) = axis a * axis b :=
  (exp_mul_exp_eq_exp_add a b).symm

private theorem axis_zero : axis 0 = 1 := by
  simp [axis]

private theorem xAxis_add (a b : ℂ) : xAxis (a + b) = xAxis a * xAxis b := by
  simp only [xAxis, axis_add, map_mul]

private theorem yAxis_add (a b : ℂ) : yAxis (a + b) = yAxis a * yAxis b := by
  simp only [yAxis, axis_add, map_mul]

private theorem xAxis_zero : xAxis 0 = 1 := by simp [xAxis, axis_zero]

private theorem yAxis_zero : yAxis 0 = 1 := by simp [yAxis, axis_zero]

private theorem split_factor (a b : ℂ) :
    xAxis a + yAxis b - 1 =
      xAxis a * yAxis b * (1 + (xAxis (-a) - 1) * (1 - yAxis (-b))) := by
  have hx : xAxis a * xAxis (-a) = 1 := by rw [← xAxis_add, add_neg_cancel, xAxis_zero]
  have hy : yAxis b * yAxis (-b) = 1 := by rw [← yAxis_add, add_neg_cancel, yAxis_zero]
  calc
    _ = xAxis a * yAxis b + (1 - xAxis a) * (yAxis b - 1) := by ring
    _ = xAxis a * yAxis b + (xAxis a * xAxis (-a) - xAxis a) *
        (yAxis b - yAxis b * yAxis (-b)) := by rw [hx, hy]
    _ = _ := by ring

private def onBoth (P Q : ℂ⟦X⟧) : BiSeries :=
  PowerSeries.map (PowerSeries.C (R := ℂ)) P * PowerSeries.C Q

private theorem coeff_onBoth (m n : ℕ) (P Q : ℂ⟦X⟧) :
    coeff n (coeff m (onBoth P Q)) = coeff m P * coeff n Q := by
  simp [onBoth, coeff_mul_C, coeff_map, coeff_C_mul]

private theorem onBoth_mul (P Q P' Q' : ℂ⟦X⟧) :
    onBoth P Q * onBoth P' Q' = onBoth (P * P') (Q * Q') := by
  simp only [onBoth, map_mul]
  ring

private theorem prod_onBoth {J : Type*} (s : Finset J) (P Q : J → ℂ⟦X⟧) :
    ∏ j ∈ s, onBoth (P j) (Q j) = onBoth (∏ j ∈ s, P j) (∏ j ∈ s, Q j) := by
  classical
  induction s using Finset.induction with
  | empty => simp [onBoth]
  | insert j s hj ih => simp only [prod_insert hj, ih, onBoth_mul]

private theorem prod_axis {J : Type*} (s : Finset J) (a : J → ℂ) :
    ∏ j ∈ s, axis (a j) = axis (∑ j ∈ s, a j) := by
  classical
  induction s using Finset.induction with
  | empty => simp [axis_zero]
  | insert j s hj ih => simp only [prod_insert hj, ih, sum_insert hj, axis_add]

/-- The formal product whose local factors choose from either axis or neither. -/
def disjointSeries {J : Type*} (s : Finset J) (a b : J → ℂ) : BiSeries :=
  ∏ j ∈ s, (xAxis (a j) + yAxis (b j) - 1)

private theorem split_product {J : Type*} (s : Finset J) (a b : J → ℂ) :
    disjointSeries s a b =
      ∑ t ∈ s.powerset,
        onBoth (axis (∑ j ∈ s, a j) * ∏ j ∈ t, (axis (-a j) - 1))
          (axis (∑ j ∈ s, b j) * ∏ j ∈ t, (1 - axis (-b j))) := by
  simp only [disjointSeries, split_factor, prod_mul_distrib]
  simp only [xAxis, yAxis, ← map_prod, prod_axis, Finset.prod_one_add, mul_sum]
  apply sum_congr rfl
  intro t _
  have h (j : J) :
      ((PowerSeries.map (PowerSeries.C (R := ℂ))) (axis (-a j)) - 1) *
          (1 - PowerSeries.C (axis (-b j))) =
        onBoth (axis (-a j) - 1) (1 - axis (-b j)) := by
    simp only [onBoth, map_sub, map_one]
  simp only [h, prod_onBoth]
  exact onBoth_mul _ _ _ _

private theorem Budget.neg {P : ℂ⟦X⟧} {b : ℝ} (h : Budget P b) : Budget (-P) b := by
  simpa only [Budget, coeffMass, map_neg, norm_neg] using h

private theorem Budget.prod {J : Type*} (s : Finset J) (P : J → ℂ⟦X⟧) (B : J → ℝ)
    (h : ∀ j ∈ s, Budget (P j) (B j)) : Budget (∏ j ∈ s, P j) (∏ j ∈ s, B j) := by
  classical
  induction s using Finset.induction with
  | empty => simpa [axis_zero] using axis_budget 0
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    exact (h j (mem_insert_self j s)).mul (ih fun k hk => h k (mem_insert_of_mem hk))

private theorem coefficient_envelope_at_one {J : Type*} (s : Finset J) (a b : J → ℂ) (m n : ℕ) :
    ‖coeff n (coeff m (disjointSeries s a b))‖ ≤
      Real.exp (‖∑ j ∈ s, a j‖ + ‖∑ j ∈ s, b j‖) *
        ∏ j ∈ s, (1 + (Real.exp ‖a j‖ - 1) * (Real.exp ‖b j‖ - 1)) := by
  classical
  let A := Real.exp ‖∑ j ∈ s, a j‖
  let B := Real.exp ‖∑ j ∈ s, b j‖
  let u := fun j => Real.exp ‖a j‖ - 1
  let v := fun j => Real.exp ‖b j‖ - 1
  let P := fun t : Finset J => axis (∑ j ∈ s, a j) * ∏ j ∈ t, (axis (-a j) - 1)
  let Q := fun t : Finset J => axis (∑ j ∈ s, b j) * ∏ j ∈ t, (1 - axis (-b j))
  have hP (t : Finset J) : Budget (P t) (A * ∏ j ∈ t, u j) := by
    apply (axis_budget _).mul
    apply Budget.prod
    intro j _
    simpa [u, neg_sub] using (tail_budget (-a j)).neg
  have hQ (t : Finset J) : Budget (Q t) (B * ∏ j ∈ t, v j) := by
    apply (axis_budget _).mul
    apply Budget.prod
    intro j _
    simpa [v] using tail_budget (-b j)
  rw [split_product]
  simp only [map_sum, coeff_onBoth]
  calc
    _ ≤ ∑ t ∈ s.powerset, ‖coeff m (P t) * coeff n (Q t)‖ := norm_sum_le _ _
    _ ≤ ∑ t ∈ s.powerset, (A * ∏ j ∈ t, u j) * (B * ∏ j ∈ t, v j) := by
      apply sum_le_sum
      intro t _
      rw [norm_mul]
      exact mul_le_mul ((hP t).coeff_le m) ((hQ t).coeff_le n) (norm_nonneg _) (hP t).nonneg
    _ = A * B * ∑ t ∈ s.powerset, ∏ j ∈ t, u j * v j := by
      rw [mul_sum]
      apply sum_congr rfl
      intro t _
      rw [prod_mul_distrib]
      ring
    _ = _ := by rw [← Finset.prod_one_add, Real.exp_add]

private def scaleBoth (r : ℂ) : BiSeries →+* BiSeries :=
  (PowerSeries.map (rescale r)).comp (rescale (PowerSeries.C r))

private theorem coeff_scaleBoth (r : ℂ) (P : BiSeries) (m n : ℕ) :
    coeff n (coeff m (scaleBoth r P)) = r ^ (m + n) * coeff n (coeff m P) := by
  simp only [scaleBoth, RingHom.comp_apply, coeff_map, coeff_rescale, ← map_pow, coeff_C_mul]
  rw [pow_add]
  ring

private theorem scaleBoth_onBoth (r : ℂ) (P Q : ℂ⟦X⟧) :
    scaleBoth r (onBoth P Q) = onBoth (rescale r P) (rescale r Q) := by
  apply PowerSeries.ext
  intro m
  apply PowerSeries.ext
  intro n
  simp only [coeff_scaleBoth, coeff_onBoth, coeff_rescale, pow_add]
  ring

private theorem scaleBoth_disjoint {J : Type*} (r : ℂ) (s : Finset J) (a b : J → ℂ) :
    scaleBoth r (disjointSeries s a b) =
      disjointSeries s (fun j => r * a j) (fun j => r * b j) := by
  have hx (z : ℂ) : xAxis z = onBoth (axis z) 1 := by simp [xAxis, onBoth]
  have hy (z : ℂ) : yAxis z = onBoth 1 (axis z) := by simp [yAxis, onBoth]
  have haxis (z : ℂ) : rescale r (axis z) = axis (r * z) := by
    rw [axis, axis, rescale_rescale, mul_comm z r]
  simp only [disjointSeries, map_prod, map_sub, map_add, map_one, hx, hy, scaleBoth_onBoth, haxis]

/-- Bound a disjoint coefficient using the sums of its two complex phase families. -/
theorem coefficient_envelope {J : Type*} (s : Finset J) (a b : J → ℂ) (m n : ℕ)
    (r : ℝ) (hr : 0 < r) :
    let phasePart := Real.exp
    ‖coeff n (coeff m (disjointSeries s a b))‖ ≤
      phasePart (r * (‖∑ j ∈ s, a j‖ + ‖∑ j ∈ s, b j‖)) *
        (∏ j ∈ s, (1 + (Real.exp (r * ‖a j‖) - 1) * (Real.exp (r * ‖b j‖) - 1))) /
        r ^ (m + n) := by
  dsimp only
  have h := coefficient_envelope_at_one s (fun j => (r : ℂ) * a j)
    (fun j => (r : ℂ) * b j) m n
  rw [← scaleBoth_disjoint, coeff_scaleBoth] at h
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    ← Finset.mul_sum] at h
  rw [le_div_iff₀ (pow_pos hr _), mul_comm]
  simpa only [mul_add] using h

end D5.S3.Fourier.Concentration.DisjointCharacterEnvelope
