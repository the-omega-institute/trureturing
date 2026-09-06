/- GID: D5/S3/Weil/ZetaBridge/WeilEvenFourierObservationTail
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilEvenFourierObservationTail
   mirror-E: none(waiver:analytic-bound-with-paper-Fourier-identification)
   anchors: []
   digest: Control the complete complex-frequency observation of an even Fourier tail, with absolute convergence and cubic cutoff decay. -/

import D5.S3.Weil.ZetaBridge.WeilInfiniteComplementLeakage
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Even Fourier observation of the entire exterior coefficient sequence

Use the same window [-L/2,L/2], plus-sign Fourier transform, and phase-adjusted
cosine basis as the actual Weil lane. For n>0 its Fourier coefficient is
  2*sqrt(2/L)*z*sin(L*z/2)/(z^2-(2*pi*n/L)^2).
For n=N+j+1, collecting the scalar factor gives `evenExteriorResponse` below.
The complex-frequency restriction excludes every denominator zero. The
rational expression is not asserted to represent removable values elsewhere.

The main theorem proves absolute convergence and an N^-3 squared observation
bound for arbitrary square-summable complex coefficients, with no terminal
Fourier cutoff, smoothness, boundary cancellation, or ground-state assumption.
The L2 Fourier-series identification, prolate model projection and dyadic
rounding argument are proved on paper in the existing RH theory volume.
No new Weil form or assumed Xi convergence is introduced here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Weil.ZetaBridge.WeilEvenFourierObservationTail

open Filter
open scoped BigOperators Topology

private def exteriorIndex (N j : ℕ) : ℝ := (N : ℝ) + (j : ℝ) + 1
private def inverseFourth (N j : ℕ) : ℝ := 1 / exteriorIndex N j ^ 4
private def coefficientMajorant (N j : ℕ) : ℝ := 4 / (3 * exteriorIndex N j ^ 2)
private def cauchyTerm (N : ℕ) (w : ℂ) (v : ℕ → ℂ) (j : ℕ) : ℂ :=
  v j / ((exteriorIndex N j : ℂ) ^ 2 - w ^ 2)

/-- The complete exterior response in the canonical phase-adjusted even
Fourier basis, on the pole-free band used by the theorem below. -/
def evenExteriorResponse (L : ℝ) (N : ℕ) (v : ℕ → ℂ) (z : ℂ) : ℂ :=
  ((-L / (2 * Real.pi ^ 2) * Real.sqrt (2 * L) : ℝ) : ℂ) *
    (z * Complex.sin (((L / 2 : ℝ) : ℂ) * z)) *
    ∑' j : ℕ, cauchyTerm N (z * ((L / (2 * Real.pi) : ℝ) : ℂ)) v j

private theorem inverse_fourth_step {x : ℝ} (hx : 0 < x) :
    1 / (x + 1) ^ 4 ≤ 1 / (3 * x ^ 3) - 1 / (3 * (x + 1) ^ 3) := by
  have hx1 : x + 1 ≠ 0 := ne_of_gt (by linarith)
  have hid : (1 / (3 * x ^ 3) - 1 / (3 * (x + 1) ^ 3)) -
      1 / (x + 1) ^ 4 = (6 * x ^ 2 + 4 * x + 1) / (3 * x ^ 3 * (x + 1) ^ 4) := by
    field_simp [hx.ne', hx1]
    <;> ring
  apply sub_nonneg.mp
  rw [hid]
  positivity

private theorem fourth_partial {N : ℕ} (hN : 0 < N) (M : ℕ) :
    (∑ j ∈ Finset.range M, inverseFourth N j) ≤
      1 / (3 * (N : ℝ) ^ 3) - 1 / (3 * ((N : ℝ) + (M : ℝ)) ^ 3) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ]
      have hs := inverse_fourth_step (show 0 < (N : ℝ) + (M : ℝ) by positivity)
      dsimp [inverseFourth, exteriorIndex] at ih ⊢
      simp only [Nat.cast_succ, ← add_assoc]
      linarith

private theorem majorant_partial {N : ℕ} (hN : 0 < N) (M : ℕ) :
    (∑ j ∈ Finset.range M, coefficientMajorant N j ^ 2) ≤
      16 / (27 * (N : ℝ) ^ 3) := by
  have ht := fourth_partial hN M
  have hp : 0 ≤ 1 / (3 * ((N : ℝ) + (M : ℝ)) ^ 3) := by positivity
  have hb : (∑ j ∈ Finset.range M, inverseFourth N j) ≤
      1 / (3 * (N : ℝ) ^ 3) := by linarith
  calc
    _ = (16 / 9 : ℝ) * ∑ j ∈ Finset.range M, inverseFourth N j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have hn : exteriorIndex N j ≠ 0 := ne_of_gt (by
        dsimp [exteriorIndex]
        positivity)
      dsimp [coefficientMajorant, inverseFourth]
      field_simp [hn]
      <;> ring
    _ ≤ (16 / 9 : ℝ) * (1 / (3 * (N : ℝ) ^ 3)) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by
      have hn : (N : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hN)
      field_simp [hn]
      <;> ring

private theorem majorant_summable {N : ℕ} (hN : 0 < N) :
    Summable (fun j : ℕ => coefficientMajorant N j ^ 2) :=
  summable_of_sum_range_le (fun _ => sq_nonneg _) (majorant_partial hN)

private theorem term_norm_le {N : ℕ} (hN : 0 < N)
    {w : ℂ} (hw : ‖w‖ ≤ (N : ℝ) / 2) (v : ℕ → ℂ) (j : ℕ) :
    ‖cauchyTerm N w v j‖ ≤ ‖v j‖ * coefficientMajorant N j := by
  let n : ℝ := exteriorIndex N j
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hn : 0 < n := by dsimp [n, exteriorIndex]; positivity
  have hNn : (N : ℝ) ≤ n := by
    dsimp [n, exteriorIndex]
    linarith [show (0 : ℝ) ≤ (j : ℝ) from Nat.cast_nonneg j]
  have hw0 := norm_nonneg w
  have hwn : ‖w‖ ≤ n / 2 := hw.trans (by linarith)
  have hw2 : ‖w‖ ^ 2 ≤ n ^ 2 / 4 := by
    have ht := pow_le_pow_left₀ hw0 hwn 2
    nlinarith
  have hreverse := norm_sub_norm_le ((n : ℂ) ^ 2) (w ^ 2)
  simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn] at hreverse
  have hden : (3 / 4 : ℝ) * n ^ 2 ≤ ‖(n : ℂ) ^ 2 - w ^ 2‖ := by linarith
  have hsmall : 0 < (3 / 4 : ℝ) * n ^ 2 := by positivity
  have hinv : ‖((n : ℂ) ^ 2 - w ^ 2)⁻¹‖ ≤ 4 / (3 * n ^ 2) := by
    calc
      _ = 1 / ‖(n : ℂ) ^ 2 - w ^ 2‖ := by rw [norm_inv, one_div]
      _ ≤ 1 / ((3 / 4 : ℝ) * n ^ 2) := one_div_le_one_div_of_le hsmall hden
      _ = _ := by field_simp [hn.ne']; ring
  change ‖v j / ((n : ℂ) ^ 2 - w ^ 2)‖ ≤ ‖v j‖ * (4 / (3 * n ^ 2))
  rw [div_eq_mul_inv, norm_mul]
  exact mul_le_mul_of_nonneg_left hinv (norm_nonneg _)

private theorem cauchy_bound {N : ℕ} (hN : 0 < N)
    {w : ℂ} (hw : ‖w‖ ≤ (N : ℝ) / 2)
    (v : ℕ → ℂ) (hv : Summable (fun j => ‖v j‖ ^ 2)) :
    Summable (fun j => ‖cauchyTerm N w v j‖) ∧
    ‖∑' j : ℕ, cauchyTerm N w v j‖ ^ 2 ≤
      (16 / (27 * (N : ℝ) ^ 3)) * ∑' j : ℕ, ‖v j‖ ^ 2 := by
  have hmaj := majorant_summable hN
  have hs : Summable (fun j => ‖cauchyTerm N w v j‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun j => ?_) ((hv.add hmaj).div_const 2)
    have ht := term_norm_le hN hw v j
    nlinarith [sq_nonneg (‖v j‖ - coefficientMajorant N j)]
  refine ⟨hs, ?_⟩
  have hp (M : ℕ) :
      ‖∑ j ∈ Finset.range M, cauchyTerm N w v j‖ ^ 2 ≤
        (16 / (27 * (N : ℝ) ^ 3)) * ∑' j : ℕ, ‖v j‖ ^ 2 := by
    have htri : ‖∑ j ∈ Finset.range M, cauchyTerm N w v j‖ ≤
        ∑ j ∈ Finset.range M, ‖v j‖ * coefficientMajorant N j :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => term_norm_le hN hw v j)
    calc
      _ ≤ (∑ j ∈ Finset.range M, ‖v j‖ * coefficientMajorant N j) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) htri 2
      _ ≤ (∑ j ∈ Finset.range M, ‖v j‖ ^ 2) *
          (∑ j ∈ Finset.range M, coefficientMajorant N j ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ (∑' j : ℕ, ‖v j‖ ^ 2) * (16 / (27 * (N : ℝ) ^ 3)) :=
        mul_le_mul
          (Summable.sum_le_tsum (Finset.range M) (fun _ _ => sq_nonneg _) hv)
          (majorant_partial hN M)
          (Finset.sum_nonneg fun _ _ => sq_nonneg _)
          (tsum_nonneg fun _ => sq_nonneg _)
      _ = _ := mul_comm _ _
  exact le_of_tendsto (((hs.of_norm.hasSum.tendsto_sum_nat).norm).pow 2)
    (Eventually.of_forall hp)

/-- A genuine complex-frequency, infinite-tail estimate. In the canonical
Fourier identification the output is the transform of the entire even
exterior component. Its squared operator norm decays as N^-3. All series
are proved absolutely convergent; no finite terminal tail is substituted. -/
theorem even_exterior_fourier_observation_bound
    {L : ℝ} (hL : 0 < L) {N : ℕ} (hN : 0 < N)
    (v : ℕ → ℂ) (hv : Summable (fun j => ‖v j‖ ^ 2))
    (z : ℂ) (hz : L * ‖z‖ ≤ Real.pi * (N : ℝ)) :
    Summable (fun j => ‖cauchyTerm N (z * ((L / (2 * Real.pi) : ℝ) : ℂ)) v j‖) ∧
    ‖evenExteriorResponse L N v z‖ ^ 2 ≤
      (8 * L ^ 3 / (27 * Real.pi ^ 4 * (N : ℝ) ^ 3)) *
        ‖z * Complex.sin (((L / 2 : ℝ) : ℂ) * z)‖ ^ 2 *
          ∑' j : ℕ, ‖v j‖ ^ 2 := by
  have hfreq : 0 < L / (2 * Real.pi) := by positivity
  have hw : ‖z * ((L / (2 * Real.pi) : ℝ) : ℂ)‖ ≤ (N : ℝ) / 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hfreq]
    have h : L * ‖z‖ / (2 * Real.pi) ≤ (N : ℝ) / 2 := by
      apply (div_le_iff₀ (show 0 < 2 * Real.pi by positivity)).mpr
      nlinarith [hz]
    convert h using 1 <;> ring
  obtain ⟨hs, hb⟩ := cauchy_bound hN hw v hv
  refine ⟨hs, ?_⟩
  let A : ℝ := -L / (2 * Real.pi ^ 2) * Real.sqrt (2 * L)
  have hA : A ^ 2 = L ^ 3 / (2 * Real.pi ^ 4) := by
    dsimp [A]
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * L)]
    field_simp [Real.pi_ne_zero]
    <;> ring
  have hAc : ‖(A : ℂ)‖ ^ 2 = A ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  change ‖(A : ℂ) * _ * _‖ ^ 2 ≤ _
  rw [norm_mul, norm_mul, mul_pow, mul_pow, hAc, hA]
  calc
    _ ≤ (L ^ 3 / (2 * Real.pi ^ 4)) *
        ‖z * Complex.sin (((L / 2 : ℝ) : ℂ) * z)‖ ^ 2 *
          ((16 / (27 * (N : ℝ) ^ 3)) * ∑' j : ℕ, ‖v j‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by
      have hn : (N : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hN)
      field_simp [Real.pi_ne_zero, hn]
      <;> ring

#print axioms even_exterior_fourier_observation_bound

end D5.S3.Weil.ZetaBridge.WeilEvenFourierObservationTail
