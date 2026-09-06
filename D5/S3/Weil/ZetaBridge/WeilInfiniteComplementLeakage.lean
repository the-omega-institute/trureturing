/- GID: D5/S3/Weil/ZetaBridge/WeilInfiniteComplementLeakage
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilInfiniteComplementLeakage
   mirror-E: none(waiver:infinite-dimensional-analytic-estimate)
   anchors: []
   digest: Control the low-frequency mass of every square-summable exterior Fourier tail. -/

import D5.S3.Weil.ZetaCore.ExplicitFormula
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The infinite Galerkin complement has quantitatively little low-frequency mass

For the window I=[-L/2,L/2], use the orthonormal Fourier basis
  (-1)^n / sqrt(L) * exp(2*pi*i*n*x/L).
Remove the modes |n|<=N. The two remaining coefficient sequences are arbitrary
square-summable complex sequences; there is no upper Galerkin cutoff.
At physical frequency t=(2*pi/L)*s the squared Fourier transform is
  L/pi^2 * sin(pi*s)^2 * |C(N+s,u)-C(N-s,v)|^2,
where C(d,u)=sum_{j>=0} u_j/(d+j+1).

This file proves absolute convergence and continuity on |s|<=N/4, then bounds
the normalized integral of this exact Cauchy density by
  4/(3*pi^2) * (sum |u_j|^2 + sum |v_j|^2).
The Fourier-series identification and the Plancherel identification of the
coefficient mass are explained in the existing RH theory volume. They are not
silently assumed to be theorems of this file. All infinite series and the
integral occurring in the theorem are proved convergent/integrable.

This is the low-frequency part of a full-space complement lower bound for the
actual arithmetic Weil form. It is not codimension-one coercivity, a proof of
a simple-even ground mode, or an assertion that a finite matrix certifies RH.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaBridge.WeilInfiniteComplementLeakage

open Filter MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

private def cauchyHalf (d : ℝ) (u : ℕ → ℂ) : ℂ :=
  ∑' j : ℕ, u j * (((d + (j : ℝ) + 1)⁻¹ : ℝ) : ℂ)

private def coefficientMass (u v : ℕ → ℂ) : ℝ :=
  (∑' j : ℕ, ‖u j‖ ^ 2) + ∑' j : ℕ, ‖v j‖ ^ 2

/-- The squared Fourier density, in the dimensionless frequency s=t*L/(2*pi),
of the full exterior Fourier tail. u and v are the coefficients at
N+j+1 and -(N+j+1), respectively, in the phase-adjusted orthonormal basis.
The theorem below uses this expression only on |s|<=N/4, away from every pole. -/
def exteriorFourierDensity (L : ℝ) (N : ℕ) (u v : ℕ → ℂ) (s : ℝ) : ℝ :=
  L / Real.pi ^ 2 * Real.sin (Real.pi * s) ^ 2 *
    ‖cauchyHalf ((N : ℝ) + s) u - cauchyHalf ((N : ℝ) - s) v‖ ^ 2

private theorem inverse_step {x : ℝ} (hx : 0 < x) :
    ((x + 1)⁻¹) ^ 2 ≤ x⁻¹ - (x + 1)⁻¹ := by
  have hx1 : 0 < x + 1 := by linarith
  have heq : x⁻¹ - (x + 1)⁻¹ = (x * (x + 1))⁻¹ := by
    field_simp [ne_of_gt hx, ne_of_gt hx1]
    <;> ring
  have hpow : ((x + 1)⁻¹) ^ 2 = ((x + 1) ^ 2)⁻¹ := by
    field_simp [ne_of_gt hx1]
  rw [heq, hpow]
  exact (inv_le_inv₀ (by positivity) (by positivity)).2 (by nlinarith)

private theorem inverse_square_partial {d : ℝ} (hd : 0 < d) (M : ℕ) :
    (∑ j ∈ Finset.range M, ((d + (j : ℝ) + 1)⁻¹) ^ 2) ≤
      d⁻¹ - (d + (M : ℝ))⁻¹ := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ]
      have hstep := inverse_step (show 0 < d + (M : ℝ) by positivity)
      simp only [Nat.cast_succ, add_assoc]
      simp only [add_assoc] at hstep
      linarith

private theorem inverse_square_partial_le {d : ℝ} (hd : 0 < d) (M : ℕ) :
    (∑ j ∈ Finset.range M, ((d + (j : ℝ) + 1)⁻¹) ^ 2) ≤ d⁻¹ := by
  have h := inverse_square_partial hd M
  have hpos : 0 ≤ (d + (M : ℝ))⁻¹ := by positivity
  linarith

private theorem inverse_square_summable {d : ℝ} (hd : 0 < d) :
    Summable (fun j : ℕ => ((d + (j : ℝ) + 1)⁻¹) ^ 2) :=
  summable_of_sum_range_le (fun _ => sq_nonneg _) (inverse_square_partial_le hd)

private theorem cauchyHalf_norm_summable {d : ℝ} (hd : 0 < d)
    (u : ℕ → ℂ) (hu : Summable (fun j => ‖u j‖ ^ 2)) :
    Summable (fun j : ℕ => ‖u j * (((d + (j : ℝ) + 1)⁻¹ : ℝ) : ℂ)‖) := by
  have hdom := (hu.add (inverse_square_summable hd)).div_const 2
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hdom
  intro j
  have hp : 0 ≤ (d + (j : ℝ) + 1)⁻¹ := by positivity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]
  nlinarith [sq_nonneg (‖u j‖ - (d + (j : ℝ) + 1)⁻¹)]

private theorem cauchyHalf_bound {d : ℝ} (hd : 0 < d)
    (u : ℕ → ℂ) (hu : Summable (fun j => ‖u j‖ ^ 2)) :
    ‖cauchyHalf d u‖ ^ 2 ≤ (∑' j : ℕ, ‖u j‖ ^ 2) * d⁻¹ := by
  have hs := (cauchyHalf_norm_summable hd u hu).of_norm
  have hp (M : ℕ) :
      ‖∑ j ∈ Finset.range M,
        u j * (((d + (j : ℝ) + 1)⁻¹ : ℝ) : ℂ)‖ ^ 2 ≤
        (∑' j : ℕ, ‖u j‖ ^ 2) * d⁻¹ := by
    have htri :
        ‖∑ j ∈ Finset.range M,
          u j * (((d + (j : ℝ) + 1)⁻¹ : ℝ) : ℂ)‖ ≤
        ∑ j ∈ Finset.range M, ‖u j‖ * (d + (j : ℝ) + 1)⁻¹ := by
      calc
        _ ≤ ∑ j ∈ Finset.range M,
            ‖u j * (((d + (j : ℝ) + 1)⁻¹ : ℝ) : ℂ)‖ := norm_sum_le _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j _
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by positivity : 0 < (d + (j : ℝ) + 1)⁻¹)]
    calc
      _ ≤ (∑ j ∈ Finset.range M, ‖u j‖ * (d + (j : ℝ) + 1)⁻¹) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) htri 2
      _ ≤ (∑ j ∈ Finset.range M, ‖u j‖ ^ 2) *
          (∑ j ∈ Finset.range M, ((d + (j : ℝ) + 1)⁻¹) ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ _ := mul_le_mul
        (Summable.sum_le_tsum (Finset.range M) (fun _ _ => sq_nonneg _) hu)
        (inverse_square_partial_le hd M)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
        (tsum_nonneg (fun _ => sq_nonneg _))
  exact le_of_tendsto ((hs.hasSum.tendsto_sum_nat.norm).pow 2)
    (Eventually.of_forall hp)

private theorem cauchyHalf_continuousOn {d : ℝ} (hd : 0 < d)
    (u : ℕ → ℂ) (hu : Summable (fun j => ‖u j‖ ^ 2)) :
    ContinuousOn (fun x : ℝ => cauchyHalf x u) (Ici d) := by
  apply continuousOn_tsum
    (u := fun j : ℕ => ‖u j * (((d + (j : ℝ) + 1)⁻¹ : ℝ) : ℂ)‖)
  · intro j
    have hc : ContinuousOn (fun x : ℝ => (x + (j : ℝ) + 1)⁻¹) (Ici d) :=
      ((continuousOn_id.add continuousOn_const).add continuousOn_const).inv₀
        (fun x hx => by
          have hx0 : 0 < x := lt_of_lt_of_le hd hx
          exact ne_of_gt (by positivity))
    exact continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hc)
  · exact cauchyHalf_norm_summable hd u hu
  · intro j x hx
    have hx0 : 0 < x := lt_of_lt_of_le hd hx
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < (x + (j : ℝ) + 1)⁻¹),
      abs_of_pos (by positivity : 0 < (d + (j : ℝ) + 1)⁻¹)]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (inv_le_inv₀ (by positivity) (by positivity)).2 (by linarith [hx])

private theorem norm_sub_sq (z w : ℂ) :
    ‖z - w‖ ^ 2 ≤ 2 * (‖z‖ ^ 2 + ‖w‖ ^ 2) := by
  have h := norm_sub_le z w
  have hz := norm_nonneg z
  have hw := norm_nonneg w
  have hzw := norm_nonneg (z - w)
  have hsq := pow_le_pow_left₀ hzw h 2
  nlinarith [sq_nonneg (‖z‖ - ‖w‖)]

private theorem response_bound {N : ℕ} (hN : 0 < N)
    (u v : ℕ → ℂ)
    (hu : Summable (fun j => ‖u j‖ ^ 2))
    (hv : Summable (fun j => ‖v j‖ ^ 2))
    {s : ℝ} (hs : |s| ≤ (N : ℝ) / 4) :
    ‖cauchyHalf ((N : ℝ) + s) u - cauchyHalf ((N : ℝ) - s) v‖ ^ 2 ≤
      8 / (3 * (N : ℝ)) * coefficientMass u v := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hlo : -(N : ℝ) / 4 ≤ s := by linarith [(abs_le.mp hs).1]
  have hhi : s ≤ (N : ℝ) / 4 := (abs_le.mp hs).2
  have hp : 0 < (N : ℝ) + s := by linarith
  have hm : 0 < (N : ℝ) - s := by linarith
  have hu' := cauchyHalf_bound hp u hu
  have hv' := cauchyHalf_bound hm v hv
  have hpi : ((N : ℝ) + s)⁻¹ ≤ 4 / (3 * (N : ℝ)) := by
    have h := (inv_le_inv₀ hp (by positivity : 0 < 3 * (N : ℝ) / 4)).2
      (show 3 * (N : ℝ) / 4 ≤ (N : ℝ) + s by linarith)
    simpa only [inv_div] using h
  have hmi : ((N : ℝ) - s)⁻¹ ≤ 4 / (3 * (N : ℝ)) := by
    have h := (inv_le_inv₀ hm (by positivity : 0 < 3 * (N : ℝ) / 4)).2
      (show 3 * (N : ℝ) / 4 ≤ (N : ℝ) - s by linarith)
    simpa only [inv_div] using h
  have hu'' := hu'.trans (mul_le_mul_of_nonneg_left hpi
    (tsum_nonneg (fun j : ℕ => sq_nonneg ‖u j‖)))
  have hv'' := hv'.trans (mul_le_mul_of_nonneg_left hmi
    (tsum_nonneg (fun j : ℕ => sq_nonneg ‖v j‖)))
  have hsub := norm_sub_sq (cauchyHalf ((N : ℝ) + s) u)
    (cauchyHalf ((N : ℝ) - s) v)
  dsimp [coefficientMass]
  nlinarith

private theorem density_bound {N : ℕ} (hN : 0 < N) {L : ℝ} (hL : 0 < L)
    (u v : ℕ → ℂ)
    (hu : Summable (fun j => ‖u j‖ ^ 2))
    (hv : Summable (fun j => ‖v j‖ ^ 2))
    {s : ℝ} (hs : |s| ≤ (N : ℝ) / 4) :
    exteriorFourierDensity L N u v s ≤
      8 * L / (3 * Real.pi ^ 2 * (N : ℝ)) * coefficientMass u v := by
  have hresp := response_bound hN u v hu hv hs
  have hsin : Real.sin (Real.pi * s) ^ 2 ≤ 1 := Real.sin_sq_le_one _
  unfold exteriorFourierDensity
  calc
    _ ≤ L / Real.pi ^ 2 * 1 *
        ‖cauchyHalf ((N : ℝ) + s) u - cauchyHalf ((N : ℝ) - s) v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsin (by positivity)) (sq_nonneg _)
    _ ≤ L / Real.pi ^ 2 * 1 *
        (8 / (3 * (N : ℝ)) * coefficientMass u v) :=
      mul_le_mul_of_nonneg_left hresp (by positivity)
    _ = _ := by
      have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
      field_simp [hNr, Real.pi_ne_zero]
      <;> ring

private theorem density_continuousOn {N : ℕ} (hN : 0 < N) (L : ℝ)
    (u v : ℕ → ℂ)
    (hu : Summable (fun j => ‖u j‖ ^ 2))
    (hv : Summable (fun j => ‖v j‖ ^ 2)) :
    ContinuousOn (exteriorFourierDensity L N u v)
      (Icc (-(N : ℝ) / 4) ((N : ℝ) / 4)) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hd : 0 < 3 * (N : ℝ) / 4 := by positivity
  have hpu := (cauchyHalf_continuousOn hd u hu).comp
    (continuousOn_const.add continuousOn_id) (by
      intro s hs
      change 3 * (N : ℝ) / 4 ≤ (N : ℝ) + s
      linarith [hs.1])
  have hpv := (cauchyHalf_continuousOn hd v hv).comp
    (continuousOn_const.sub continuousOn_id) (by
      intro s hs
      change 3 * (N : ℝ) / 4 ≤ (N : ℝ) - s
      linarith [hs.2])
  exact (continuousOn_const.mul
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn.pow 2)).mul
      ((hpu.sub hpv).norm.pow 2)

/-- Every infinite exterior Fourier tail has at most 4/(3*pi^2) of its
coefficient mass in the physical band |t|<=pi*N/(2*L).

The statement includes interval integrability, so the estimate cannot hold
merely because Lean assigns zero to an undefined integral. The two inputs are
arbitrary square-summable sequences, with no finite upper cutoff and no
boundary-vanishing, real-valuedness, parity, or spectral assumption. -/
theorem infinite_complement_low_frequency_mass {N : ℕ} (hN : 0 < N)
    {L : ℝ} (hL : 0 < L) (u v : ℕ → ℂ)
    (hu : Summable (fun j => ‖u j‖ ^ 2))
    (hv : Summable (fun j => ‖v j‖ ^ 2)) :
    IntervalIntegrable (exteriorFourierDensity L N u v) volume
      (-(N : ℝ) / 4) ((N : ℝ) / 4) ∧
    (1 / L) * (∫ s in (-(N : ℝ) / 4)..((N : ℝ) / 4),
      exteriorFourierDensity L N u v s) ≤
        (4 / (3 * Real.pi ^ 2)) *
          ((∑' j : ℕ, ‖u j‖ ^ 2) + ∑' j : ℕ, ‖v j‖ ^ 2) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hab : -(N : ℝ) / 4 ≤ (N : ℝ) / 4 := by linarith
  have hc := density_continuousOn hN L u v hu hv
  have hi : IntervalIntegrable (exteriorFourierDensity L N u v) volume
      (-(N : ℝ) / 4) ((N : ℝ) / 4) := by
    have hcu : ContinuousOn (exteriorFourierDensity L N u v)
        (uIcc (-(N : ℝ) / 4) ((N : ℝ) / 4)) := by
      simpa only [uIcc_of_le hab] using hc
    exact hcu.intervalIntegrable
  refine ⟨hi, ?_⟩
  let C : ℝ := 8 * L / (3 * Real.pi ^ 2 * (N : ℝ)) * coefficientMass u v
  have hint :
      (∫ s in (-(N : ℝ) / 4)..((N : ℝ) / 4), exteriorFourierDensity L N u v s) ≤
      ((N : ℝ) / 2) * C := by
    calc
      _ ≤ ∫ _s in (-(N : ℝ) / 4)..((N : ℝ) / 4), C := by
        apply intervalIntegral.integral_mono_on hab hi intervalIntegrable_const
        intro s hs
        apply density_bound hN hL u v hu hv
        exact abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
      _ = _ := by rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; ring
  have h := mul_le_mul_of_nonneg_left hint (by positivity : 0 ≤ 1 / L)
  calc
    _ ≤ (1 / L) * ((N : ℝ) / 2 * C) := h
    _ = _ := by
      dsimp [C, coefficientMass]
      field_simp [ne_of_gt hL, ne_of_gt hNr, Real.pi_ne_zero]
      <;> ring

#print axioms infinite_complement_low_frequency_mass

end
end D5.S3.Weil.ZetaBridge.WeilInfiniteComplementLeakage
