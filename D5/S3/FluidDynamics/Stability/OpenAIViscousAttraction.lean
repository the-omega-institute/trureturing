/- GID: D5/S3/FluidDynamics/Stability/OpenAIViscousAttraction
   generality: G
   mirror-B: D5/B/S3/FluidDynamics/Stability/OpenAIViscousAttraction
   mirror-E: none(waiver:actual-ODE-and-forced-periodic-field)
   anchors: []
   utility: none
   digest: Source-faithful OpenAI viscous norm estimates give a sharp attraction tube and an actual forced-NS shear consumer. -/

import D5.S3.FluidDynamics.Fourier.ToralIsogenyShearNS
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Module

/-!
The three private norm lemmas below are adapted from OpenAI,
NavierStokes/ViscousPropagator.lean, commit
f9e8bc5b38b6e212696e8a30e3e91517af887bbd, Apache-2.0.
Original names: hasDerivWithinAt_norm_of_ne_zero,
norm_le_initial_add_integral, weighted_norm_le_initial_add_integral.
Changes: namespace, private visibility and local helper names; upstream-only
imports are replaced by the Mathlib imports actually needed here. Original
right-derivative and closed-interval continuity hypotheses are preserved.
The upstream file has no separate copyright notice. Attribution is retained
without supplying an invented individual author or copyright holder.

The public additions consume these helpers: an exact nonzero-initial-data
bounded-forcing tube, and a physical consumer built from the preceding actual
periodic shear. No upstream terminal NS theorem is restated as an axiom.
No repository toolchain pin is changed. The upstream endpoint theorems cover
forced C/D breakdown; they are not global stability assumptions.

All statements about trajectories require the displayed actual differential
equation on the displayed interval. General NS solution existence, a general
stationary solution, nonlinear transverse stability and uniqueness outside
the shear family are not proved here. The certified state norm in the shear
consumer is the actual amplitude, recovered by a fixed evaluation; the field
error bound is uniform over space and over both components.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

namespace D5.S3.FluidDynamics.Stability.OpenAIViscousAttraction

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private theorem norm_derivative {u : ℝ → H} {u' : H} {s : Set ℝ} {t : ℝ}
    (hu : HasDerivWithinAt u u' s t) (hne : u t ≠ 0) :
    HasDerivWithinAt (fun x => ‖u x‖) (⟪u t, u'⟫_ℝ / ‖u t‖) s t := by
  have hn : ‖u t‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  have hs := hu.norm_sq.sqrt (pow_ne_zero 2 hn)
  simpa only [Real.sqrt_sq_eq_abs, abs_norm,
    mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)] using hs

private theorem dissipative_norm_bound
    {a b : ℝ} {u f : ℝ → H} (A : ℝ → H →L[ℝ] H)
    (hu : ContinuousOn u (Icc a b)) (hf : Continuous f)
    (hode : ∀ t ∈ Ico a b,
      HasDerivWithinAt u (A t (u t) + f t) (Ici t) t)
    (hA : ∀ t ∈ Ico a b, ∀ x : H, ⟪x, A t x⟫_ℝ ≤ 0) :
    ∀ t ∈ Icc a b, ‖u t‖ ≤ ‖u a‖ + ∫ s in a..t, ‖f s‖ := by
  let B : ℝ → ℝ := fun t => ‖u a‖ + ∫ s in a..t, ‖f s‖
  have hB (t : ℝ) : HasDerivAt B ‖f t‖ t :=
    (intervalIntegral.integral_hasDerivAt_right (hf.norm.intervalIntegrable a t)
      (hf.norm.stronglyMeasurableAtFilter _ _) hf.norm.continuousAt).const_add ‖u a‖
  apply image_le_of_liminf_slope_right_le_deriv_boundary
    (continuous_norm.comp_continuousOn hu) (by simp [B])
    (fun t _ => (hB t).continuousAt.continuousWithinAt)
    (fun t _ => (hB t).hasDerivWithinAt)
  intro t ht r hr
  by_cases hz : u t = 0
  · have hd : HasDerivWithinAt u (f t) (Ici t) t := by
      simpa [hz] using hode t ht
    exact hd.liminf_right_slope_norm_le hr
  · have hn : 0 < ‖u t‖ := norm_pos_iff.mpr hz
    have hi : ⟪u t, A t (u t) + f t⟫_ℝ ≤ ‖u t‖ * ‖f t‖ := by
      rw [inner_add_right]
      exact (add_le_add (hA t ht (u t)) (real_inner_le_norm (u t) (f t))).trans_eq
        (zero_add _)
    have hdiv : ⟪u t, A t (u t) + f t⟫_ℝ / ‖u t‖ ≤ ‖f t‖ := by
      apply (div_le_iff₀ hn).2
      simpa only [mul_comm] using hi
    exact (norm_derivative (hode t ht) hz).liminf_right_slope_le
      (lt_of_le_of_lt hdiv hr)

private theorem weighted_norm_bound
    {a b : ℝ} {u f : ℝ → H} (A : ℝ → H →L[ℝ] H)
    (growth W : ℝ → ℝ) (hWpos : ∀ t, 0 < W t)
    (hW : ∀ t, HasDerivAt W (growth t * W t) t)
    (hu : ContinuousOn u (Icc a b)) (hf : Continuous f)
    (hode : ∀ t ∈ Ico a b,
      HasDerivWithinAt u (A t (u t) + f t) (Ici t) t)
    (hA : ∀ t ∈ Ico a b, ∀ x : H,
      ⟪x, A t x⟫_ℝ ≤ growth t * ‖x‖ ^ 2) :
    ∀ t ∈ Icc a b,
      ‖u t‖ / W t ≤ ‖u a‖ / W a + ∫ s in a..t, ‖f s‖ / W s := by
  have hInv (t : ℝ) : HasDerivAt (fun s => (W s)⁻¹)
      (-growth t * (W t)⁻¹) t := by
    convert! (hW t).inv (ne_of_gt (hWpos t)) using 1
    field_simp [ne_of_gt (hWpos t)]
  have hcInv : Continuous (fun t => (W t)⁻¹) :=
    continuous_iff_continuousAt.mpr fun t => (hInv t).continuousAt
  let v : ℝ → H := fun t => (W t)⁻¹ • u t
  let F : ℝ → H := fun t => (W t)⁻¹ • f t
  let B : ℝ → H →L[ℝ] H := fun t => A t - growth t • ContinuousLinearMap.id ℝ H
  have hv : ContinuousOn v (Icc a b) := hcInv.continuousOn.smul hu
  have hF : Continuous F := hcInv.smul hf
  have hvode (t : ℝ) (ht : t ∈ Ico a b) :
      HasDerivWithinAt v (B t (v t) + F t) (Ici t) t := by
    convert! (hInv t).hasDerivWithinAt.smul (hode t ht) using 1
    dsimp [v, F, B]
    simp only [sub_apply, smul_apply, ContinuousLinearMap.id_apply, map_smul, smul_add]
    module
  have hB (t : ℝ) (ht : t ∈ Ico a b) (x : H) : ⟪x, B t x⟫_ℝ ≤ 0 := by
    dsimp [B]
    simp only [sub_apply, smul_apply, ContinuousLinearMap.id_apply,
      inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
    linarith [hA t ht x]
  have hn (t : ℝ) (x : H) : ‖(W t)⁻¹ • x‖ = ‖x‖ / W t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hWpos t)),
      div_eq_mul_inv, mul_comm]
  have h := dissipative_norm_bound B hv hF hvode hB
  dsimp [v, F] at h
  simpa only [hn] using h

/-- The exact finite-time attraction tube. The rate is strictly dissipative,
and the nonzero initial error and forcing amplitude are both retained. -/
theorem norm_le_exponential_tube
    {T γ ρ : ℝ} {u f : ℝ → H} (A : ℝ → H →L[ℝ] H)
    (hγ : 0 < γ) (hu : ContinuousOn u (Icc 0 T)) (hf : Continuous f)
    (hode : ∀ t ∈ Ico 0 T,
      HasDerivWithinAt u (A t (u t) + f t) (Ici t) t)
    (hA : ∀ t ∈ Ico 0 T, ∀ x : H, ⟪x, A t x⟫_ℝ ≤ -γ * ‖x‖ ^ 2)
    (hforce : ∀ t ∈ Icc 0 T, ‖f t‖ ≤ ρ) :
    ∀ t ∈ Icc 0 T,
      ‖u t‖ ≤ Real.exp (-γ * t) * ‖u 0‖ + (ρ / γ) * (1 - Real.exp (-γ * t)) := by
  have hW (t : ℝ) : HasDerivAt (fun s : ℝ => Real.exp (-γ * s))
      (-γ * Real.exp (-γ * t)) t := by
    convert ((hasDerivAt_id t).const_mul (-γ)).exp using 1 <;> simp <;> ring
  have hbase := weighted_norm_bound A (fun _ => -γ) (fun s => Real.exp (-γ * s))
    (fun s => Real.exp_pos _) hW hu hf hode hA
  intro t ht
  have hc : Continuous (fun s : ℝ => ρ * Real.exp (γ * s)) := by fun_prop
  have hprim (s : ℝ) : HasDerivAt (fun x : ℝ => (ρ / γ) * Real.exp (γ * x))
      (ρ * Real.exp (γ * s)) s := by
    convert (((hasDerivAt_id s).const_mul γ).exp).const_mul (ρ / γ) using 1 <;>
      field_simp [ne_of_gt hγ] <;> ring
  have hint : (∫ s in 0..t, ρ * Real.exp (γ * s)) =
      (ρ / γ) * (Real.exp (γ * t) - 1) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hprim s) (hc.intervalIntegrable 0 t)
    simpa only [mul_zero, Real.exp_zero, mul_one, mul_sub] using h
  have hcont : Continuous (fun s => ‖f s‖ / Real.exp (-γ * s)) :=
    hf.norm.div (by fun_prop) (fun s => (Real.exp_pos _).ne')
  have hle : (∫ s in 0..t, ‖f s‖ / Real.exp (-γ * s)) ≤
      (ρ / γ) * (Real.exp (γ * t) - 1) := by
    rw [← hint]
    apply intervalIntegral.integral_mono_on ht.1
      (hcont.intervalIntegrable 0 t) (hc.intervalIntegrable 0 t)
    intro s hs
    have hb := hforce s ⟨hs.1, hs.2.trans ht.2⟩
    have he : -γ * s = -(γ * s) := by ring
    rw [he, Real.exp_neg, div_eq_mul_inv, inv_inv]
    exact mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
  have hw : ‖u t‖ / Real.exp (-γ * t) ≤
      ‖u 0‖ + (ρ / γ) * (Real.exp (γ * t) - 1) := by
    have h := hbase t ht
    simp only [mul_zero, Real.exp_zero, div_one] at h
    exact h.trans (add_le_add_left hle _)
  have hexp : Real.exp (γ * t) * Real.exp (-γ * t) = 1 := by
    rw [← Real.exp_add]
    have hzero : γ * t + -γ * t = 0 := by ring
    rw [hzero, Real.exp_zero]
  calc
    ‖u t‖ ≤ (‖u 0‖ + (ρ / γ) * (Real.exp (γ * t) - 1)) * Real.exp (-γ * t) :=
      (div_le_iff₀ (Real.exp_pos _)).mp hw
    _ = Real.exp (-γ * t) * ‖u 0‖ +
        (ρ / γ) * (Real.exp (γ * t) * Real.exp (-γ * t) - Real.exp (-γ * t)) := by ring
    _ = _ := by rw [hexp]

/-- Zero forcing gives contraction to the actual zero equilibrium, not merely
non-increase of a non-coercive observation. Existence of the input solution
is not asserted by this estimate. -/
theorem unforced_norm_contraction
    {T γ : ℝ} {u : ℝ → H} (A : ℝ → H →L[ℝ] H)
    (hγ : 0 < γ) (hu : ContinuousOn u (Icc 0 T))
    (hode : ∀ t ∈ Ico 0 T, HasDerivWithinAt u (A t (u t)) (Ici t) t)
    (hA : ∀ t ∈ Ico 0 T, ∀ x : H, ⟪x, A t x⟫_ℝ ≤ -γ * ‖x‖ ^ 2) :
    ∀ t ∈ Icc 0 T, ‖u t‖ ≤ Real.exp (-γ * t) * ‖u 0‖ := by
  have h := norm_le_exponential_tube (u := u) (f := fun _ => (0 : H)) (ρ := 0)
    A hγ hu continuous_const (by simpa using hode) hA (by simp)
  simpa using h

#print axioms norm_le_exponential_tube
#print axioms unforced_norm_contraction

end Hilbert

/-- A scalar stationary state plus an arbitrary bounded forcing defect. This
is obtained by applying the OpenAI Hilbert estimate to the actual error a-c. -/
theorem scalar_equilibrium_tube {T γ ρ c : ℝ} {a r : ℝ → ℝ}
    (hγ : 0 < γ) (ha : ContinuousOn a (Icc 0 T)) (hr : Continuous r)
    (hode : ∀ t ∈ Ico 0 T,
      HasDerivWithinAt a (-γ * (a t - c) + r t) (Ici t) t)
    (hforce : ∀ t ∈ Icc 0 T, |r t| ≤ ρ) :
    ∀ t ∈ Icc 0 T,
      |a t - c| ≤ Real.exp (-γ * t) * |a 0 - c| +
        (ρ / γ) * (1 - Real.exp (-γ * t)) := by
  let A : ℝ → ℝ →L[ℝ] ℝ := fun _ => (-γ) • ContinuousLinearMap.id ℝ ℝ
  have hd (t : ℝ) (ht : t ∈ Ico 0 T) :
      HasDerivWithinAt (fun s => a s - c) (A t (a t - c) + r t) (Ici t) t := by
    simpa [A, smul_eq_mul] using (hode t ht).sub_const c
  have hA (t : ℝ) (_ht : t ∈ Ico 0 T) (x : ℝ) :
      ⟪x, A t x⟫_ℝ ≤ -γ * ‖x‖ ^ 2 := by
    change ⟪x, (-γ) • x⟫_ℝ ≤ -γ * ‖x‖ ^ 2
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
  simpa only [Real.norm_eq_abs] using norm_le_exponential_tube
    A hγ (ha.sub continuousOn_const) hr hd hA (by simpa only [Real.norm_eq_abs] using hforce)

#print axioms scalar_equilibrium_tube

end D5.S3.FluidDynamics.Stability.OpenAIViscousAttraction
