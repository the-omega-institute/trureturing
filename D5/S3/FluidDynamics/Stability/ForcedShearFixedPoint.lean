/- GID: D5/S3/FluidDynamics/Stability/ForcedShearFixedPoint
   generality: G
   mirror-B: D5/B/S3/FluidDynamics/Stability/ForcedShearFixedPoint
   mirror-E: none(waiver:actual-shear-forcing-and-uniform-space-bound)
   anchors: []
   utility: none
   digest: Independently proved dissipative comparison certifies attraction to actual stationary forced shears. -/

import D5.S3.FluidDynamics.Stability.DissipativeAttraction
import D5.S3.FluidDynamics.Fourier.ToralIsogenyShearNS

/-!
An actual consumer of the mathlib-only dissipative energy estimate on the
previously defined 2*pi-periodic Euclidean shear family. Forcing has the
same divergence-free spatial profile and may have a continuous amplitude
error r(t). The stationary forcing is gamma*c*profile and the actual target
field c*profile solves that equation. Perturbations remain in this family.

Every equation uses the predecessor's ordinary derivatives and nsResidual.
The final field error bound is uniform in space and both components. No
L2 normalization, general existence or transverse PDE stability is inferred.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace D5.S3.FluidDynamics.Stability.ForcedShearFixedPoint

open D5.S3.FluidDynamics.Stability.DissipativeAttraction
open D5.S3.FluidDynamics.Fourier.ToralIsogenyShearNS
open private wave amplitude wave_dx wave_dy wave_dxx wave_dxy wave_dyy
  from D5.S3.FluidDynamics.Fourier.ToralIsogenyShearNS

/-- The exact spatial profile already present in the original shear solution. -/
def profile (k : ℕ) (x y : ℝ) (i : Fin 2) : ℝ := shear k 0 0 0 x y i

/-- An arbitrary time amplitude multiplying that actual profile. -/
def field (k : ℕ) (a : ℝ → ℝ) : PlanarField := fun t x y i => a t * profile k x y i

/-- Euclidean viscous decay rate, with spatial period fixed at 2*pi. -/
def rate (k : ℕ) (nu : ℝ) : ℝ := 4 * nu * ((k : ℝ) ^ 2 + 1)

private theorem profile_formula (k : ℕ) (x y : ℝ) (i : Fin 2) :
    profile k x y i = amplitude k i * Real.cos (-2 * (k : ℝ) * x + 2 * y) := by
  simp [profile, shear, wave]

private theorem field_as_wave (k : ℕ) (a : ℝ → ℝ) (t x y : ℝ) (i : Fin 2) :
    field k a t x y i =
      wave (a t * amplitude k i) (-2 * (k : ℝ)) 2 0 0 0 x y := by
  simp [field, profile_formula, wave, mul_assoc]

private theorem dx_formula (k : ℕ) (a : ℝ → ℝ) (t x y : ℝ) (i : Fin 2) :
    dx (field k a) t x y i =
      2 * (k : ℝ) * a t * amplitude k i * Real.sin (-2 * (k : ℝ) * x + 2 * y) := by
  unfold dx
  simp_rw [field_as_wave]
  rw [wave_dx]
  simp <;> ring

private theorem dy_formula (k : ℕ) (a : ℝ → ℝ) (t x y : ℝ) (i : Fin 2) :
    dy (field k a) t x y i =
      -2 * a t * amplitude k i * Real.sin (-2 * (k : ℝ) * x + 2 * y) := by
  unfold dy
  simp_rw [field_as_wave]
  rw [wave_dy]
  simp <;> ring

private theorem dxx_formula (k : ℕ) (a : ℝ → ℝ) (t x y : ℝ) (i : Fin 2) :
    dxx (field k a) t x y i = -4 * (k : ℝ) ^ 2 * field k a t x y i := by
  unfold dxx dx
  simp_rw [field_as_wave]
  rw [wave_dxx]
  ring

private theorem dyy_formula (k : ℕ) (a : ℝ → ℝ) (t x y : ℝ) (i : Fin 2) :
    dyy (field k a) t x y i = -4 * field k a t x y i := by
  unfold dyy dy
  simp_rw [field_as_wave]
  rw [wave_dyy]
  ring

private theorem time_formula (k : ℕ) (a : ℝ → ℝ) (t da x y : ℝ) (i : Fin 2)
    (ha : HasDerivAt a da t) :
    dt (field k a) t x y i = da * profile k x y i :=
  (ha.mul_const (profile k x y i)).deriv

/-- The exact PDE residual for an arbitrary differentiable amplitude. -/
theorem field_equation (k : ℕ) (nu : ℝ) (a : ℝ → ℝ) (t da x y : ℝ)
    (i : Fin 2) (ha : HasDerivAt a da t) :
    divergence (field k a) t x y = 0 ∧
    nsResidual nu 1 0 1 (field k a) t x y i =
      (da + rate k nu * a t) * profile k x y i := by
  constructor
  · rw [divergence, dx_formula, dy_formula]
    norm_num [amplitude] <;> ring
  · rw [nsResidual, time_formula k a t da x y i ha,
      dx_formula, dy_formula, dxx_formula, dyy_formula]
    simp only [zero_mul, mul_zero, add_zero, one_mul]
    simp only [field, profile_formula]
    norm_num [amplitude, rate] <;> ring

/-- With forcing gamma*c*profile, the literal field c*profile is stationary. -/
theorem stationary_forced_solution (k : ℕ) (nu c t x y : ℝ) (i : Fin 2) :
    divergence (field k (fun _ => c)) t x y = 0 ∧
    nsResidual nu 1 0 1 (field k (fun _ => c)) t x y i =
      rate k nu * c * profile k x y i := by
  simpa using field_equation k nu (fun _ => c) t 0 x y i (hasDerivAt_const t c)

/-- Fixed evaluation recovers the amplitude from the actual velocity field. -/
theorem amplitude_readout (k : ℕ) (a : ℝ → ℝ) (t : ℝ) :
    field k a t 0 0 0 = a t := by
  simp [field, profile_formula, amplitude]

private theorem profile_bound (k : ℕ) (x y : ℝ) (i : Fin 2) :
    |profile k x y i| ≤ 1 + (k : ℝ) := by
  rw [profile_formula, abs_mul]
  have hcos := Real.abs_cos_le_one (-2 * (k : ℝ) * x + 2 * y)
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  fin_cases i
  · simp only [amplitude, if_pos rfl, abs_one, one_mul]
    linarith
  · have h01 : (1 : Fin 2) ≠ 0 := by decide
    simp only [amplitude, if_neg h01, abs_of_nonneg hk]
    have h := mul_le_mul_of_nonneg_left hcos hk
    nlinarith

/-- The same actual PDE and spatial tube, now using the independent proof. -/
theorem forced_shear_attraction {T nu c ρ : ℝ} (k : ℕ) {a r : ℝ → ℝ}
    (hnu : 0 < nu) (ha : ContinuousOn a (Icc 0 T)) (hr : Continuous r)
    (hode : ∀ t ∈ Icc 0 T,
      HasDerivAt a (-rate k nu * (a t - c) + r t) t)
    (hforce : ∀ t ∈ Icc 0 T, |r t| ≤ ρ) :
    ∀ t ∈ Icc 0 T, ∀ x y : ℝ, ∀ i : Fin 2,
      (divergence (field k a) t x y = 0 ∧
        nsResidual nu 1 0 1 (field k a) t x y i =
          (rate k nu * c + r t) * profile k x y i) ∧
      |field k a t x y i - field k (fun _ => c) t x y i| ≤
        (1 + (k : ℝ)) *
          (Real.exp (-rate k nu * t) * |a 0 - c| +
            (ρ / rate k nu) * (1 - Real.exp (-rate k nu * t))) := by
  have hγ : 0 < rate k nu := by unfold rate; positivity
  have hb := scalar_equilibrium_tube hγ ha hr
    (fun t ht => (hode t (Ico_subset_Icc_self ht)).hasDerivWithinAt) hforce
  intro t ht x y i
  have hres := field_equation k nu a t (-rate k nu * (a t - c) + r t) x y i (hode t ht)
  refine ⟨⟨hres.1, ?_⟩, ?_⟩
  · rw [hres.2]
    ring
  · let E := Real.exp (-rate k nu * t) * |a 0 - c| +
      (ρ / rate k nu) * (1 - Real.exp (-rate k nu * t))
    have hE : |a t - c| ≤ E := hb t ht
    have hE0 : 0 ≤ E := (abs_nonneg _).trans hE
    calc
      |field k a t x y i - field k (fun _ => c) t x y i| =
          |a t - c| * |profile k x y i| := by
        rw [field, field, ← sub_mul, abs_mul]
      _ ≤ E * |profile k x y i| := mul_le_mul_of_nonneg_right hE (abs_nonneg _)
      _ ≤ E * (1 + (k : ℝ)) := mul_le_mul_of_nonneg_left (profile_bound k x y i) hE0
      _ = _ := by dsimp [E]; ring

#print axioms field_equation
#print axioms stationary_forced_solution
#print axioms amplitude_readout
#print axioms forced_shear_attraction

end D5.S3.FluidDynamics.Stability.ForcedShearFixedPoint
