/- GID: D5/S3/ObserverMemory/Dynamics/DampedExchangeMemory
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Dynamics/DampedExchangeMemory
   mirror-E: none(waiver:exact-ODE-elimination-and-readout)
   anchors: []
   utility: none
   digest: A damped resolved-hidden exchange has an exact signed memory kernel, state-energy decay and quantitatively conditioned jet recovery. -/

import D5.S3.FluidDynamics.Stability.DissipativeAttraction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
The literal two-state ODE is x'=-a*x+b*y, y'=-b*x-d*y.
Its skew exchange cancels in x^2+y^2, while eliminating y produces a signed
Volterra kernel -b^2*exp(-d*t) and the initial hidden-state term. All three
objects are derived from the same equations; no memory equation is assumed.

This exact finite-dimensional model is not identified with an arbitrary NS
Galerkin truncation or nonlinear Mori-Zwanzig orthogonal dynamics. It tests
what stability, state reconstruction and finite memory forgetfulness each
require. The only external formal dependency is mathlib. Classical linear
elimination and observability are not claimed as new open-problem solutions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory

namespace D5.S3.ObserverMemory.Dynamics.DampedExchangeMemory

open D5.S3.FluidDynamics.Stability.DissipativeAttraction

def resolvedRhs (a b x y : ℝ) : ℝ := -a * x + b * y
def hiddenRhs (b d x y : ℝ) : ℝ := -b * x - d * y

/-- The actual squared Euclidean state energy, not a readout-based score. -/
def energy (x y : ℝ) : ℝ := x ^ 2 + y ^ 2

/-- Exchange is energy-neutral for every coupling strength. -/
theorem exchange_energy_identity (a b d x y : ℝ) :
    2 * x * resolvedRhs a b x y + 2 * y * hiddenRhs b d x y =
      -2 * a * x ^ 2 - 2 * d * y ^ 2 := by
  dsimp [resolvedRhs, hiddenRhs]
  ring

/-- Both actual coordinates decay in squared energy. The rate is independent
of the exchange strength b; no eigenvalue estimate or closedness is assumed. -/
theorem state_energy_decay {a b d γ T : ℝ} {x y : ℝ → ℝ}
    (_hγ : 0 < γ) (ha : γ ≤ a) (hd : γ ≤ d)
    (hx : ContinuousOn x (Icc 0 T)) (hy : ContinuousOn y (Icc 0 T))
    (hxd : ∀ s ∈ Ico 0 T, HasDerivAt x (resolvedRhs a b (x s) (y s)) s)
    (hyd : ∀ s ∈ Ico 0 T, HasDerivAt y (hiddenRhs b d (x s) (y s)) s) :
    ∀ t ∈ Icc 0 T,
      energy (x t) (y t) ≤ energy (x 0) (y 0) * Real.exp ((-2 * γ) * t) := by
  let E : ℝ → ℝ := fun s => energy (x s) (y s)
  let D : ℝ → ℝ := fun s =>
    2 * x s * resolvedRhs a b (x s) (y s) + 2 * y s * hiddenRhs b d (x s) (y s)
  have hEc : ContinuousOn E (Icc 0 T) := (hx.pow 2).add (hy.pow 2)
  have hEd (s : ℝ) (hs : s ∈ Ico 0 T) : HasDerivAt E (D s) s := by
    convert ((hxd s hs).pow 2).add ((hyd s hs).pow 2) using 1 <;>
      dsimp [E, D, energy] <;> norm_num <;> ring
  have hbound (s : ℝ) (_hs : s ∈ Ico 0 T) : D s ≤ (-2 * γ) * E s + 0 := by
    dsimp [D, E]
    rw [exchange_energy_identity]
    dsimp [energy]
    have h1 := mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg (x s))
    have h2 := mul_nonneg (sub_nonneg.mpr hd) (sq_nonneg (y s))
    nlinarith
  have h := le_gronwallBound_of_liminf_deriv_right_le
    (f := E) (f' := D) (δ := E 0) (K := -2 * γ) (ε := 0)
    hEc (fun s hs r hr => (hEd s hs).hasDerivWithinAt.liminf_right_slope_le hr)
    (le_refl _) hbound
  simpa only [gronwallBound_ε0, sub_zero] using h

/-- The actual initial-hidden-state elimination uses this weighted integral. -/
def weightedPast (d : ℝ) (x : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in 0..t, Real.exp (d * s) * x s

def memoryKernel (b d τ : ℝ) : ℝ := -(b ^ 2) * Real.exp (-d * τ)

def memoryTerm (b d : ℝ) (x : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in 0..t, memoryKernel b d (t - s) * x s

/-- The signed convolution equals the integral appearing in actual elimination. -/
theorem memoryTerm_factored (b d : ℝ) (x : ℝ → ℝ) (t : ℝ) :
    memoryTerm b d x t = -(b ^ 2) * Real.exp (-d * t) * weightedPast d x t := by
  unfold memoryTerm
  calc
    (∫ s in 0..t, memoryKernel b d (t - s) * x s) =
        ∫ s in 0..t, (-(b ^ 2) * Real.exp (-d * t)) * (Real.exp (d * s) * x s) := by
      apply intervalIntegral.integral_congr
      intro s _hs
      dsimp [memoryKernel]
      have he : -d * (t - s) = -d * t + d * s := by ring
      rw [he, Real.exp_add]
      ring
    _ = _ := by rw [intervalIntegral.integral_const_mul]; rfl

/-- Fundamental-theorem-of-calculus derivation from the actual hidden ODE.
It does not assume a Volterra equation or identify a chosen kernel by name. -/
theorem hidden_history_formula {b d t : ℝ} {x y : ℝ → ℝ}
    (ht : 0 ≤ t) (hx : Continuous x)
    (hyd : ∀ s ∈ Icc 0 t, HasDerivAt y (hiddenRhs b d (x s) (y s)) s) :
    y t = Real.exp (-d * t) * (y 0 - b * weightedPast d x t) := by
  have hF (s : ℝ) (hs : s ∈ Icc 0 t) :
      HasDerivAt (fun q => Real.exp (d * q) * y q)
        (-b * (Real.exp (d * s) * x s)) s := by
    convert (((hasDerivAt_id s).const_mul d).exp).mul (hyd s hs) using 1 <;>
      dsimp [hiddenRhs, id] <;> ring
  have hc : Continuous (fun s => -b * (Real.exp (d * s) * x s)) := by fun_prop
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hF s (by simpa only [uIcc_of_le ht] using hs))
    (hc.intervalIntegrable 0 t)
  rw [intervalIntegral.integral_const_mul] at hI
  simp only [mul_zero, Real.exp_zero, one_mul] at hI
  change -b * weightedPast d x t = Real.exp (d * t) * y t - y 0 at hI
  have hE : Real.exp (-d * t) * Real.exp (d * t) = 1 := by
    rw [← Real.exp_add]
    have he : -d * t + d * t = 0 := by ring
    rw [he, Real.exp_zero]
  have hv : Real.exp (d * t) * y t = y 0 - b * weightedPast d x t := by linarith
  calc
    y t = (Real.exp (-d * t) * Real.exp (d * t)) * y t := by rw [hE, one_mul]
    _ = Real.exp (-d * t) * (Real.exp (d * t) * y t) := by ring
    _ = _ := by rw [hv]

/-- The actual resolved derivative contains both memory and the hidden initial
condition. Omitting the latter is an additional approximation. -/
theorem resolved_memory_equation {a b d t : ℝ} {x y : ℝ → ℝ}
    (ht : 0 ≤ t) (hx : Continuous x)
    (hyd : ∀ s ∈ Icc 0 t, HasDerivAt y (hiddenRhs b d (x s) (y s)) s)
    (hxd : HasDerivAt x (resolvedRhs a b (x t) (y t)) t) :
    HasDerivAt x (-a * x t + b * Real.exp (-d * t) * y 0 + memoryTerm b d x t) t := by
  have hy := hidden_history_formula ht hx hyd
  rw [memoryTerm_factored]
  dsimp [resolvedRhs] at hxd
  rw [hy] at hxd
  convert hxd using 1 <;> ring

/-- With the same resolved input, hidden initialization error decays exactly
at the hidden dissipation rate. This is a finite-memory restart certificate. -/
theorem hidden_restart_error {b d T : ℝ} {x y z : ℝ → ℝ}
    (hd : 0 < d) (hy : ContinuousOn y (Icc 0 T)) (hz : ContinuousOn z (Icc 0 T))
    (hyd : ∀ s ∈ Ico 0 T, HasDerivAt y (hiddenRhs b d (x s) (y s)) s)
    (hzd : ∀ s ∈ Ico 0 T, HasDerivAt z (hiddenRhs b d (x s) (z s)) s) :
    ∀ t ∈ Icc 0 T,
      |b * (y t - z t)| ≤ |b| * Real.exp (-d * t) * |y 0 - z 0| := by
  have hode (s : ℝ) (hs : s ∈ Ico 0 T) :
      HasDerivWithinAt (fun q => y q - z q) (-d * ((y s - z s) - 0) + 0) (Ici s) s := by
    convert ((hyd s hs).sub (hzd s hs)).hasDerivWithinAt using 1 <;>
      dsimp [hiddenRhs] <;> ring
  have hb := scalar_equilibrium_tube (c := 0) (ρ := 0) (r := fun _ => 0)
    hd (hy.sub hz) continuous_const hode (by simp)
  intro t ht
  have h : |y t - z t| ≤ Real.exp (-d * t) * |y 0 - z 0| := by simpa using hb t ht
  rw [abs_mul]
  calc
    |b| * |y t - z t| ≤ |b| * (Real.exp (-d * t) * |y 0 - z 0|) :=
      mul_le_mul_of_nonneg_left h (abs_nonneg b)
    _ = _ := by ring

/-- A visible state and its actual derivative reconstruct the hidden state
when the coupling is nonzero. -/
def recoverHidden (a b observedState observedRate : ℝ) : ℝ :=
  (observedRate + a * observedState) / b

theorem exact_jet_recovery (a b x y : ℝ) (hb : b ≠ 0) :
    recoverHidden a b x (resolvedRhs a b x y) = y := by
  dsimp [recoverHidden, resolvedRhs]
  field_simp
  ring

/-- Quantitative conditioning of the same reconstruction. Stability of the
full system alone gives no uniform control as coupling b tends to zero. -/
theorem noisy_jet_recovery (a b x y xobs vobs εx εv : ℝ) (hb : b ≠ 0)
    (hx : |xobs - x| ≤ εx) (hv : |vobs - resolvedRhs a b x y| ≤ εv) :
    |recoverHidden a b xobs vobs - y| ≤ (εv + |a| * εx) / |b| := by
  have he : recoverHidden a b xobs vobs - y =
      ((vobs - resolvedRhs a b x y) + a * (xobs - x)) / b := by
    dsimp [recoverHidden, resolvedRhs]
    field_simp
    ring
  rw [he, abs_div]
  apply div_le_div_of_nonneg_right _ (abs_nonneg b)
  have hsum := abs_add_le (vobs - resolvedRhs a b x y) (a * (xobs - x))
  rw [abs_mul] at hsum
  have hmul := mul_le_mul_of_nonneg_left hx (abs_nonneg a)
  linarith

/-- The same eliminated dynamics gives the steady-state Schur correction.
Transient stability, memory elimination and this static identity use one system. -/
theorem stationary_hidden_elimination (a b d x y : ℝ) (hd : d ≠ 0)
    (hy : hiddenRhs b d x y = 0) :
    y = -b * x / d ∧ resolvedRhs a b x y = -(a + b ^ 2 / d) * x := by
  have hxy : d * y = -b * x := by dsimp [hiddenRhs] at hy; linarith
  have hyeq : y = -b * x / d := (eq_div_iff hd).mpr (by simpa [mul_comm] using hxy)
  refine ⟨hyeq, ?_⟩
  rw [hyeq]
  dsimp [resolvedRhs]
  field_simp
  ring

#print axioms exchange_energy_identity
#print axioms state_energy_decay
#print axioms memoryTerm_factored
#print axioms hidden_history_formula
#print axioms resolved_memory_equation
#print axioms hidden_restart_error
#print axioms exact_jet_recovery
#print axioms noisy_jet_recovery
#print axioms stationary_hidden_elimination

end D5.S3.ObserverMemory.Dynamics.DampedExchangeMemory
