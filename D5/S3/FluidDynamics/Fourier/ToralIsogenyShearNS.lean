/- GID: D5/S3/FluidDynamics/Fourier/ToralIsogenyShearNS
   generality: G
   mirror-B: D5/B/S3/FluidDynamics/Fourier/ToralIsogenyShearNS
   mirror-E: none(waiver:actual-smooth-periodic-shear-and-coordinate-derivatives)
   anchors: []
   utility: none
   digest: The original toral isogeny transports an exact shear solution with the pulled metric; the unchanged Euclidean NS equation has an explicit nonzero defect. -/

import D5.S3.Observer.Dynamics.ToralReturnModuleSpectrum
import D5.S3.FluidDynamics.Fourier.ReversalWaveSynthesis
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
This source uses ordinary derivatives of actual smooth functions, not a table
of Fourier multipliers postulated to solve an equation. The planar velocity
is periodic in both spatial variables; pressure and external force are zero.
A constant symmetric contravariant metric is written through its three
coefficients. Euclidean NS is the specialization (1,0,1). The real inverse
acts on tangent vectors; it is not a global inverse of the degree-two torus
cover, and no bijection of arbitrary velocity-field spaces is claimed.

The integer bridge is the original P_k=[[1,0],[-2k,2]]. Its actual real inverse
pulls back the base velocity. The pulled inverse metric is P_k^{-1}P_k^{-T}.
The theorem computes the full convection-diffusion residual of the shear.
It proves failure at the unchanged metric and exact repair after transporting
the metric, as well as a different exact Euclidean solution at its own rate.
This is not uniqueness of a metric compatible with one Fourier mode.

This is an exact planar invariant family. It gives no general 3D regularity,
blowup, nonlinear perturbation stability or physical realization of a cat map
as a particle time-one map. The period convention is 2*pi, whereas the
arithmetic torus module uses period one; scalar rescaling is not used to
transfer an untracked viscosity constant.

Source search reused actual ReversalWaveSynthesis and AugmentedReadoutRecovery;
the latter already solves the instantaneous two-amplitude inverse problem and
is not duplicated. Classical context: Fannjiang--Wolowski math/0209231 and
Arnaudon--Cruzeiro--Fang 1509.03491. The present flat constant-metric example
avoids ambiguity among different viscous operators on curved manifolds.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix
open scoped Matrix ContDiff

namespace D5.S3.FluidDynamics.Fourier.ToralIsogenyShearNS

open D5.S3.Observer.Dynamics.ToralReturnModuleSpectrum

abbrev PlanarField := ℝ → ℝ → ℝ → Fin 2 → ℝ

/-- Actual time and coordinate derivatives, with no symbolic differentiator. -/
def dt (v : PlanarField) (t x y : ℝ) (i : Fin 2) := deriv (fun s => v s x y i) t
def dx (v : PlanarField) (t x y : ℝ) (i : Fin 2) := deriv (fun s => v t s y i) x
def dy (v : PlanarField) (t x y : ℝ) (i : Fin 2) := deriv (fun s => v t x s i) y
def dxx (v : PlanarField) (t x y : ℝ) (i : Fin 2) := deriv (fun s => dx v t s y i) x
def dxy (v : PlanarField) (t x y : ℝ) (i : Fin 2) := deriv (fun s => dx v t x s i) y
def dyy (v : PlanarField) (t x y : ℝ) (i : Fin 2) := deriv (fun s => dy v t x s i) y

def divergence (v : PlanarField) (t x y : ℝ) : ℝ := dx v t x y 0 + dy v t x y 1

/-- Zero-pressure, zero-force NS residual for a constant symmetric inverse
metric [[h00,h01],[h01,h11]]. Euclidean residual is (h00,h01,h11)=(1,0,1). -/
def nsResidual (nu h00 h01 h11 : ℝ) (v : PlanarField) (t x y : ℝ) (i : Fin 2) : ℝ :=
  dt v t x y i + v t x y 0 * dx v t x y i + v t x y 1 * dy v t x y i -
    nu * (h00 * dxx v t x y i + 2 * h01 * dxy v t x y i + h11 * dyy v t x y i)

private def wave (c a b nu rate t x y : ℝ) : ℝ :=
  (c * Real.exp ((-nu * rate) * t)) * Real.cos (a * x + b * y)

private theorem wave_dt (c a b nu rate t x y : ℝ) :
    deriv (fun s => wave c a b nu rate s x y) t =
      (-nu * rate) * wave c a b nu rate t x y := by
  have h := ((((hasDerivAt_id t).const_mul (-nu * rate)).exp).const_mul c).mul_const
    (Real.cos (a * x + b * y))
  convert h.deriv using 1 <;> dsimp [wave] <;> ring

private theorem wave_dx (c a b nu rate t x y : ℝ) :
    deriv (fun s => wave c a b nu rate t s y) x =
      (-a * c * Real.exp ((-nu * rate) * t)) * Real.sin (a * x + b * y) := by
  have h := ((((hasDerivAt_id x).const_mul a).add
    (hasDerivAt_const x (b * y))).cos).const_mul (c * Real.exp ((-nu * rate) * t))
  convert h.deriv using 1 <;> dsimp [wave] <;> ring

private theorem wave_dy (c a b nu rate t x y : ℝ) :
    deriv (fun s => wave c a b nu rate t x s) y =
      (-b * c * Real.exp ((-nu * rate) * t)) * Real.sin (a * x + b * y) := by
  have h := (((hasDerivAt_const y (a * x)).add
    ((hasDerivAt_id y).const_mul b)).cos).const_mul (c * Real.exp ((-nu * rate) * t))
  convert h.deriv using 1 <;> dsimp [wave] <;> ring

private theorem wave_dxx (c a b nu rate t x y : ℝ) :
    deriv (fun s => deriv (fun r => wave c a b nu rate t r y) s) x =
      -(a ^ 2) * wave c a b nu rate t x y := by
  simp_rw [wave_dx]
  have h := ((((hasDerivAt_id x).const_mul a).add
    (hasDerivAt_const x (b * y))).sin).const_mul (-a * c * Real.exp ((-nu * rate) * t))
  convert h.deriv using 1 <;> dsimp [wave] <;> ring

private theorem wave_dxy (c a b nu rate t x y : ℝ) :
    deriv (fun s => deriv (fun r => wave c a b nu rate t r s) x) y =
      -(a * b) * wave c a b nu rate t x y := by
  simp_rw [wave_dx]
  have h := (((hasDerivAt_const y (a * x)).add
    ((hasDerivAt_id y).const_mul b)).sin).const_mul (-a * c * Real.exp ((-nu * rate) * t))
  convert h.deriv using 1 <;> dsimp [wave] <;> ring

private theorem wave_dyy (c a b nu rate t x y : ℝ) :
    deriv (fun s => deriv (fun r => wave c a b nu rate t x r) s) y =
      -(b ^ 2) * wave c a b nu rate t x y := by
  simp_rw [wave_dy]
  have h := (((hasDerivAt_const y (a * x)).add
    ((hasDerivAt_id y).const_mul b)).sin).const_mul (-b * c * Real.exp ((-nu * rate) * t))
  convert h.deriv using 1 <;> dsimp [wave] <;> ring

/-- The smooth, unforced horizontal shear before the lattice-cover pullback. -/
def baseVelocity (nu : ℝ) : PlanarField := fun t x y i =>
  wave (if i = 0 then 1 else 0) 0 1 nu 1 t x y

/-- Ordinary derivatives verify the base Euclidean NS equation at every point. -/
theorem baseVelocity_solves (nu t x y : ℝ) (i : Fin 2) :
    divergence (baseVelocity nu) t x y = 0 ∧ nsResidual nu 1 0 1 (baseVelocity nu) t x y i = 0 := by
  constructor
  · simp [divergence, dx, dy, baseVelocity, wave_dx, wave_dy]
  · simp only [nsResidual, dt, dxx, dxy, dyy, dx, dy, baseVelocity]
    rw [wave_dxx, wave_dxy, wave_dyy]
    simp only [wave_dt, wave_dx, wave_dy]
    fin_cases i <;> norm_num [wave] <;> ring

private def amplitude (k : ℕ) (i : Fin 2) : ℝ := if i = 0 then 1 else (k : ℝ)

/-- The full time-dependent velocity (1,k)*exp(-nu*rate*t)*cos(-2k*x+2y). -/
def shear (k : ℕ) (nu rate : ℝ) : PlanarField := fun t x y i =>
  wave (amplitude k i) (-2 * (k : ℝ)) 2 nu rate t x y

/-- The field is jointly smooth in time and both space coordinates. -/
theorem shear_contDiff (k : ℕ) (nu rate : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => shear k nu rate p.1 p.2.1 p.2.2) := by
  apply contDiff_pi.mpr
  intro i
  dsimp [shear, wave]
  fun_prop

/-- Actual spatial periodicity, with a fixed 2*pi convention. -/
theorem shear_periodic (k : ℕ) (nu rate t x y : ℝ) :
    shear k nu rate t (x + 2 * Real.pi) y = shear k nu rate t x y ∧
    shear k nu rate t x (y + 2 * Real.pi) = shear k nu rate t x y := by
  have hx : -2 * (k : ℝ) * (x + 2 * Real.pi) + 2 * y =
      (-2 * (k : ℝ) * x + 2 * y) + ((-2 * (k : ℤ) : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  have hy : -2 * (k : ℝ) * x + 2 * (y + 2 * Real.pi) =
      (-2 * (k : ℝ) * x + 2 * y) + ((2 : ℤ) : ℝ) * (2 * Real.pi) := by ring
  constructor <;> funext i
  · dsimp [shear, wave]
    rw [hx, Real.cos_add_int_mul_two_pi]
  · dsimp [shear, wave]
    rw [hy, Real.cos_add_int_mul_two_pi]

/-- The actual divergence vanishes, independently of the chosen decay rate. -/
theorem shear_divergence (k : ℕ) (nu rate t x y : ℝ) :
    divergence (shear k nu rate) t x y = 0 := by
  simp only [divergence, dx, dy, shear, wave_dx, wave_dy]
  norm_num [amplitude] <;> ring

/-- Full constant-metric NS residual, including the nonlinear advective terms.
They cancel because (1,k) is orthogonal to the covector (-2k,2). -/
theorem shear_residual (k : ℕ) (nu rate h00 h01 h11 t x y : ℝ) (i : Fin 2) :
    nsResidual nu h00 h01 h11 (shear k nu rate) t x y i =
      nu * (4 * h00 * (k : ℝ) ^ 2 - 8 * h01 * (k : ℝ) + 4 * h11 - rate) *
        shear k nu rate t x y i := by
  simp only [nsResidual, dt, dxx, dxy, dyy, dx, dy, shear]
  rw [wave_dxx, wave_dxy, wave_dyy]
  simp only [wave_dt, wave_dx, wave_dy]
  norm_num [wave, amplitude] <;> ring

/-- The actual real matrix supplied by the original arithmetic bridge. -/
def bridgeReal (k : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (bridge k).map (Int.castRingHom ℝ)

def inverseBridge (k : ℕ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; (k : ℝ), 1 / 2]

def pullbackMetric (k : ℕ) : Matrix (Fin 2) (Fin 2) ℝ := (bridgeReal k)ᵀ * bridgeReal k

def inverseMetric (k : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  inverseBridge k * (inverseBridge k)ᵀ

/-- Both inverse identities and the metric coefficients are derived from P_k. -/
theorem bridge_and_metric_identities (k : ℕ) :
    bridgeReal k * inverseBridge k = 1 ∧ inverseBridge k * bridgeReal k = 1 ∧
    inverseMetric k = !![1, (k : ℝ); (k : ℝ), (k : ℝ) ^ 2 + 1 / 4] ∧
    pullbackMetric k * inverseMetric k = 1 ∧ inverseMetric k * pullbackMetric k = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [bridgeReal, bridge, inverseBridge, inverseMetric, pullbackMetric,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Strict positivity of the transported inverse metric is a sum-of-squares fact. -/
theorem inverseMetric_positive (k : ℕ) (r s : ℝ) (h : r ≠ 0 ∨ s ≠ 0) :
    0 < r ^ 2 + 2 * (k : ℝ) * r * s + ((k : ℝ) ^ 2 + 1 / 4) * s ^ 2 := by
  have heq : r ^ 2 + 2 * (k : ℝ) * r * s + ((k : ℝ) ^ 2 + 1 / 4) * s ^ 2 =
      (r + (k : ℝ) * s) ^ 2 + s ^ 2 / 4 := by ring
  rw [heq]
  by_cases hs : s = 0
  · subst s
    rcases h with hr | hs
    · simpa using sq_pos_of_ne_zero hr
    · exact False.elim (hs rfl)
  · have hp := sq_pos_of_ne_zero hs
    nlinarith [sq_nonneg (r + (k : ℝ) * s)]

/-- Tensorially correct pullback of the vector field through the original P_k. -/
def pulledVelocity (k : ℕ) (nu : ℝ) : PlanarField := fun t x y =>
  (inverseBridge k).mulVec
    (baseVelocity nu t ((bridgeReal k).mulVec ![x, y] 0) ((bridgeReal k).mulVec ![x, y] 1))

theorem pulledVelocity_eq_shear (k : ℕ) (nu : ℝ) : pulledVelocity k nu = shear k nu 1 := by
  funext t x y i
  have hp : (bridgeReal k).mulVec ![x, y] = ![x, -2 * (k : ℝ) * x + 2 * y] := by
    funext j
    fin_cases j <;>
      norm_num [bridgeReal, bridge, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  change (inverseBridge k).mulVec
    (baseVelocity nu t ((bridgeReal k).mulVec ![x, y] 0)
      ((bridgeReal k).mulVec ![x, y] 1)) i = shear k nu 1 t x y i
  rw [hp]
  fin_cases i <;>
    norm_num [inverseBridge, baseVelocity, shear, wave, amplitude,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- The pulled field satisfies NS with the actual pulled constant metric. -/
theorem pulled_metric_solution (k : ℕ) (nu t x y : ℝ) (i : Fin 2) :
    divergence (pulledVelocity k nu) t x y = 0 ∧
    nsResidual nu 1 (k : ℝ) ((k : ℝ) ^ 2 + 1 / 4) (pulledVelocity k nu) t x y i = 0 := by
  rw [pulledVelocity_eq_shear]
  refine ⟨shear_divergence k nu 1 t x y, ?_⟩
  rw [shear_residual]
  have hzero : 4 * (1 : ℝ) * (k : ℝ) ^ 2 - 8 * (k : ℝ) * (k : ℝ) +
      4 * ((k : ℝ) ^ 2 + 1 / 4) - 1 = 0 := by ring
  rw [hzero, mul_zero, zero_mul]

/-- Retaining the original decay rate but replacing the pulled metric by the
Euclidean metric creates a nonzero, explicitly computed NS residual. -/
theorem pulled_euclidean_defect (k : ℕ) (nu t x y : ℝ) (i : Fin 2) :
    nsResidual nu 1 0 1 (pulledVelocity k nu) t x y i =
      nu * (4 * (k : ℝ) ^ 2 + 3) * pulledVelocity k nu t x y i := by
  rw [pulledVelocity_eq_shear, shear_residual]
  ring

/-- A literal evaluation witnesses failure for every physical viscosity nu>0. -/
theorem pulled_euclidean_defect_positive (k : ℕ) (nu : ℝ) (hnu : 0 < nu) :
    0 < nsResidual nu 1 0 1 (pulledVelocity k nu) 0 0 0 0 := by
  rw [pulled_euclidean_defect, pulledVelocity_eq_shear]
  norm_num [shear, wave, amplitude]
  positivity

/-- The same initial shear has a different exact Euclidean NS evolution, with
its actual squared spatial frequency as decay rate. -/
theorem euclidean_shear_solution (k : ℕ) (nu t x y : ℝ) (i : Fin 2) :
    divergence (shear k nu (4 * ((k : ℝ) ^ 2 + 1))) t x y = 0 ∧
    nsResidual nu 1 0 1 (shear k nu (4 * ((k : ℝ) ^ 2 + 1))) t x y i = 0 := by
  refine ⟨shear_divergence k nu _ t x y, ?_⟩
  rw [shear_residual]
  have hzero : 4 * (1 : ℝ) * (k : ℝ) ^ 2 - 8 * 0 * (k : ℝ) + 4 * 1 -
      4 * ((k : ℝ) ^ 2 + 1) = 0 := by ring
  rw [hzero, mul_zero, zero_mul]

/-- Both metric evolutions start from the identical literal velocity field. -/
theorem euclidean_and_pulled_same_initial (k : ℕ) (nu x y : ℝ) :
    shear k nu (4 * ((k : ℝ) ^ 2 + 1)) 0 x y = pulledVelocity k nu 0 x y := by
  rw [pulledVelocity_eq_shear]
  funext i
  simp [shear, wave]

#print axioms baseVelocity_solves
#print axioms shear_contDiff
#print axioms shear_periodic
#print axioms shear_divergence
#print axioms shear_residual
#print axioms bridge_and_metric_identities
#print axioms inverseMetric_positive
#print axioms pulledVelocity_eq_shear
#print axioms pulled_metric_solution
#print axioms pulled_euclidean_defect_positive
#print axioms euclidean_shear_solution
#print axioms euclidean_and_pulled_same_initial

end D5.S3.FluidDynamics.Fourier.ToralIsogenyShearNS
