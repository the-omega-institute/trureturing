/- GID: D5/S3/FluidDynamics/Stability/QuadraticEquilibriumCertificate
   generality: G
   mirror-B: D5/B/S3/FluidDynamics/Stability/QuadraticEquilibriumCertificate
   mirror-E: none(waiver:nonlinear-energy-and-residual-certificate)
   anchors: []
   utility: none
   digest: Bilinear energy cancellation yields nonlinear attraction, equilibrium uniqueness and a residual-to-state bound with one verified margin. -/

import D5.S3.FluidDynamics.Stability.DissipativeAttraction

/-!
Independently derived algebra for F(x)=Lx-B(x,x)+f on a real inner-product
space. B is an actual curried bilinear map. The cancellation hypothesis is
inner(b,B(a,b))=0, not an assumed contraction of F. Expanding about a given
stationary state leaves precisely the strain term inner(w,B(w,v)).

The linear dissipativity and strain bounds yield a margin mu-G. It controls
both time-dependent attraction and the static error from an actual residual.
Existence of the stationary state is required separately. The polynomial
model is not declared to be a continuum NS solution: on an actual PDE domain,
pressure orthogonality, derivative domains and integration by parts must be
proved before this algebra or the energy theorem can be used.

No external code or theorem port. The sole external formal dependency is
mathlib through the independently proved DissipativeAttraction module.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace

namespace D5.S3.FluidDynamics.Stability.QuadraticEquilibriumCertificate

open D5.S3.FluidDynamics.Stability.DissipativeAttraction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The literal quadratic vector field, with a fixed forcing vector. -/
def vectorField (L : H →ₗ[ℝ] H) (B : H →ₗ[ℝ] H →ₗ[ℝ] H) (f : H) (x : H) : H :=
  L x - B x x + f

/-- Full bilinear expansion and cancellation identify the surviving term.
The bilinear map need not be symmetric. -/
theorem difference_energy_identity
    (L : H →ₗ[ℝ] H) (B : H →ₗ[ℝ] H →ₗ[ℝ] H) (f v w : H)
    (hcancel : ∀ a b : H, ⟪b, B a b⟫_ℝ = 0) :
    ⟪w, vectorField L B f (v + w) - vectorField L B f v⟫_ℝ =
      ⟪w, L w⟫_ℝ - ⟪w, B w v⟫_ℝ := by
  simp only [vectorField, map_add, LinearMap.add_apply,
    inner_add_right, inner_sub_right, hcancel]
  ring

/-- The negative margin follows from two concrete quadratic-form bounds. -/
theorem shifted_energy_bound
    (L : H →ₗ[ℝ] H) (B : H →ₗ[ℝ] H →ₗ[ℝ] H) (f v : H) (μ G : ℝ)
    (hcancel : ∀ a b : H, ⟪b, B a b⟫_ℝ = 0)
    (hL : ∀ w : H, ⟪w, L w⟫_ℝ ≤ -μ * ‖w‖ ^ 2)
    (hstrain : ∀ w : H, -⟪w, B w v⟫_ℝ ≤ G * ‖w‖ ^ 2) (x : H) :
    ⟪x - v, vectorField L B f x - vectorField L B f v⟫_ℝ ≤
      -(μ - G) * ‖x - v‖ ^ 2 := by
  have hid := difference_energy_identity L B f v (x - v) hcancel
  have hvx : v + (x - v) = x := by abel
  rw [hvx] at hid
  rw [hid]
  nlinarith [hL (x - v), hstrain (x - v)]

/-- A small actual residual certifies proximity to the specified equilibrium.
This does not infer existence from a small residual. -/
theorem residual_controls_state
    (L : H →ₗ[ℝ] H) (B : H →ₗ[ℝ] H →ₗ[ℝ] H) (f v : H) (μ G : ℝ)
    (hcancel : ∀ a b : H, ⟪b, B a b⟫_ℝ = 0)
    (hL : ∀ w : H, ⟪w, L w⟫_ℝ ≤ -μ * ‖w‖ ^ 2)
    (hstrain : ∀ w : H, -⟪w, B w v⟫_ℝ ≤ G * ‖w‖ ^ 2)
    (hmargin : G < μ) (hstationary : vectorField L B f v = 0) (x : H) :
    ‖x - v‖ ≤ ‖vectorField L B f x‖ / (μ - G) := by
  have hγ : 0 < μ - G := sub_pos.mpr hmargin
  by_cases hx : x = v
  · subst x
    simp [hstationary]
  · have hn : 0 < ‖x - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
    have he := shifted_energy_bound L B f v μ G hcancel hL hstrain x
    rw [hstationary, sub_zero] at he
    have hc : -⟪x - v, vectorField L B f x⟫_ℝ ≤
        ‖x - v‖ * ‖vectorField L B f x‖ := by
      calc
        -⟪x - v, vectorField L B f x⟫_ℝ ≤ |⟪x - v, vectorField L B f x⟫_ℝ| := neg_le_abs _
        _ ≤ ‖x - v‖ * ‖vectorField L B f x‖ := norm_inner_le_norm _ _
    have hm : ((μ - G) * ‖x - v‖) * ‖x - v‖ ≤
        ‖vectorField L B f x‖ * ‖x - v‖ := by nlinarith
    have hshort : (μ - G) * ‖x - v‖ ≤ ‖vectorField L B f x‖ :=
      (mul_le_mul_iff_right₀ hn).mp hm
    exact (le_div_iff₀ hγ).mpr (by simpa [mul_comm] using hshort)

/-- One energy-stable stationary state excludes every other stationary state
in this same model and space. No global solution-existence theorem is used. -/
theorem equilibrium_unique
    (L : H →ₗ[ℝ] H) (B : H →ₗ[ℝ] H →ₗ[ℝ] H) (f v : H) (μ G : ℝ)
    (hcancel : ∀ a b : H, ⟪b, B a b⟫_ℝ = 0)
    (hL : ∀ w : H, ⟪w, L w⟫_ℝ ≤ -μ * ‖w‖ ^ 2)
    (hstrain : ∀ w : H, -⟪w, B w v⟫_ℝ ≤ G * ‖w‖ ^ 2)
    (hmargin : G < μ) (hstationary : vectorField L B f v = 0)
    (x : H) (hx : vectorField L B f x = 0) : x = v := by
  have h := residual_controls_state L B f v μ G hcancel hL hstrain hmargin hstationary x
  rw [hx, norm_zero, zero_div] at h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

/-- Actual trajectories of the nonlinear equation inherit the sharp forced
tube. The potentially large self-interaction cancels before any estimate. -/
theorem nonlinear_equilibrium_tube
    (L : H →ₗ[ℝ] H) (B : H →ₗ[ℝ] H →ₗ[ℝ] H) (f v : H) (μ G : ℝ)
    (hcancel : ∀ a b : H, ⟪b, B a b⟫_ℝ = 0)
    (hL : ∀ w : H, ⟪w, L w⟫_ℝ ≤ -μ * ‖w‖ ^ 2)
    (hstrain : ∀ w : H, -⟪w, B w v⟫_ℝ ≤ G * ‖w‖ ^ 2)
    (hmargin : G < μ) (hstationary : vectorField L B f v = 0)
    {T ρ : ℝ} {u r : ℝ → H} (hρ : 0 ≤ ρ)
    (hu : ContinuousOn u (Icc 0 T))
    (hode : ∀ s ∈ Ico 0 T,
      HasDerivWithinAt u (vectorField L B f (u s) + r s) (Ici s) s)
    (hr : ∀ s ∈ Ico 0 T, ‖r s‖ ≤ ρ) :
    ∀ t ∈ Icc 0 T,
      ‖u t - v‖ ≤ Real.exp (-(μ - G) * t) * ‖u 0 - v‖ +
        (ρ / (μ - G)) * (1 - Real.exp (-(μ - G) * t)) := by
  apply norm_tube_of_energy (sub_pos.mpr hmargin) hρ
    (hu.sub continuousOn_const) (fun s hs => (hode s hs).sub_const v)
  intro s hs
  have he := shifted_energy_bound L B f v μ G hcancel hL hstrain (u s)
  rw [hstationary, sub_zero] at he
  rw [inner_add_right]
  have hinner := real_inner_le_norm (u s - v) (r s)
  have hforce := mul_le_mul_of_nonneg_left (hr s hs) (norm_nonneg (u s - v))
  linarith

#print axioms difference_energy_identity
#print axioms shifted_energy_bound
#print axioms residual_controls_state
#print axioms equilibrium_unique
#print axioms nonlinear_equilibrium_tube

end D5.S3.FluidDynamics.Stability.QuadraticEquilibriumCertificate
