/- GID: D5/S3/FluidDynamics/Stability/DissipativeAttraction
   generality: G
   mirror-B: D5/B/S3/FluidDynamics/Stability/DissipativeAttraction
   mirror-E: none(waiver:regularized-energy-comparison)
   anchors: []
   utility: none
   digest: A mathlib-only regularized-energy proof gives sharp forced attraction without a bounded-generator premise. -/

import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Tactic

/-!
Independent proof from mathlib: apply scalar signed Gronwall comparison to
sqrt(norm(u)^2 + delta^2), then let the positive regularizer tend to zero.
There is no copied external proof, external theorem import or new axiom.
The proof neither differentiates the norm at zero nor assumes a linear
bounded generator. A strong Hilbert-space derivative and its actual energy
inequality are the inputs. This does not construct a PDE solution or prove
that an arbitrary weak solution has that derivative.

The previous PR candidate's externally ported three-helper proof is replaced,
not renamed. Classical dissipative comparison remains classical mathematics.
Pinned mathlib db584cd6 supplies norm-square differentiation, square root,
scalar Gronwall and order/continuity passage at the regularization endpoint.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology InnerProductSpace

namespace D5.S3.FluidDynamics.Stability.DissipativeAttraction

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Sharp state-norm control from the actual derivative energy inequality.
The forcing budget must be nonnegative, and the rate is strictly positive.
Only right derivatives before the final endpoint are required. -/
theorem norm_tube_of_energy
    {T γ ρ : ℝ} {u du : ℝ → H}
    (hγ : 0 < γ) (hρ : 0 ≤ ρ)
    (hu : ContinuousOn u (Icc 0 T))
    (hdu : ∀ s ∈ Ico 0 T, HasDerivWithinAt u (du s) (Ici s) s)
    (henergy : ∀ s ∈ Ico 0 T,
      ⟪u s, du s⟫_ℝ ≤ -γ * ‖u s‖ ^ 2 + ρ * ‖u s‖) :
    ∀ t ∈ Icc 0 T,
      ‖u t‖ ≤ Real.exp (-γ * t) * ‖u 0‖ +
        (ρ / γ) * (1 - Real.exp (-γ * t)) := by
  intro t ht
  let B : ℝ → ℝ := fun δ =>
    Real.sqrt (‖u 0‖ ^ 2 + δ ^ 2) * Real.exp (-γ * t) +
      ((ρ + γ * δ) / γ) * (1 - Real.exp (-γ * t))
  have hreg : ∀ δ ∈ Ioi (0 : ℝ), ‖u t‖ ≤ B δ := by
    intro δ hδ
    have hδpos : 0 < δ := hδ
    let z : ℝ → ℝ := fun s => Real.sqrt (‖u s‖ ^ 2 + δ ^ 2)
    have hzpos (s : ℝ) : 0 < z s := by
      dsimp [z]
      exact Real.sqrt_pos.mpr (by nlinarith [sq_nonneg ‖u s‖, sq_pos_of_ne_zero hδpos.ne'])
    have hzsq (s : ℝ) : (z s) ^ 2 = ‖u s‖ ^ 2 + δ ^ 2 :=
      Real.sq_sqrt (by positivity)
    have huz (s : ℝ) : ‖u s‖ ≤ z s := by
      nlinarith [hzsq s, (hzpos s).le, norm_nonneg (u s), sq_nonneg δ]
    have hδz (s : ℝ) : δ ≤ z s := by
      nlinarith [hzsq s, (hzpos s).le, sq_nonneg ‖u s‖]
    have hzc : ContinuousOn z (Icc 0 T) :=
      Real.continuous_sqrt.comp_continuousOn ((hu.norm.pow 2).add continuousOn_const)
    have hzd (s : ℝ) (hs : s ∈ Ico 0 T) :
        HasDerivWithinAt z (⟪u s, du s⟫_ℝ / z s) (Ici s) s := by
      have harg : ‖u s‖ ^ 2 + δ ^ 2 ≠ 0 := by positivity
      have h := ((hdu s hs).norm_sq.add_const (δ ^ 2)).sqrt harg
      simpa only [z, mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)] using h
    have hzb (s : ℝ) (hs : s ∈ Ico 0 T) :
        ⟪u s, du s⟫_ℝ / z s ≤ -γ * z s + (ρ + γ * δ) := by
      apply (div_le_iff₀ (hzpos s)).mpr
      have hρdiff := mul_nonneg hρ (sub_nonneg.mpr (huz s))
      have hδdiff := mul_nonneg (mul_nonneg hγ.le hδpos.le) (sub_nonneg.mpr (hδz s))
      have hγsq := congrArg (fun r : ℝ => γ * r) (hzsq s)
      nlinarith [henergy s hs, hγsq]
    have hb := le_gronwallBound_of_liminf_deriv_right_le
      (f := z) (f' := fun s => ⟪u s, du s⟫_ℝ / z s)
      (δ := z 0) (K := -γ) (ε := ρ + γ * δ)
      hzc (fun s hs r hr => (hzd s hs).liminf_right_slope_le hr)
      (le_refl _) hzb t ht
    have hneg : -γ ≠ 0 := neg_ne_zero.mpr hγ.ne'
    simp only [gronwallBound, if_neg hneg, sub_zero] at hb
    calc
      ‖u t‖ ≤ z t := huz t
      _ ≤ z 0 * Real.exp (-γ * t) +
          ((ρ + γ * δ) / (-γ)) * (Real.exp (-γ * t) - 1) := hb
      _ = B δ := by dsimp [B, z]; rw [div_neg]; ring
  have hBc : Continuous B := by dsimp [B]; fun_prop
  have hlimit : ‖u t‖ ≤ B 0 :=
    continuousWithinAt_const.closure_le hBc.continuousWithinAt
      (by simp : (0 : ℝ) ∈ closure (Ioi (0 : ℝ))) hreg
  simpa [B, Real.sqrt_sq_eq_abs, abs_norm, mul_comm] using hlimit

/-- A bounded linear equation is one consumer of the energy theorem. The
proof checks its energy inequality directly; it does not postulate a bound
for the solution operator. The continuity of f is retained for compatibility. -/
theorem norm_le_exponential_tube
    {T γ ρ : ℝ} {u f : ℝ → H} (A : ℝ → H →L[ℝ] H)
    (hγ : 0 < γ) (hu : ContinuousOn u (Icc 0 T)) (_hf : Continuous f)
    (hode : ∀ t ∈ Ico 0 T,
      HasDerivWithinAt u (A t (u t) + f t) (Ici t) t)
    (hA : ∀ t ∈ Ico 0 T, ∀ x : H, ⟪x, A t x⟫_ℝ ≤ -γ * ‖x‖ ^ 2)
    (hforce : ∀ t ∈ Icc 0 T, ‖f t‖ ≤ ρ) :
    ∀ t ∈ Icc 0 T,
      ‖u t‖ ≤ Real.exp (-γ * t) * ‖u 0‖ +
        (ρ / γ) * (1 - Real.exp (-γ * t)) := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hρ : 0 ≤ ρ := (norm_nonneg (f 0)).trans (hforce 0 ⟨le_rfl, hT⟩)
  apply norm_tube_of_energy hγ hρ hu hode ?_ t ht
  intro s hs
  rw [inner_add_right]
  have hi := add_le_add (hA s hs (u s)) (real_inner_le_norm (u s) (f s))
  have hf := mul_le_mul_of_nonneg_left (hforce s (Ico_subset_Icc_self hs)) (norm_nonneg (u s))
  linarith

/-- Zero forcing retains the strictly negative rate. Global existence is a
separate obligation when this finite-interval estimate is used at all times. -/
theorem unforced_norm_contraction
    {T γ : ℝ} {u : ℝ → H} (A : ℝ → H →L[ℝ] H)
    (hγ : 0 < γ) (hu : ContinuousOn u (Icc 0 T))
    (hode : ∀ t ∈ Ico 0 T, HasDerivWithinAt u (A t (u t)) (Ici t) t)
    (hA : ∀ t ∈ Ico 0 T, ∀ x : H, ⟪x, A t x⟫_ℝ ≤ -γ * ‖x‖ ^ 2) :
    ∀ t ∈ Icc 0 T, ‖u t‖ ≤ Real.exp (-γ * t) * ‖u 0‖ := by
  have h := norm_tube_of_energy (ρ := 0) hγ (le_refl 0) hu hode
    (fun s hs => by simpa using hA s hs (u s))
  simpa using h

/-- Scalar equilibrium certificate, used by the actual forced shear module. -/
theorem scalar_equilibrium_tube {T γ ρ c : ℝ} {a r : ℝ → ℝ}
    (hγ : 0 < γ) (ha : ContinuousOn a (Icc 0 T)) (hr : Continuous r)
    (hode : ∀ t ∈ Ico 0 T,
      HasDerivWithinAt a (-γ * (a t - c) + r t) (Ici t) t)
    (hforce : ∀ t ∈ Icc 0 T, |r t| ≤ ρ) :
    ∀ t ∈ Icc 0 T,
      |a t - c| ≤ Real.exp (-γ * t) * |a 0 - c| +
        (ρ / γ) * (1 - Real.exp (-γ * t)) := by
  let A : ℝ → ℝ →L[ℝ] ℝ := fun _ => (-γ) • ContinuousLinearMap.id ℝ ℝ
  have hd (s : ℝ) (hs : s ∈ Ico 0 T) :
      HasDerivWithinAt (fun t => a t - c) (A s (a s - c) + r s) (Ici s) s := by
    simpa [A, smul_eq_mul] using (hode s hs).sub_const c
  have hA (s : ℝ) (_hs : s ∈ Ico 0 T) (x : ℝ) :
      ⟪x, A s x⟫_ℝ ≤ -γ * ‖x‖ ^ 2 := by
    change ⟪x, (-γ) • x⟫_ℝ ≤ -γ * ‖x‖ ^ 2
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
  simpa only [Real.norm_eq_abs] using norm_le_exponential_tube
    A hγ (ha.sub continuousOn_const) hr hd hA
    (by simpa only [Real.norm_eq_abs] using hforce)

end Hilbert

#print axioms norm_tube_of_energy
#print axioms norm_le_exponential_tube
#print axioms unforced_norm_contraction
#print axioms scalar_equilibrium_tube

end D5.S3.FluidDynamics.Stability.DissipativeAttraction
