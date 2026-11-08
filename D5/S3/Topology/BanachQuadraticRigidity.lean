/- GID: D5/S3/Topology/BanachQuadraticRigidity
   generality: G
   mirror-B: D5/B/S3/Topology/BanachQuadraticRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Exponential]
   utility: none
   digest: Symmetric quadratic ODEs preserve distance in arbitrary real Banach spaces. -/

module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Distance conservation without a differentiability hypothesis on the norm. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter Asymptotics
open scoped Topology

namespace D5.S3.Topology.BanachQuadraticRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Comparison with the frozen linear orbit differentiates the norm along the
curve without differentiating the ambient norm. -/
private theorem hasDerivAt_norm_of_exp_isometry
    (A : E →L[ℝ] E)
    (hA : ∀ h : ℝ, Isometry (fun v : E => (NormedSpace.exp (h • A)) v))
    {z : ℝ → E} {t : ℝ} (hz : HasDerivAt z (A (z t)) t) :
    HasDerivAt (fun s => ‖z s‖) 0 t := by
  let w : ℝ → E := fun s => (NormedSpace.exp ((s - t) • A)) (z t)
  have hw : HasDerivAt w (A (z t)) t := by
    have hd := ((hasDerivAt_exp_smul_const A (t - t)).scomp (h := fun s : ℝ => s - t) t
      ((hasDerivAt_id t).sub_const t)).clm_apply (hasDerivAt_const t (z t))
    simpa [w, NormedSpace.exp_zero, mul_apply_eq_comp] using hd
  have hwval : w t = z t := by simp [w, NormedSpace.exp_zero]
  have hwnorm (s : ℝ) : ‖w s‖ = ‖z t‖ :=
    (hA (s - t)).norm_map_of_map_zero (map_zero _) _
  have hsmall : (fun s => z s - w s) =o[𝓝 t] (fun s => s - t) := by
    simpa only [Pi.sub_apply, sub_self, hwval, smul_zero, sub_zero] using (hz.sub hw).isLittleO
  apply HasDerivAt.of_isLittleO
  simp only [smul_zero, sub_zero]
  apply (isBigO_of_le (𝓝 t) (f := fun s => ‖z s‖ - ‖z t‖)
    (g := fun s => z s - w s) ?_).trans_isLittleO hsmall
  intro s
  rw [← hwnorm s, Real.norm_eq_abs]
  exact abs_norm_sub_norm_le _ _

/-- Two solutions of the same symmetric quadratic equation preserve their
distance on every open connected time domain, for an arbitrary Banach norm. -/
theorem quadratic_solution_dist_eq
    (B : E →L[ℝ] E →L[ℝ] E)
    (hsymm : ∀ x y : E, B x y = B y x)
    (hiso : ∀ (x : E) (t : ℝ),
      Isometry (fun y : E => (NormedSpace.exp (t • B x)) y))
    {s : Set ℝ} (hs : IsOpen s) (hconn : IsPreconnected s)
    {x y : ℝ → E}
    (hx : ∀ t ∈ s, HasDerivAt x (B (x t) (x t)) t)
    (hy : ∀ t ∈ s, HasDerivAt y (B (y t) (y t)) t)
    {t u : ℝ} (ht : t ∈ s) (hu : u ∈ s) :
    dist (x t) (y t) = dist (x u) (y u) := by
  have hd (v : ℝ) (hv : v ∈ s) :
      HasDerivAt (fun w => ‖x w - y w‖) 0 v := by
    apply hasDerivAt_norm_of_exp_isometry (B (x v + y v)) (hiso _)
    have halg : B (x v + y v) (x v - y v) =
        B (x v) (x v) - B (y v) (y v) := by
      simp only [map_add, add_apply, map_sub]
      rw [hsymm (y v) (x v)]
      abel
    rw [halg]
    exact (hx v hv).sub (hy v hv)
  rw [dist_eq_norm, dist_eq_norm]
  exact hs.is_const_of_deriv_eq_zero hconn
    (fun v hv => (hd v hv).differentiableAt.differentiableWithinAt)
    (fun v hv => (hd v hv).deriv) ht hu

end D5.S3.Topology.BanachQuadraticRigidity
