/- GID: D5/S3/Topology/BanachQuadraticRigidity
   generality: G
   mirror-B: D5/B/S3/Topology/BanachQuadraticRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Exponential]
   utility: none
   digest: Symmetric quadratic ODEs preserve distance in arbitrary real Banach spaces. -/

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Normed.Affine.MazurUlam
import D5.S3.Geometry.ODE.UniformLocalGlobalPasting

/-! Distance conservation without a differentiability hypothesis on the norm. -/

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

/-- Normalize speed, not the state space. A common local time near zero for
the quadratic field gives a common local time on all states for this field. -/
private theorem exists_global_quadratic_solution
    (B : E →L[ℝ] E →L[ℝ] E)
    (hsymm : ∀ x y : E, B x y = B y x)
    (hiso : ∀ (x : E) (t : ℝ),
      Isometry (fun y : E => (NormedSpace.exp (t • B x)) y))
    (x₀ : E) : ∃ γ : ℝ → E, γ 0 = x₀ ∧
      ∀ t : ℝ, HasDerivAt γ (B (γ t) (γ t)) t := by
  have hnorm {s : Set ℝ} (hs : IsOpen s) (hc : IsPreconnected s)
      {x : ℝ → E} (hx : ∀ t ∈ s, HasDerivAt x (B (x t) (x t)) t)
      {t u : ℝ} (ht : t ∈ s) (hu : u ∈ s) : ‖x t‖ = ‖x u‖ := by
    simpa using quadratic_solution_dist_eq B hsymm hiso hs hc hx
      (x := x) (y := fun _ => 0) (fun t _ => by simpa using hasDerivAt_const t (0 : E)) ht hu
  have hC1 : ContDiff ℝ 1 (fun x : E => B x x) :=
    B.isBoundedBilinearMap.contDiff.comp (contDiff_id.prodMk contDiff_id)
  obtain ⟨r, hr, ε, hε, hlocal⟩ :=
    hC1.contDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt (0 : ℝ)
  let f : E → E := fun x => (1 + ‖x‖)⁻¹ • B x x
  have hflocal (x : E) : ∃ C : ℝ → E, C 0 = x ∧
      ∀ t ∈ Ioo (-(r * ε)) (r * ε), HasDerivAt C (f (C t)) t := by
    let a : ℝ := r / (1 + ‖x‖)
    have hden : 0 < 1 + ‖x‖ := by positivity
    have ha : 0 < a := div_pos hr hden
    have hax : a • x ∈ Metric.closedBall (0 : E) r := by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
      dsimp [a]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hden).2
      nlinarith [norm_nonneg x]
    obtain ⟨C, hC0, hCd⟩ := hlocal (a • x) hax
    have hCd' : ∀ t ∈ Ioo (-ε) ε, HasDerivAt C (B (C t) (C t)) t := by
      simpa only [zero_sub, zero_add] using hCd
    have hCn (t : ℝ) (ht : t ∈ Ioo (-ε) ε) : ‖C t‖ = a * ‖x‖ := by
      have hn := hnorm isOpen_Ioo (convex_Ioo (-ε) ε).isPreconnected hCd'
        ht (show (0 : ℝ) ∈ Ioo (-ε) ε from ⟨by linarith, hε⟩)
      simpa [hC0, norm_smul, Real.norm_eq_abs, abs_of_pos ha] using hn
    refine ⟨fun t => a⁻¹ • C (t / r), ?_, ?_⟩
    · simp [hC0, smul_smul, ne_of_gt ha]
    · intro t ht
      have htr : t / r ∈ Ioo (-ε) ε := by
        constructor
        · exact (lt_div_iff₀ hr).2 (by nlinarith [ht.1])
        · exact (div_lt_iff₀ hr).2 (by nlinarith [ht.2])
      have hd := ((hCd' (t / r) htr).scomp (h := fun t : ℝ => t / r) t ((hasDerivAt_id t).div_const r)).const_smul a⁻¹
      have hn : ‖a⁻¹ • C (t / r)‖ = ‖x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha), hCn _ htr]
        field_simp
      have hcoeff : f (a⁻¹ • C (t / r)) = a⁻¹ • ((1 / r) • B (C (t / r)) (C (t / r))) := by
        dsimp [f]
        rw [hn]
        simp only [map_smul, smul_apply, smul_smul]
        congr 1
        dsimp [a]
        field_simp
      rw [hcoeff]
      convert hd using 1 <;> ext v <;> rfl
  obtain ⟨γ, hγ0, hγd⟩ :=
    D5.S3.Geometry.ODE.UniformLocalGlobalPasting.exists_global_solution_of_uniform_local
      f (mul_pos hr hε) hflocal x₀
  have hγn (t : ℝ) : ‖γ t‖ = ‖x₀‖ := by
    have hd (t : ℝ) : HasDerivAt (fun s => ‖γ s‖) 0 t := by
      apply hasDerivAt_norm_of_exp_isometry ((1 + ‖γ t‖)⁻¹ • B (γ t))
      · intro h
        simpa only [smul_smul] using hiso (γ t) (h * (1 + ‖γ t‖)⁻¹)
      · simpa [f] using hγd t
    have hn := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
      (fun t => (hd t).deriv) t 0
    simpa [hγ0] using hn
  refine ⟨fun t => γ ((1 + ‖x₀‖) * t), by simpa using hγ0, ?_⟩
  intro t
  have hd := (hγd ((1 + ‖x₀‖) * t)).scomp (h := fun t : ℝ => (1 + ‖x₀‖) * t) t
    ((hasDerivAt_id t).const_mul (1 + ‖x₀‖))
  simpa [Function.comp_def, f, hγn, smul_smul,
    ne_of_gt (show 0 < 1 + ‖x₀‖ by positivity)] using hd

/-- Symmetric bilinear exponential-isometry rigidity in an arbitrary real
Banach space, with no supplied flow or dimension restriction. -/
theorem eq_zero_of_symmetric_exp_isometry
    (B : E →L[ℝ] E →L[ℝ] E)
    (hsymm : ∀ x y : E, B x y = B y x)
    (hiso : ∀ (x : E) (t : ℝ),
      Isometry (fun y : E => (NormedSpace.exp (t • B x)) y)) : B = 0 := by
  classical
  choose φ hφ0 hφd using exists_global_quadratic_solution B hsymm hiso
  have hdist {x y : ℝ → E}
      (hx : ∀ t, HasDerivAt x (B (x t) (x t)) t)
      (hy : ∀ t, HasDerivAt y (B (y t) (y t)) t) (t u : ℝ) :
      dist (x t) (y t) = dist (x u) (y u) :=
    quadratic_solution_dist_eq B hsymm hiso isOpen_univ isPreconnected_univ
      (fun t _ => hx t) (fun t _ => hy t) (mem_univ t) (mem_univ u)
  have huniq {x y : ℝ → E}
      (hx : ∀ t, HasDerivAt x (B (x t) (x t)) t)
      (hy : ∀ t, HasDerivAt y (B (y t) (y t)) t)
      (h0 : x 0 = y 0) (t : ℝ) : x t = y t := by
    apply dist_eq_zero.mp
    rw [hdist hx hy t 0, h0, dist_self]
  have hcomp (x : E) (s t : ℝ) : φ (φ x t) s = φ x (s + t) := by
    apply huniq (hφd (φ x t))
      (fun v => (hφd x (v + t)).comp_add_const v t) (by simp [hφ0]) s
  have hzero (t : ℝ) : φ 0 t = 0 := by
    apply huniq (hφd 0) (y := fun _ => 0)
      (fun v => by simpa using hasDerivAt_const v (0 : E)) (hφ0 0) t
  have hisometry (t : ℝ) : Isometry (fun x => φ x t) := by
    apply isometry_iff_dist_eq.2
    intro x y
    simpa [hφ0] using hdist (hφd x) (hφd y) t 0
  have hlinear (t : ℝ) : ∀ (c : ℝ) (x : E), φ (c • x) t = c • φ x t := by
    let e : E ≃ᵢ E := IsometryEquiv.mk' (fun x => φ x t) (fun x => φ x (-t))
      (fun x => by rw [hcomp]; simpa using hφ0 x) (hisometry t)
    exact (e.toRealLinearIsometryEquivOfMapZero (hzero t)).map_smul
  have hdiag (x : E) : B x x = 0 := by
    have hfun : φ ((2 : ℝ) • x) = (fun t => (2 : ℝ) • φ x t) :=
      funext (fun t => hlinear t 2 x)
    have hleft := hφd ((2 : ℝ) • x) 0
    rw [hfun] at hleft
    have heq := hleft.unique ((hφd x 0).const_smul (2 : ℝ))
    simp only [hφ0, map_smul, smul_apply, smul_smul] at heq
    have htwo : (2 : ℝ) • B x x = 0 := by
      apply add_left_cancel (a := (2 : ℝ) • B x x)
      simpa only [add_zero, ← add_smul] using heq
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  ext x y
  have htwo : (2 : ℝ) • B x y = 0 := by
    simpa [map_add, add_apply, hdiag, hsymm, two_smul] using hdiag (x + y)
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

end D5.S3.Topology.BanachQuadraticRigidity
