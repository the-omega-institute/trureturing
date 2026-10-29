/- GID: D5/S3/Analytic/Laplace/EulerLocalContinuation
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/EulerLocalContinuation
   mirror-E: none(waiver:analytic-proof-only)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.HasPrimitives, mathlib/module/Mathlib.Analysis.Analytic.Order]
   utility: none
   digest: Complex Euler equations extend across ordinary real cuts and across zero with a finite boundary value. -/

import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Analytic.Order
import Mathlib.Tactic

/-! Double primitives reduce the complex Euler equation to an affine defect. -/

noncomputable section
open Complex Set Filter Metric
open scoped Topology

namespace D5.S3.Analytic.Laplace.EulerLocalContinuation

/-- The complex right half of the disk with real center c. -/
def rightHalfDisk (c r : ℝ) : Set ℂ := ball (c : ℂ) r ∩ {z | c < z.re}

private theorem half_open (c r : ℝ) : IsOpen (rightHalfDisk c r) :=
  isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)

private theorem half_preconnected (c r : ℝ) : IsPreconnected (rightHalfDisk c r) :=
  ((convex_ball (c : ℂ) r).inter (convex_halfSpace_re_gt c)).isPreconnected

/-- Twice integrating the equation leaves precisely an affine defect in zF. -/
private theorem affine_defect {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {F R Q P : ℂ → ℂ} (hF : DifferentiableOn ℂ F U)
    (hQ : ∀ z ∈ U, HasDerivAt Q (R z) z)
    (hP : ∀ z ∈ U, HasDerivAt P (Q z) z)
    (hode : ∀ z ∈ U, z * deriv (deriv F) z + 2 * deriv F z = R z) :
    ∃ A B : ℂ, ∀ z ∈ U, z * F z - P z = A * z + B := by
  let E : ℂ → ℂ := fun z => F z + z * deriv F z - Q z
  have hE : ∀ z ∈ U, HasDerivAt E 0 z := by
    intro z hz
    have hd : HasDerivAt E
        (deriv F z + (deriv F z + z * deriv (deriv F) z) - R z) z := by
      simpa only [E, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, id_eq, one_mul] using!
        ((hF.hasDerivAt (hU.mem_nhds hz)).add
          ((hasDerivAt_id z).mul ((hF.deriv hU).hasDerivAt (hU.mem_nhds hz)))).sub
            (hQ z hz)
    have he : deriv F z + (deriv F z + z * deriv (deriv F) z) - R z = 0 := by
      linear_combination hode z hz
    exact he ▸ hd
  obtain ⟨A, hA⟩ := hU.exists_is_const_of_deriv_eq_zero hUc
    (fun z hz => (hE z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hE z hz).deriv)
  let G : ℂ → ℂ := fun z => z * F z - P z - A * z
  have hG : ∀ z ∈ U, HasDerivAt G 0 z := by
    intro z hz
    have hd : HasDerivAt G (F z + z * deriv F z - Q z - A) z := by
      simpa only [G, Pi.sub_apply, Pi.mul_apply, id_eq, one_mul, mul_one] using!
        ((((hasDerivAt_id z).mul (hF.hasDerivAt (hU.mem_nhds hz))).sub
          (hP z hz)).sub ((hasDerivAt_id z).const_mul A))
    have he : F z + z * deriv F z - Q z - A = 0 := sub_eq_zero.mpr (hA z hz)
    exact he ▸ hd
  obtain ⟨B, hB⟩ := hU.exists_is_const_of_deriv_eq_zero hUc
    (fun z hz => (hG z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hG z hz).deriv)
  refine ⟨A, B, fun z hz => ?_⟩
  have hb := hB z hz
  dsimp [G] at hb
  linear_combination hb

/-- Holomorphic forcing extends an Euler solution across any nonzero real cut center. -/
theorem exists_extension_of_ne_zero {c r : ℝ} (hc : c ≠ 0) (hr : 0 < r)
    {R F : ℂ → ℂ} (hR : DifferentiableOn ℂ R (ball (c : ℂ) r))
    (hF : DifferentiableOn ℂ F (rightHalfDisk c r))
    (hode : ∀ z ∈ rightHalfDisk c r,
      z * deriv (deriv F) z + 2 * deriv F z = R z) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ r ∧ ∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H (ball (c : ℂ) δ) ∧ EqOn H F (rightHalfDisk c δ) := by
  obtain ⟨Q, hQ⟩ := hR.isExactOn_ball
  have hQd : DifferentiableOn ℂ Q (ball (c : ℂ) r) :=
    fun z hz => (hQ z hz).differentiableAt.differentiableWithinAt
  obtain ⟨P, hP⟩ := hQd.isExactOn_ball
  obtain ⟨A, B, hAB⟩ := affine_defect (half_open c r) (half_preconnected c r) hF
    (fun z hz => hQ z hz.1) (fun z hz => hP z hz.1) hode
  let δ := min r (‖(c : ℂ)‖ / 2)
  have hn : 0 < ‖(c : ℂ)‖ := norm_pos_iff.mpr (Complex.ofReal_ne_zero.mpr hc)
  have hδ : 0 < δ := lt_min hr (half_pos hn)
  have hsub : ball (c : ℂ) δ ⊆ ball (c : ℂ) r := ball_subset_ball (min_le_left _ _)
  have hnz : ∀ z ∈ ball (c : ℂ) δ, z ≠ 0 := by
    intro z hz he
    subst z
    have hz' : ‖(c : ℂ)‖ < δ := by simpa [mem_ball, dist_eq_norm] using hz
    have : δ ≤ ‖(c : ℂ)‖ / 2 := min_le_right _ _
    linarith
  let H : ℂ → ℂ := fun z => (P z + A * z + B) / z
  refine ⟨δ, hδ, min_le_left _ _, H, ?_, ?_⟩
  · have hPd : DifferentiableOn ℂ P (ball (c : ℂ) δ) :=
      fun z hz => (hP z (hsub hz)).differentiableAt.differentiableWithinAt
    exact ((hPd.add ((differentiableOn_const A).mul differentiableOn_id)).add
      (differentiableOn_const B)).div differentiableOn_id hnz
  · intro z hz
    have he := hAB z ⟨hsub hz.1, hz.2⟩
    apply (div_eq_iff (hnz z hz.1)).mpr
    linear_combination -he

/-- A finite positive-real boundary limit removes the singular homogeneous solution at zero. -/
theorem exists_extension_at_zero {r : ℝ} (hr : 0 < r) {R F : ℂ → ℂ} {ell : ℂ}
    (hR : DifferentiableOn ℂ R (ball (0 : ℂ) r))
    (hF : DifferentiableOn ℂ F (rightHalfDisk 0 r))
    (hode : ∀ z ∈ rightHalfDisk 0 r,
      z * deriv (deriv F) z + 2 * deriv F z = R z)
    (hlim : Tendsto (fun x : ℝ => F (x : ℂ)) (𝓝[Ioi 0] 0) (𝓝 ell)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ r ∧ ∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H (ball (0 : ℂ) δ) ∧
        EqOn H F (rightHalfDisk 0 δ) ∧ H 0 = ell := by
  obtain ⟨Q, hQ0, hQ⟩ := hR.isExactOn_ball.with_val_at 0 ell
  have hQd : DifferentiableOn ℂ Q (ball (0 : ℂ) r) :=
    fun z hz => (hQ z hz).differentiableAt.differentiableWithinAt
  obtain ⟨P, hP0, hP⟩ := hQd.isExactOn_ball.with_val_at 0 0
  have hPd : DifferentiableOn ℂ P (ball (0 : ℂ) r) :=
    fun z hz => (hP z hz).differentiableAt.differentiableWithinAt
  obtain ⟨A, B, hAB⟩ := affine_defect (half_open 0 r) (half_preconnected 0 r) hF
    (fun z hz => hQ z hz.1) (fun z hz => hP z hz.1) hode
  obtain ⟨H, hHa, hfactor⟩ :=
    (hPd.analyticOnNhd isOpen_ball 0 (mem_ball_self hr)).exists_eq_sum_add_pow_mul 1
  have hfac : ∀ z : ℂ, P z = z * H z := by
    intro z
    simpa [hP0, Finset.sum_range_one, smul_eq_mul] using hfactor z
  have hPf : P = fun z => z * H z := funext hfac
  have hH0 : H 0 = ell := by
    have hh : HasDerivAt P (H 0) 0 := by
      rw [hPf]
      simpa using! (hasDerivAt_id (0 : ℂ)).mul hHa.differentiableAt.hasDerivAt
    exact (hh.unique (hP 0 (mem_ball_self hr))).trans hQ0
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hHa.eventually_analyticAt
  let δ := min r ε
  have hδ : 0 < δ := lt_min hr hε
  have hsub : ball (0 : ℂ) δ ⊆ ball (0 : ℂ) r := ball_subset_ball (min_le_left _ _)
  have hHd : DifferentiableOn ℂ H (ball (0 : ℂ) δ) := by
    intro z hz
    exact (hεsub (ball_subset_ball (min_le_right _ _) hz)).differentiableAt.differentiableWithinAt
  have hxmem : ∀ᶠ x : ℝ in 𝓝[Ioi 0] 0, (x : ℂ) ∈ rightHalfDisk 0 δ := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)] with x hx hxδ
    refine ⟨?_, hx⟩
    simpa [mem_ball, dist_eq_norm, Real.norm_eq_abs, abs_of_pos (show 0 < x from hx)] using hxδ
  have hxc : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[Ioi 0] 0) (𝓝 (0 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hPlim : Tendsto (fun x : ℝ => P (x : ℂ)) (𝓝[Ioi 0] 0) (𝓝 (0 : ℂ)) := by
    simpa only [Function.comp_def, hP0] using (hP 0 (mem_ball_self hr)).continuousAt.tendsto.comp hxc
  have hBlim : Tendsto (fun x : ℝ => (x : ℂ) * F (x : ℂ) - P (x : ℂ) - A * (x : ℂ))
      (𝓝[Ioi 0] 0) (𝓝 (0 : ℂ)) := by
    simpa using ((hxc.mul hlim).sub hPlim).sub (tendsto_const_nhds.mul hxc)
  have hBeq : (fun x : ℝ => (x : ℂ) * F (x : ℂ) - P (x : ℂ) - A * (x : ℂ))
      =ᶠ[𝓝[Ioi 0] 0] fun _ => B := by
    filter_upwards [hxmem] with x hx
    have he := hAB (x : ℂ) ⟨hsub hx.1, hx.2⟩
    linear_combination he
  have hB : B = 0 := tendsto_nhds_unique tendsto_const_nhds (hBlim.congr' hBeq)
  have hFA : ∀ z ∈ rightHalfDisk 0 δ, F z = H z + A := by
    intro z hz
    have hnz : z ≠ 0 := by intro he; simpa [he] using hz.2
    apply mul_left_cancel₀ hnz
    have he := hAB z ⟨hsub hz.1, hz.2⟩
    rw [hfac z, hB] at he
    linear_combination he
  have hHlim : Tendsto (fun x : ℝ => H (x : ℂ) + A) (𝓝[Ioi 0] 0) (𝓝 (ell + A)) := by
    simpa [hH0] using (hHa.continuousAt.tendsto.comp hxc).add_const A
  have hAeq : (fun x : ℝ => F (x : ℂ)) =ᶠ[𝓝[Ioi 0] 0] fun x => H (x : ℂ) + A := by
    filter_upwards [hxmem] with x hx
    exact hFA _ hx
  have hA : A = 0 := by
    have he : ell = ell + A := tendsto_nhds_unique hlim (hHlim.congr' hAeq.symm)
    linear_combination -he
  refine ⟨δ, hδ, min_le_left _ _, H, hHd, ?_, hH0⟩
  intro z hz
  simpa [hA] using (hFA z hz).symm

end D5.S3.Analytic.Laplace.EulerLocalContinuation
