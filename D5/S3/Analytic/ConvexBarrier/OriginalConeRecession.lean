/- GID: D5/S3/Analytic/ConvexBarrier/OriginalConeRecession
   generality: I
   mirror-B: D5/B/S3/Analytic/ConvexBarrier/OriginalConeRecession
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Formalized power-cone geometry and analytic support module. -/

import D5.S3.Analytic.ConvexBarrier.HomogeneousHessian
import D5.S3.Analytic.ConvexBarrier.RecessionOneDimensional
import Mathlib.Analysis.Convex.Topology

/-!
Direct original-cone gradient/Hessian control. The geometric interface
contains only ordinary cone-domain operations. The concrete power-cone
application proves every one of them from its defining inequalities.

The gradient sign is derived from Hessian convexity and log homogeneity.
For lambda >= 1, -nu*log(lambda) <= 0 already suffices; no log/r growth
assumption is needed. Closed endpoints are approached by y+epsilon*x.
The actual Frechet line jets then supply the recession theorem's data.

This standard self-concordance argument replaces the dual-side quadratic
supplier for the chord estimate of Zhang--Fu--Dai, arXiv:2611.06404v1,
Lemma 3.2. It asserts no global conjugate theory or optimality theorem.
SOURCE ONLY, UNCOMPILED; no kernel/CI/official/novelty claim.
-/

open Set Filter
open scoped Topology ContDiff

namespace D5.S3.Analytic.ConvexBarrier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Only geometry: no gradient sign, ray derivative, Dikin estimate,
support covector, conjugate, or desired bound is included. -/
structure ConeRayGeometry (D K : Set E) : Prop where
  convex_domain : Convex ℝ D
  scale_domain : ∀ x ∈ D, ∀ t : ℝ, 0 < t → t • x ∈ D
  scale_cone : ∀ y ∈ K, ∀ t : ℝ, 0 ≤ t → t • y ∈ K
  add_domain_cone : ∀ x ∈ D, ∀ y ∈ K, x+y ∈ D

/-- Hessian positivity integrated twice along the segment gives the
actual first-order convex supporting inequality. -/
theorem IsLHSCB.supporting_inequality {ν : ℝ} {D B : Set E} {F : E → ℝ}
    (hF : IsLHSCB ν D B F) (hconv : Convex ℝ D)
    {x z : E} (hx : x ∈ D) (hz : z ∈ D) :
    F x+fderiv ℝ F x (z-x) ≤ F z := by
  by_cases hzx : z = x
  · subst z
    simp
  let v := z-x
  have hv : v ≠ 0 := sub_ne_zero.mpr hzx
  have hline : ∀ t ∈ Icc (0 : ℝ) 1, x+t • v ∈ D :=
    fun t ht => hconv.add_smul_sub_mem hx hz ht
  let f := lineJet 0 F x v
  let g := lineJet 1 F x v
  let q := lineJet 2 F x v
  have hg : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g (q t) t :=
    fun t ht => hF.lineJet_hasDerivAt (hline t ht) (by norm_num)
  have hq : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ q t := by
    intro t ht
    dsimp only [q]
    rw [hF.lineJet_eq_diagonal (hline t ht) (by norm_num)]
    exact (hF.hessian_pos _ (hline t ht) v hv).le
  have hgm := monotoneOn_from_hasDerivAt
    (convex_Icc (0 : ℝ) 1) hg hq
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hone : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hd : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun u => f u-u*g 0) (g t-g 0) t := by
    intro t ht
    convert (hF.lineJet_hasDerivAt (n := 0) (hline t ht) (by norm_num)).sub
      ((hasDerivAt_id t).mul_const (g 0)) using 1
    · ext u
      simp [f, g]
    · simp [f, g]
  have hfm := monotoneOn_from_hasDerivAt
    (convex_Icc (0 : ℝ) 1) hd (fun t ht =>
    sub_nonneg.mpr (hgm hzero ht ht.1))
  have hh := hfm hzero hone (by norm_num)
  have hl1 : x+(1 : ℝ) • v = z := by dsimp [v]; simp only [one_smul]; abel
  have hh' : F x ≤ F z-fderiv ℝ F x (z-x) := by
    simpa [f, g, lineJet, hl1, v] using hh
  linarith

/-- The interior gradient sign is proved, not supplied. Log homogeneity
at lambda*y and the supporting inequality would force linear positive
growth if DF(x)[y] were positive, while F(lambda*y) <= F(y) for lambda>=1.
The explicit lambda below makes that contradiction finite. -/
theorem IsLHSCB.gradient_nonpos_interior {ν : ℝ} {D B : Set E} {F : E → ℝ}
    (hF : IsLHSCB ν D B F) (hconv : Convex ℝ D)
    (hscale : ∀ y ∈ D, ∀ t : ℝ, 0 < t → t • y ∈ D)
    {x y : E} (hx : x ∈ D) (hy : y ∈ D) : fderiv ℝ F x y ≤ 0 := by
  by_contra hn
  have hg : 0 < fderiv ℝ F x y := lt_of_not_ge hn
  let C := F y-F x+fderiv ℝ F x x
  let lam := max 1 ((C+1)/fderiv ℝ F x y)
  have hlam1 : 1 ≤ lam := le_max_left _ _
  have hlam : 0 < lam := lt_of_lt_of_le zero_lt_one hlam1
  have hs := hF.supporting_inequality hconv hx (hscale y hy lam hlam)
  rw [hF.homogeneous y hy lam hlam, map_sub, map_smul, smul_eq_mul] at hs
  have hlog : 0 ≤ ν*Real.log lam :=
    mul_nonneg hF.parameter_pos.le (Real.log_nonneg hlam1)
  have hupper : lam*fderiv ℝ F x y ≤ C := by dsimp [C]; linarith
  have hlower : C+1 ≤ lam*fderiv ℝ F x y := by
    have hh := mul_le_mul_of_nonneg_right
      (le_max_right (1 : ℝ) ((C+1)/fderiv ℝ F x y)) hg.le
    simpa only [div_mul_cancel₀ _ hg.ne'] using hh
  linarith

/-- The sign on every closed-cone direction, including coordinate-zero
faces. The approximating points are the actual y+epsilon*x, epsilon>0. -/
theorem IsLHSCB.gradient_nonpos_cone {ν : ℝ} {D B K : Set E} {F : E → ℝ}
    (hF : IsLHSCB ν D B F) (hgeom : ConeRayGeometry D K)
    {x y : E} (hx : x ∈ D) (hy : y ∈ K) : fderiv ℝ F x y ≤ 0 := by
  let eps : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have heps : ∀ n, 0 < eps n := fun n => by dsimp [eps]; positivity
  have happrox : ∀ n, y+eps n • x ∈ D := by
    intro n
    simpa only [add_comm] using hgeom.add_domain_cone
      (eps n • x) (hgeom.scale_domain x hx _ (heps n)) y hy
  have hsign : ∀ n, fderiv ℝ F x (y+eps n • x) ≤ 0 := fun n =>
    hF.gradient_nonpos_interior hgeom.convex_domain hgeom.scale_domain hx (happrox n)
  have hu : Tendsto (fun n => y+eps n • x) atTop (𝓝 y) := by
    have hh := (tendsto_const_nhds (x := y)).add
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul
        (tendsto_const_nhds (x := x)))
    simpa only [eps, zero_smul, add_zero] using hh
  exact le_of_tendsto' (((fderiv ℝ F x).continuous.tendsto y).comp hu) hsign

/-- The entire original cone ray stays in the actual open domain. -/
theorem ConeRayGeometry.ray_mem {D K : Set E} (hgeom : ConeRayGeometry D K)
    {x y : E} (hx : x ∈ D) (hy : y ∈ K) {t : ℝ} (ht : 0 ≤ t) :
    x+t • y ∈ D :=
  hgeom.add_domain_cone x hx (t • y) (hgeom.scale_cone y hy t ht)

/-- Direct original-cone recession gradient/Hessian theorem, with every
line derivative inherited from the actual Frechet tensors of F. This
works for boundary directions y as well as interior directions; it uses
neither finite-boundary blowup nor a limiting value for DF(x+t*y)[y]. -/
theorem IsLHSCB.original_cone_gradient_hessian {ν : ℝ} {D B K : Set E}
    {F : E → ℝ} (hF : IsLHSCB ν D B F) (hgeom : ConeRayGeometry D K)
    {x y : E} (hx : x ∈ D) (hy : y ∈ K) :
    Real.sqrt (diagonal 2 D F x y) ≤ -fderiv ℝ F x y := by
  by_cases hy0 : y = 0
  · subst y
    rw [hF.diagonal_two_eq_hessian hx]
    simp [hessian]
  have hline : ∀ t : ℝ, 0 ≤ t → x+t • y ∈ D := fun t ht =>
    hgeom.ray_mem hx hy ht
  let g := lineJet 1 F x y
  let q := lineJet 2 F x y
  let c := lineJet 3 F x y
  have hg : ∀ t : ℝ, 0 ≤ t → HasDerivAt g (q t) t :=
    fun t ht => hF.lineJet_hasDerivAt (hline t ht) (by norm_num)
  have hq : ∀ t : ℝ, 0 ≤ t → HasDerivAt q (c t) t :=
    fun t ht => hF.lineJet_hasDerivAt (hline t ht) (by norm_num)
  have hpos : ∀ t : ℝ, 0 ≤ t → 0 < q t := by
    intro t ht
    dsimp only [q]
    rw [hF.lineJet_eq_diagonal (hline t ht) (by norm_num)]
    exact hF.hessian_pos _ (hline t ht) y hy0
  have hsc : ∀ t : ℝ, 0 ≤ t → |c t| ≤ 2*q t*Real.sqrt (q t) := by
    intro t ht
    dsimp only [c, q]
    rw [hF.lineJet_eq_diagonal (hline t ht) (by norm_num),
      hF.lineJet_eq_diagonal (hline t ht) (by norm_num)]
    exact hF.self_concordant _ (hline t ht) y
  have hsign : ∀ t : ℝ, 0 ≤ t → g t ≤ 0 := by
    intro t ht
    simpa only [g, lineJet, iteratedFDeriv_one_apply] using
      hF.gradient_nonpos_cone hgeom (hline t ht) hy
  have hh := selfConcordant_recession hg hq hpos hsc hsign
  have hq0 : q 0 = diagonal 2 D F x y := by
    dsimp only [q]
    rw [hF.lineJet_eq_diagonal (hline 0 le_rfl) (by norm_num)]
    simp
  simpa only [hq0, g, lineJet, zero_smul, add_zero, iteratedFDeriv_one_apply] using hh

/-- The same result stated with analytic assumptions alone, with no
boundary set or boundary blowup assumption at all. The empty boundary
below merely packages these data for the preceding proof; the domain D
and closed directions K are unchanged. No primal Dikin theorem is used.
-/
theorem original_cone_gradient_hessian_of_analytic_data {ν : ℝ} {D K : Set E}
    {F : E → ℝ} (hparam : 1 ≤ ν) (hD : IsOpen D)
    (hC : ContDiffOn ℝ 3 F D)
    (hH : ∀ x ∈ D, ∀ h : E, h ≠ 0 → 0 < diagonal 2 D F x h)
    (hsc : ∀ x ∈ D, ∀ h : E, |diagonal 3 D F x h| ≤
      2*diagonal 2 D F x h*Real.sqrt (diagonal 2 D F x h))
    (hhom : ∀ x ∈ D, ∀ t : ℝ, 0 < t → F (t • x) = F x-ν*Real.log t)
    (hgeom : ConeRayGeometry D K) {x y : E} (hx : x ∈ D) (hy : y ∈ K) :
    Real.sqrt (diagonal 2 D F x y) ≤ -fderiv ℝ F x y := by
  have hF : IsLHSCB ν D ∅ F := by
    refine ⟨hparam, hD, hC, hH, hsc, hhom, ?_⟩
    intro z hz
    exact False.elim hz
  exact hF.original_cone_gradient_hessian hgeom hx hy

end D5.S3.Analytic.ConvexBarrier
