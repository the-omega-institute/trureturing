/- GID: D5/S3/Geometry/C1LocalFiber
   generality: G
   mirror-B: D5/B/S3/Geometry/C1LocalFiber
   mirror-E: none(waiver:source-owner-registration-pending)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff]
   utility: none
   digest: Actual local fibers of real C1 maps at a point of maximal derivative rank. -/

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.Complemented
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic

/-
Portions adapted from LeanPool:
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license (https://www.apache.org/licenses/LICENSE-2.0).
-/

/-! The vertical range argument and the use of complementary projections adapt
BochaoKong's Apache-2.0 LeanPool complex constant-rank proof
(commit 2b1ec889365345f19a45fa94b6457a4d92c96295) to real C1 maps.
Only a source fiber is constructed; no holomorphic or constant-rank theorem is imported. -/

noncomputable section

open Set Filter Metric
open scoped Topology

namespace D5.S3.Geometry.C1LocalFiber

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- A surjective observed coordinate and its rank budget force every vertical
direction to vanish. Used both for C1 fibers and finite matrix completion. -/
theorem linear_vertical_eq_zero
    {𝕜 R K G : Type*} [DivisionRing 𝕜]
    [AddCommGroup R] [Module 𝕜 R] [FiniteDimensional 𝕜 R]
    [AddCommGroup K] [Module 𝕜 K] [FiniteDimensional 𝕜 K]
    [AddCommGroup G] [Module 𝕜 G] [FiniteDimensional 𝕜 G]
    (T : R × K →ₗ[𝕜] G) (p : G →ₗ[𝕜] R)
    (hp : p.comp T = LinearMap.fst 𝕜 R K)
    (hr : Module.finrank 𝕜 (LinearMap.range T) ≤ Module.finrank 𝕜 R)
    (z : K) : T (0, z) = 0 := by
  let P : LinearMap.range T →ₗ[𝕜] R := p.domRestrict (LinearMap.range T)
  have hP : Function.Surjective P := by
    intro y
    refine ⟨⟨T (y, 0), ⟨(y, 0), rfl⟩⟩, ?_⟩
    exact DFunLike.congr_fun hp (y, 0)
  have hdim : Module.finrank 𝕜 (LinearMap.range T) = Module.finrank 𝕜 R :=
    le_antisymm hr (LinearMap.finrank_le_finrank_of_surjective hP)
  have hPi : Function.Injective P :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hP
  have hz : (⟨T (0, z), ⟨(0, z), rfl⟩⟩ : LinearMap.range T) = 0 := by
    apply hPi
    change p (T (0, z)) = p 0
    rw [map_zero]
    exact DFunLike.congr_fun hp (0, z)
  exact congrArg Subtype.val hz

private lemma slice_constant
    {R K : Type*}
    [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R]
    [NormedAddCommGroup K] [NormedSpace ℝ K] [FiniteDimensional ℝ K]
    {P : R × K → F} (p : F →L[ℝ] R)
    (hP : ContDiffAt ℝ 1 P 0)
    (hproj : (fun w => p (P w)) =ᶠ[𝓝 0] fun w => w.1)
    (hrank : ∀ᶠ w in 𝓝 0,
      Module.finrank ℝ (LinearMap.range (fderiv ℝ P w).toLinearMap) ≤
        Module.finrank ℝ R) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ ball (0 : K) ε, P (0, z) = P 0 := by
  have hloc := eventually_eventuallyEq_nhds.mpr hproj
  have hgood : ∀ᶠ w in 𝓝 0,
      DifferentiableAt ℝ P w ∧ ∀ z : K, fderiv ℝ P w (0, z) = 0 := by
    filter_upwards [hP.eventually (by norm_num), hloc, hrank] with w hw hl hr
    have hd := hw.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
    have hpd := p.hasFDerivAt.comp w hd.hasFDerivAt
    have hfst : p.comp (fderiv ℝ P w) = ContinuousLinearMap.fst ℝ R K :=
      (hpd.congr_of_eventuallyEq hl.symm).unique
        (ContinuousLinearMap.fst ℝ R K).hasFDerivAt
    exact ⟨hd, linear_vertical_eq_zero (fderiv ℝ P w).toLinearMap p.toLinearMap
      (congrArg ContinuousLinearMap.toLinearMap hfst) hr⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hgood
  refine ⟨ε, hε, ?_⟩
  let Q : K → F := fun z => P (0, z)
  have hQ (z : K) (hz : z ∈ ball 0 ε) : HasFDerivAt Q (0 : K →L[ℝ] F) z := by
    have hw : (0, z) ∈ ball (0 : R × K) ε := by
      simpa only [Metric.mem_ball, Prod.dist_eq, Prod.fst_zero, Prod.snd_zero,
        dist_self, max_lt_iff, and_iff_right hε] using hz
    let i : K →L[ℝ] R × K := ContinuousLinearMap.inr ℝ R K
    have hi : HasFDerivAt (fun z : K => (0, z)) i z := i.hasFDerivAt
    have hd := (hball hw).1.hasFDerivAt.comp z hi
    have he : (fderiv ℝ P (0, z)).comp i = 0 := by
      ext v
      exact (hball hw).2 v
    simpa only [Q, he, Function.comp_def] using hd
  intro z hz
  apply (convex_ball (0 : K) ε).is_const_of_fderivWithin_eq_zero
    (fun z hz => (hQ z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hQ z hz).hasFDerivWithinAt.fderivWithin
      (isOpen_ball.uniqueDiffWithinAt hz)) hz (mem_ball_self hε)

/-- At a point whose derivative rank bounds all ranks on the open domain,
the level set contains a C1 ball with an explicit continuous linear left inverse.
The dimension identity gives the full kernel dimension, including rank zero. -/
theorem exists_local_fiber {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ 1 f U) {a : E} (ha : a ∈ U)
    (hmax : ∀ x ∈ U,
      Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) ≤
        Module.finrank ℝ (LinearMap.range (fderiv ℝ f a).toLinearMap)) :
    ∃ (K : Submodule ℝ E) (q : E →L[ℝ] K) (k : K → E) (ε : ℝ),
      0 < ε ∧
      Module.finrank ℝ K +
        Module.finrank ℝ (LinearMap.range (fderiv ℝ f a).toLinearMap) =
          Module.finrank ℝ E ∧
      k 0 = a ∧ ContDiffOn ℝ 1 k (ball 0 ε) ∧
      ∀ z ∈ ball 0 ε, k z ∈ U ∧ f (k z) = f a ∧ q (k z - a) = z := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  let A := fderiv ℝ f a
  let R := LinearMap.range A.toLinearMap
  obtain ⟨C, hRC⟩ := Submodule.exists_isCompl R
  have hRCt : Submodule.IsTopCompl R C :=
    Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional hRC
      R.closed_of_finiteDimensional
  let p : F →L[ℝ] R := R.projectionOntoL C hRCt
  let G : E →L[ℝ] R := p.comp A
  have hG : Function.Surjective G := by
    intro y
    obtain ⟨x, hx⟩ := y.property
    change A x = (y : F) at hx
    refine ⟨x, ?_⟩
    change p (A x) = y
    rw [hx]
    exact Submodule.projectionOntoL_apply_left hRCt y
  let K := LinearMap.ker G.toLinearMap
  obtain ⟨L, hKL⟩ := Submodule.exists_isCompl K
  have hKLt : Submodule.IsTopCompl K L :=
    Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional hKL
      K.closed_of_finiteDimensional
  let q : E →L[ℝ] K := K.projectionOntoL L hKLt
  have hker : IsCompl (LinearMap.ker G.toLinearMap)
      (LinearMap.ker q.toLinearMap) := by
    simpa [K, q] using hKL
  let e : E ≃L[ℝ] R × K :=
    (LinearMap.equivProdOfSurjectiveOfIsCompl G.toLinearMap q.toLinearMap
      (LinearMap.range_eq_top.mpr hG) (Submodule.range_projectionOntoL hKLt)
      hker).toContinuousLinearEquiv
  let H : E → R × K := fun x => (p (f x - f a), q (x - a))
  have hfa : ContDiffAt ℝ 1 f a := hf.contDiffAt (hU.mem_nhds ha)
  have hH : ContDiffAt ℝ 1 H a :=
    (p.contDiff.contDiffAt.comp a (hfa.sub contDiffAt_const)).prodMk
      (q.contDiff.contDiffAt.comp a (contDiffAt_id.sub contDiffAt_const))
  have hHd : HasFDerivAt H (e : E →L[ℝ] R × K) a := by
    have h₁ := p.hasFDerivAt.comp a (hfa.differentiableAt_one.hasFDerivAt.sub_const (f a))
    have h₂ := q.hasFDerivAt.comp a ((hasFDerivAt_id a).sub_const a)
    change HasFDerivAt H (G.prod q) a
    simpa only [H, G, A, Function.comp_def, id_eq, ContinuousLinearMap.comp_id]
      using h₁.prodMk h₂
  have hH0 : H a = 0 := by simp [H]
  let j : R × K → E := hH.localInverse hHd (by norm_num)
  have hj0 : j 0 = a := by
    simpa only [hH0] using hH.localInverse_apply_image hHd (by norm_num)
  have hj : ContDiffAt ℝ 1 j 0 := by
    simpa only [hH0] using hH.to_localInverse hHd (by norm_num)
  have hright : ∀ᶠ w in 𝓝 (0 : R × K), H (j w) = w := by
    simpa only [j, ContDiffAt.localInverse, hH0] using
      (hH.hasStrictFDerivAt' hHd (by norm_num)).eventually_right_inverse
  have hjU : ∀ᶠ w in 𝓝 (0 : R × K), j w ∈ U := by
    exact hj.continuousAt (by simpa only [hj0] using hU.mem_nhds ha)
  let P : R × K → F := fun w => f (j w) - f a
  have hP : ContDiffAt ℝ 1 P 0 := by
    have hfa' : ContDiffAt ℝ 1 f (j 0) := by simpa only [hj0] using hfa
    exact (hfa'.comp 0 hj).sub contDiffAt_const
  have hproj : (fun w => p (P w)) =ᶠ[𝓝 0] fun w => w.1 := by
    filter_upwards [hright] with w hw
    exact congrArg Prod.fst hw
  have hrank : ∀ᶠ w in 𝓝 (0 : R × K),
      Module.finrank ℝ (LinearMap.range (fderiv ℝ P w).toLinearMap) ≤
        Module.finrank ℝ R := by
    filter_upwards [hjU, hj.eventually (by norm_num)] with w hw hdj
    have hdf := (hf.contDiffAt (hU.mem_nhds hw)).differentiableAt_one
    have hd : HasFDerivAt P
        ((fderiv ℝ f (j w)).comp (fderiv ℝ j w)) w :=
      (hdf.hasFDerivAt.comp w hdj.differentiableAt_one.hasFDerivAt).sub_const (f a)
    rw [hd.fderiv]
    exact (Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)).trans
      (hmax (j w) hw)
  obtain ⟨ε₁, hε₁, hslice⟩ := slice_constant p hP hproj hrank
  have hgood : ∀ᶠ z in 𝓝 (0 : K),
      j (0, z) ∈ U ∧ H (j (0, z)) = (0, z) ∧ ContDiffAt ℝ 1 j (0, z) := by
    have ht : Tendsto (fun z : K => ((0 : R), z)) (𝓝 0) (𝓝 0) := by
      exact tendsto_const_nhds.prodMk_nhds tendsto_id
    exact ht (hjU.and (hright.and (hj.eventually (by norm_num))))
  obtain ⟨ε₂, hε₂, hball⟩ := Metric.mem_nhds_iff.mp hgood
  let ε := min ε₁ ε₂
  have he₁ : ball (0 : K) ε ⊆ ball 0 ε₁ := ball_subset_ball (min_le_left _ _)
  have he₂ : ball (0 : K) ε ⊆ ball 0 ε₂ := ball_subset_ball (min_le_right _ _)
  refine ⟨K, q, fun z => j (0, z), ε, lt_min hε₁ hε₂, ?_, hj0, ?_, ?_⟩
  · have hd := LinearMap.finrank_range_add_finrank_ker G.toLinearMap
    rw [LinearMap.range_eq_top.mpr hG, finrank_top] at hd
    change Module.finrank ℝ R + Module.finrank ℝ K = Module.finrank ℝ E at hd
    change Module.finrank ℝ K + Module.finrank ℝ R = Module.finrank ℝ E
    omega
  · intro z hz
    exact ((hball (he₂ hz)).2.2.comp z
      (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt
  · intro z hz
    refine ⟨(hball (he₂ hz)).1, ?_, ?_⟩
    · have hs := hslice z (he₁ hz)
      change f (j (0, z)) - f a = f (j 0) - f a at hs
      rw [hj0] at hs
      exact sub_left_inj.mp hs
    · exact congrArg Prod.snd (hball (he₂ hz)).2.1

/-- A real C1 map to a smaller finite-dimensional space has an actual
collision in every nonempty open domain. -/
theorem exists_collision {U : Set E} (hU : IsOpen U) (hne : U.Nonempty)
    {f : E → F} (hf : ContDiffOn ℝ 1 f U)
    (hdim : Module.finrank ℝ F < Module.finrank ℝ E) :
    ∃ x ∈ U, ∃ y ∈ U, x ≠ y ∧ f x = f y := by
  classical
  let rank (x : E) := Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap)
  have hbound (x : E) : rank x ≤ Module.finrank ℝ F := Submodule.finrank_le _
  let P (r : ℕ) := ∃ x ∈ U, rank x = r
  obtain ⟨b, hb⟩ := hne
  obtain ⟨a, ha, har⟩ := Nat.findGreatest_spec (P := P) (hbound b) ⟨b, hb, rfl⟩
  have hmax (x : E) (hx : x ∈ U) : rank x ≤ rank a := by
    rw [har]
    exact Nat.le_findGreatest (hbound x) ⟨x, hx, rfl⟩
  obtain ⟨K, q, k, ε, hε, hK, hk0, _, hk⟩ := exists_local_fiber hU hf ha hmax
  have hKpos : 0 < Module.finrank ℝ K := by
    have := hbound a
    change Module.finrank ℝ K + rank a = Module.finrank ℝ E at hK
    omega
  letI : Nontrivial K := Module.nontrivial_of_finrank_pos hKpos
  obtain ⟨z, hzn⟩ := exists_norm_eq K (le_of_lt (half_pos hε))
  have hz : z ∈ ball (0 : K) ε := by simpa [Metric.mem_ball, hzn] using half_lt_self hε
  have hzne : z ≠ 0 := norm_pos_iff.mp (by rw [hzn]; exact half_pos hε)
  refine ⟨k z, (hk z hz).1, a, ha, ?_, (hk z hz).2.1⟩
  intro he
  have heq := (hk z hz).2.2
  rw [he, sub_self, map_zero] at heq
  exact hzne heq.symm

/-- In particular no such map is injective on a nonempty open domain. -/
theorem not_injOn {U : Set E} (hU : IsOpen U) (hne : U.Nonempty)
    {f : E → F} (hf : ContDiffOn ℝ 1 f U)
    (hdim : Module.finrank ℝ F < Module.finrank ℝ E) : ¬ Set.InjOn f U := by
  obtain ⟨x, hx, y, hy, hne, heq⟩ := exists_collision hU hne hf hdim
  exact fun hi => hne (hi hx hy heq)

end D5.S3.Geometry.C1LocalFiber
