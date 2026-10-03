/- GID: D5/S3/Observer/Linear/ObservableTrajectoryCoordinates
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/ObservableTrajectoryCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Observable exponential trajectories admit normalized image coordinates with the exact integrated Gramian. -/

import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Observer.Linear.ObservableTrajectoryCoordinates
open ContinuousLinearMap MeasureTheory Set Filter Module WithLp
open scoped InnerProductSpace Matrix.Norms.L2Operator Topology
theorem observable_trajectory_coordinates (d p : ℕ)
    (B : (EuclideanSpace ℝ (Fin d)) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (C : (EuclideanSpace ℝ (Fin d)) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (T : ℝ) (hT : 0 < T)
    (hobs : ∀ x, (∀ k : Fin d, C ((B ^ (k : ℕ)) x) = 0) → x = 0) :
    ∃ F : (EuclideanSpace ℝ (Fin d)) →L[ℝ] Lp (EuclideanSpace ℝ (Fin p)) 2 (volume.restrict (Ioc 0 T)),
      (∀ x, (fun t => F x t) =ᵐ[volume.restrict (Ioc 0 T)]
        fun t => C ((NormedSpace.exp (t • B)) x)) ∧
      Function.Injective F ∧ finrank ℝ F.range = d ∧
      ∃ basis : OrthonormalBasis (Fin d) ℝ F.range,
      ∃ U : Lp (EuclideanSpace ℝ (Fin p)) 2 (volume.restrict (Ioc 0 T)) →L[ℝ] EuclideanSpace ℝ (Fin d),
      ∃ M : Matrix (Fin d) (Fin d) ℝ,
        U = basis.repr.toContinuousLinearEquiv.toContinuousLinearMap.comp
          F.range.orthogonalProjectionOnto ∧
        (∀ g, ‖U g‖ ≤ ‖g‖) ∧
        (∀ g i, U g i = ∫ t in (0:ℝ)..T,
          inner ℝ ((basis i : Lp (EuclideanSpace ℝ (Fin p)) 2 (volume.restrict (Ioc 0 T))) t) (g t)) ∧
        (∀ (g : Lp (EuclideanSpace ℝ (Fin p)) 2 (volume.restrict (Ioc 0 T))) i, IntervalIntegrable (fun t =>
          inner ℝ ((basis i : Lp (EuclideanSpace ℝ (Fin p)) 2 (volume.restrict (Ioc 0 T))) t) (g t)) volume 0 T) ∧
        U.adjoint.comp U = F.range.starProjection ∧
        M.toEuclideanLin.toContinuousLinearMap = U.comp F ∧
        (U.comp F).adjoint.comp (U.comp F) = F.adjoint.comp F ∧
        F.adjoint.comp F = ∫ t in (0:ℝ)..T,
          (C.comp (NormedSpace.exp (t • B))).adjoint.comp (C.comp (NormedSpace.exp (t • B))) ∧
        (let b := Matrix.toEuclideanLin.symm B.toLinearMap
         let c := Matrix.toEuclideanLin.symm C.toLinearMap
         M.transpose*M = ∫ t in (0:ℝ)..T,
           NormedSpace.exp (t • b.transpose)*c.transpose*c*NormedSpace.exp (t • b)) := by
  classical
  let action {d a : Type} [Fintype d] [DecidableEq d] [Fintype a] [DecidableEq a]
      (M : Matrix a d ℝ) : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ a :=
    M.toEuclideanLin.toContinuousLinearMap
  have action_apply {d a : Type} [Fintype d] [DecidableEq d] [Fintype a] [DecidableEq a] (M : Matrix a d ℝ) (x : EuclideanSpace ℝ d) :
      action M x = toLp 2 (M.mulVec (ofLp x)) := rfl
  have action_comp {d a b : Type} [Fintype d] [DecidableEq d] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (M : Matrix a b ℝ) (N : Matrix b d ℝ) :
      (action M).comp (action N) = action (M * N) := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, action_apply, ofLp_toLp,
      Matrix.mulVec_mulVec]
  have inner_action {d a : Type} [Fintype d] [DecidableEq d] [Fintype a] [DecidableEq a] (M : Matrix a d ℝ) (x : EuclideanSpace ℝ d) (y : EuclideanSpace ℝ a) :
      ⟪action M x, y⟫_ℝ = ⟪x, action M.transpose y⟫_ℝ := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, action_apply,
      ofLp_toLp, star_trivial, dotProduct_comm] using
      (Matrix.dotProduct_transpose_mulVec M (ofLp x) (ofLp y)).symm
  have action_adjoint {d a : Type} [Fintype d] [DecidableEq d] [Fintype a] [DecidableEq a] (M : Matrix a d ℝ) :
      (action M).adjoint = action M.transpose := by
    apply ContinuousLinearMap.ext
    intro y
    apply ext_inner_left ℝ
    intro x
    rw [ContinuousLinearMap.adjoint_inner_right, inner_action]
  let E := EuclideanSpace Real (Fin d)
  let W := EuclideanSpace Real (Fin p)
  let H := Lp W 2 (volume.restrict (Ioc 0 T))
  let f : Real -> E →L[ℝ] W := fun t => C.comp (NormedSpace.exp (t • B))
  have hexp : Continuous (NormedSpace.exp : (E →L[ℝ] E) -> E →L[ℝ] E) := by
    apply continuous_iff_continuousAt.mpr
    intro A
    exact (NormedSpace.exp_analytic (𝕂 := Real) A).continuousAt
  have hf : Continuous f := by
    exact continuous_const.clm_comp (hexp.comp (continuous_id.smul continuous_const))
  have hfx (x : E) : Continuous (fun t => f t x) :=
    (ContinuousLinearMap.apply Real W x).continuous.comp hf
  have hmem (x : E) : MemLp (fun t : Real => f t x) 2
      (volume.restrict (Ioc 0 T)) := by
    obtain ⟨N, hN⟩ := (isCompact_Icc : IsCompact (Icc (0 : Real) T)).exists_bound_of_continuousOn (hfx x).continuousOn
    apply MemLp.of_bound (hfx x).aestronglyMeasurable N
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hN s (Ioc_subset_Icc_self hs)
  let flin : E →ₗ[Real] H := {
    toFun := fun x => (hmem x).toLp (fun t => f t x)
    map_add' := by
      intro x y
      calc
        (hmem (x + y)).toLp _ = ((hmem x).add (hmem y)).toLp _ := by
          apply MemLp.toLp_congr
          filter_upwards with t
          simp
        _ = (hmem x).toLp _ + (hmem y).toLp _ := MemLp.toLp_add _ _
    map_smul' := by
      intro a x
      calc
        (hmem (a • x)).toLp _ = ((hmem x).const_smul a).toLp _ := by
          apply MemLp.toLp_congr
          filter_upwards with t
          simp
        _ = a • (hmem x).toLp _ := MemLp.toLp_const_smul a _ }
  let F : E →L[Real] H := ⟨flin, flin.continuous_of_finiteDimensional⟩
  have hrep (x : E) :
      (fun t => F x t) =ᵐ[volume.restrict (Ioc 0 T)] fun t => f t x :=
    MemLp.coeFn_toLp (hmem x)
  have hinj : Function.Injective F := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm
    · intro x hx
      have hz : F x = 0 := hx
      have hae : (fun t => f t x) =ᵐ[volume.restrict (Ioc 0 T)] 0 := by
        have hr := hrep x
        rw [hz] at hr
        exact hr.symm.trans (Lp.coeFn_zero W 2 (volume.restrict (Ioc 0 T)))
      have hon : EqOn (fun t => f t x) 0 (Ioc (0 : Real) T) :=
        MeasureTheory.Measure.eqOn_Ioc_of_ae_eq (μ := volume) hae
          (hfx x).continuousOn continuous_zero.continuousOn
      let u : Real →L[ℝ] (E →L[ℝ] E) := toSpanSingleton Real B
      let a : (E →L[ℝ] E) →L[ℝ] W := C.comp (ContinuousLinearMap.apply Real E x)
      have hana : AnalyticOnNhd Real (fun t => f t x) univ := by
        intro t _
        exact (a.analyticAt _).comp
          ((NormedSpace.exp_analytic (𝕂 := Real) (u t)).comp (u.analyticAt t))
      have hevent : (fun t => f t x) =ᶠ[𝓝 (T / 2)] 0 := by
        filter_upwards [Ioo_mem_nhds (show 0 < T / 2 by linarith) (show T / 2 < T by linarith)] with t ht
        exact hon ⟨ht.1, ht.2.le⟩
      have hall := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (mem_univ (T / 2)) hevent
      have hseries : HasFPowerSeriesAt (fun t => f t x)
          (a.compFormalMultilinearSeries
            ((NormedSpace.expSeries Real (E →L[ℝ] E)).compContinuousLinearMap u)) 0 := by
        have he : HasFPowerSeriesAt NormedSpace.exp
            (NormedSpace.expSeries Real (E →L[ℝ] E)) (u 0) := by
          simpa using (NormedSpace.exp_hasFPowerSeriesAt_zero (𝕂 := Real) (𝔸 := E →L[ℝ] E))
        obtain ⟨r, hr⟩ := he.compContinuousLinearMap (u := u)
        exact (a.comp_hasFPowerSeriesOnBall hr).hasFPowerSeriesAt
      have hs0 := hseries.eq_zero_of_eventually (Filter.Eventually.of_forall (fun t => hall (mem_univ t)))
      have hcoeff (k : Fin d) : C ((B ^ (k : Nat)) x) = 0 := by
        have hk := congrArg (fun q => q (k : Nat) (fun _ => (1 : Real))) hs0
        simp only [ContinuousLinearMap.compFormalMultilinearSeries_apply',
          FormalMultilinearSeries.compContinuousLinearMap_apply,
          Function.comp_def, u, toSpanSingleton_apply, one_smul,
          NormedSpace.expSeries_apply_eq, a, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply, map_smul,
          Pi.zero_apply, ContinuousMultilinearMap.zero_apply] at hk
        exact (smul_eq_zero.mp hk).resolve_left (inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (k : Nat)))
      have hx0 := hobs x hcoeff
      exact hx0
    · exact bot_le
  have hrank : finrank Real F.range = d := by
    simpa [E] using (LinearMap.finrank_range_of_inj hinj)
  letI : FiniteDimensional Real F.range := inferInstance
  let basis : OrthonormalBasis (Fin d) Real F.range :=
    (stdOrthonormalBasis Real F.range).reindex (finCongr hrank)
  let L := basis.repr.toContinuousLinearEquiv.toContinuousLinearMap.comp F.rangeRestrict
  let M : Matrix (Fin d) (Fin d) Real := Matrix.toEuclideanLin.symm L.toLinearMap
  have hM : M.toEuclideanLin.toContinuousLinearMap = L := by
    apply ContinuousLinearMap.ext
    intro x
    exact congrArg (fun A : E →ₗ[Real] E => A x)
      (LinearEquiv.apply_symm_apply Matrix.toEuclideanLin L.toLinearMap)
  have hGram : L.adjoint.comp L = F.adjoint.comp F := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left Real
    intro y
    simp only [ContinuousLinearMap.comp_apply]
    rw [L.adjoint_inner_right, F.adjoint_inner_right]
    exact basis.repr.inner_map_map (F.rangeRestrict y) (F.rangeRestrict x)
  have hphysical : F.adjoint.comp F =
      integral (volume.restrict (Ioc 0 T))
        (fun t : Real => (f t).adjoint.comp (f t)) := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left Real
    intro y
    rw [ContinuousLinearMap.comp_apply, F.adjoint_inner_right]
    rw [MeasureTheory.L2.inner_def]
    have hinner : integral (volume.restrict (Ioc 0 T))
        (fun t => inner Real (F y t) (F x t)) =
      integral (volume.restrict (Ioc 0 T))
        (fun t => inner Real (f t y) (f t x)) := by
      apply integral_congr_ae
      filter_upwards [hrep y, hrep x] with t hy hx
      rw [hy, hx]
    rw [hinner]
    have hg : Continuous (fun t => (f t).adjoint.comp (f t)) :=
      (ContinuousLinearMap.adjoint.continuous.comp hf).clm_comp hf
    have hgint := hg.intervalIntegrable (μ := volume) (0 : Real) T
    simp only [<- intervalIntegral.integral_of_le hT.le]
    rw [ContinuousLinearMap.intervalIntegral_apply hgint]
    have hv : IntervalIntegrable
        (fun t => ((f t).adjoint.comp (f t)) x) volume 0 T :=
      ((ContinuousLinearMap.apply Real E x).continuous.comp hg).intervalIntegrable
        (μ := volume) 0 T
    have hi := (innerSL Real y).intervalIntegral_comp_comm hv
    calc
      _ = ∫ t in (0 : Real)..T, inner Real y (((f t).adjoint.comp (f t)) x) := by
        apply intervalIntegral.integral_congr
        intro t _
        change inner Real (f t y) (f t x) = inner Real y ((f t).adjoint (f t x))
        exact ((f t).adjoint_inner_right y (f t x)).symm
      _ = _ := by simpa using hi
  let b := Matrix.toEuclideanLin.symm B.toLinearMap
  let c := Matrix.toEuclideanLin.symm C.toLinearMap
  let e : Matrix (Fin d) (Fin d) Real ≃L[Real] (E →L[Real] E) :=
    (Matrix.toEuclideanCLM (𝕜 := Real) (n := Fin d)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv
  letI : NormedAlgebra Rat (Matrix (Fin d) (Fin d) Real) :=
    NormedAlgebra.restrictScalars Rat Real _
  letI : NormedAlgebra Rat (E →L[Real] E) :=
    NormedAlgebra.restrictScalars Rat Real _
  have hact (A : Matrix (Fin d) (Fin d) Real) : action A = e A := rfl
  have hb : action b = B := by
    apply ContinuousLinearMap.ext
    intro x
    exact congrArg (fun A : E →ₗ[Real] E => A x)
      (LinearEquiv.apply_symm_apply Matrix.toEuclideanLin B.toLinearMap)
  have hc : action c = C := by
    apply ContinuousLinearMap.ext
    intro x
    exact congrArg (fun A : E →ₗ[Real] W => A x)
      (LinearEquiv.apply_symm_apply Matrix.toEuclideanLin C.toLinearMap)
  have hecont : Continuous (Matrix.toEuclideanCLM (𝕜 := Real) (n := Fin d)) :=
    (Matrix.toEuclideanCLM (𝕜 := Real) (n := Fin d)).toAlgEquiv.toLinearEquiv.continuous_of_finiteDimensional
  have hmap (A : Matrix (Fin d) (Fin d) Real) :
      (Matrix.toEuclideanCLM (𝕜 := Real) (n := Fin d)) A = action A := by
    apply ContinuousLinearMap.ext
    intro x
    rfl
  have hexpact (t : Real) : action (NormedSpace.exp (t • b)) =
      NormedSpace.exp (t • B) := by
    have he := NormedSpace.map_exp
      (Matrix.toEuclideanCLM (𝕜 := Real) (n := Fin d)) hecont (t • b)
    have hs : action (t • b) = t • action b := by
      apply ContinuousLinearMap.ext
      intro x
      simp [action_apply, Matrix.smul_mulVec]
    simpa only [hmap, hs, hb] using he
  let g : Real → Matrix (Fin d) (Fin d) Real := fun t =>
    NormedSpace.exp (t • b.transpose) * c.transpose * c * NormedSpace.exp (t • b)
  have htranspose (t : Real) : NormedSpace.exp (t • b.transpose) =
      (NormedSpace.exp (t • b)).transpose := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_smul] using (NormedSpace.star_exp (t • b)).symm
  have heg (t : Real) : e (g t) = (f t).adjoint.comp (f t) := by
    rw [← hact]
    simp only [g, htranspose, ← action_comp, ← action_adjoint, hexpact, hc,
      ContinuousLinearMap.comp_assoc, ContinuousLinearMap.adjoint_comp, f]
  have hmatrix : M.transpose * M = integral (volume.restrict (Ioc 0 T)) g := by
    apply e.injective
    change action M = L at hM
    rw [← hact, ← action_comp, ← action_adjoint, hM, hGram, hphysical]
    rw [← e.integral_comp_comm]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun t => (heg t).symm))
  let U : H →L[ℝ] E := basis.repr.toContinuousLinearEquiv.toContinuousLinearMap.comp
    F.range.orthogonalProjectionOnto
  have hUL : U.comp F = L := by
    apply ContinuousLinearMap.ext
    intro x
    change basis.repr (F.range.orthogonalProjectionOnto (F x)) = basis.repr (F.rangeRestrict x)
    apply congrArg basis.repr
    apply Subtype.ext
    change F.range.starProjection (F x) = F x
    exact F.range.starProjection_eq_self_iff.mpr ⟨x,rfl⟩
  have hUnorm (g : H) : ‖U g‖ ≤ ‖g‖ := by
    change ‖basis.repr (F.range.orthogonalProjectionOnto g)‖ ≤ ‖g‖
    rw [basis.repr.norm_map]
    exact F.range.norm_orthogonalProjectionOnto_apply_le g
  have hUcoord (g : H) (i : Fin d) : U g i = ∫ t in (0:ℝ)..T,
      inner ℝ ((basis i : H) t) (g t) := by
    change basis.repr (F.range.orthogonalProjectionOnto g) i = _
    rw [OrthonormalBasis.repr_apply_apply,
      F.range.inner_orthogonalProjectionOnto_eq_of_mem_left]
    rw [L2.inner_def, intervalIntegral.integral_of_le hT.le]
  have hUint (g : H) (i : Fin d) : IntervalIntegrable
      (fun t => inner ℝ ((basis i : H) t) (g t)) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr (L2.integrable_inner (basis i : H) g)
  have hUproj : U.adjoint.comp U = F.range.starProjection := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℝ
    intro y
    simp only [ContinuousLinearMap.comp_apply]
    rw [U.adjoint_inner_right]
    change inner ℝ (basis.repr (F.range.orthogonalProjectionOnto y))
      (basis.repr (F.range.orthogonalProjectionOnto x)) = inner ℝ y (F.range.starProjection x)
    rw [basis.repr.inner_map_map,
      F.range.inner_orthogonalProjectionOnto_eq_of_mem_right]
    rfl
  have hphysical' : F.adjoint.comp F = ∫ t in (0:ℝ)..T,
      (C.comp (NormedSpace.exp (t • B))).adjoint.comp (C.comp (NormedSpace.exp (t • B))) := by
    rw [intervalIntegral.integral_of_le hT.le]
    exact hphysical
  have hmatrix' : M.transpose*M = ∫ t in (0:ℝ)..T,
      NormedSpace.exp (t • b.transpose)*c.transpose*c*NormedSpace.exp (t • b) := by
    rw [intervalIntegral.integral_of_le hT.le]
    exact hmatrix
  refine ⟨F,hrep,hinj,hrank,basis,U,M,rfl,hUnorm,hUcoord,hUint,hUproj,?_,?_,hphysical',hmatrix'⟩
  · rw [hUL]
    exact hM
  · rw [hUL]
    exact hGram

end D5.S3.Observer.Linear.ObservableTrajectoryCoordinates
