/- GID: D5/S3/Observer/Linear/DerivativeLayerNativeGramian
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Algebra.Exponential, mathlib/module/Mathlib.Analysis.InnerProductSpace.Adjoint]
   utility: none
   digest: Construct the actual invertible derivative-layer scaling and its native-time Gramian limit on the observable complement. -/

import D5.S3.Observer.Linear.DerivativeLayerNormalizedObservation
import D5.S3.Observer.Linear.DerivativeLayerGramianPositivity

/-!
The same state and readout operators determine every object in this result.
The diagonal scaling is invertible for every positive time, while its Gramian
converges at a common linear rate for small times. No observability assumption
is imposed on the whole state space. Utility is none: this is a symbolic
filtration, integral change of variables, and analytic operator estimate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.Linear.DerivativeLayerNativeGramian

open ContinuousLinearMap MeasureTheory Finset
open scoped Function InnerProductSpace RealInnerProductSpace

/-- Native-time congruence and a positive polynomial limit for the actual
derivative-layer scaling, including empty layers and zero-dimensional spaces. -/
theorem derivative_layer_native_gramian
    {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    (B : V →ₗ[ℝ] V) (C : V →ₗ[ℝ] W) :
    let n := Module.finrank ℝ V
    let N : ℕ → Submodule ℝ V := fun j =>
      ⨅ k : Fin j, LinearMap.ker (C.comp (B ^ (k : ℕ)))
    let U : Submodule ℝ V := (N n)ᗮ
    let E : Fin n → Submodule ℝ V := fun j => N j ⊓ (N (j + 1))ᗮ
    let b : V →L[ℝ] V := B.toContinuousLinearMap
    let c : V →L[ℝ] W := C.toContinuousLinearMap
    let Q : Fin n → U →L[ℝ] U := fun j =>
      U.orthogonalProjectionOnto.comp ((E j).starProjection.comp U.subtypeL)
    let d : ℝ → U →L[ℝ] U := fun T =>
      ∑ j : Fin n, (Real.sqrt T * T ^ (j : ℕ)) • Q j
    let e : ℝ → U →L[ℝ] U := fun T =>
      ∑ j : Fin n, (Real.sqrt T * T ^ (j : ℕ))⁻¹ • Q j
    let A : ℝ → U →L[ℝ] W := fun t =>
      c.comp ((NormedSpace.exp (t • b)).comp U.subtypeL)
    let G : ℝ → U →L[ℝ] U := fun T =>
      ∫ t in (0 : ℝ)..T, (A t).adjoint.comp (A t)
    let F₀ : ℝ → U →L[ℝ] W := fun s =>
      ∑ j : Fin n, (s ^ (j : ℕ) / (Nat.factorial (j : ℕ) : ℝ)) •
        c.comp ((b ^ (j : ℕ)).comp ((E j).starProjection.comp U.subtypeL))
    let H : U →L[ℝ] U := ∫ s in (0 : ℝ)..1, (F₀ s).adjoint.comp (F₀ s)
    (∀ T : ℝ, 0 < T →
      (d T).comp (e T) = ContinuousLinearMap.id ℝ U ∧
      (e T).comp (d T) = ContinuousLinearMap.id ℝ U ∧
      (e T).comp ((G T).comp (e T)) =
        ∫ s in (0 : ℝ)..1,
          (Real.sqrt T • (A (T * s)).comp (e T)).adjoint.comp
            (Real.sqrt T • (A (T * s)).comp (e T))) ∧
    (∀ x : U, x ≠ 0 → 0 < ⟪x, H x⟫_ℝ) ∧
    ∃ R : ℝ, 0 ≤ R ∧ ∀ T : ℝ, 0 < T → T ≤ 1 → T * ‖b‖ < 1 →
      ‖(e T).comp ((G T).comp (e T)) - H‖ ≤ R * T := by
  classical
  intro n N U E b c Q d e A G F₀ H
  letI : CompleteSpace V := FiniteDimensional.complete ℝ V
  have hNnest {j k : ℕ} (hjk : j ≤ k) : N k ≤ N j := by
    intro z hz
    apply (Submodule.mem_iInf _).mpr
    intro q
    exact ((Submodule.mem_iInf _).mp hz) (⟨q, lt_of_lt_of_le q.isLt hjk⟩ : Fin k)
  have hEsub (j : Fin n) : E j ≤ U :=
    le_trans inf_le_right
      (Submodule.orthogonal_le (hNnest (Nat.succ_le_of_lt j.isLt)))
  have hQval (j : Fin n) (x : U) :
      (Q j x : V) = (E j).starProjection (x : V) := by
    change U.starProjection ((E j).starProjection (x : V)) = _
    exact U.starProjection_eq_self_iff.mpr
      (hEsub j ((E j).starProjection_apply_mem (x : V)))
  have hQadj (j : Fin n) : (Q j).adjoint = Q j := by
    symm
    apply (ContinuousLinearMap.eq_adjoint_iff (Q j) (Q j)).mpr
    intro x y
    change ⟪(Q j x : V), (y : V)⟫_ℝ = ⟪(x : V), (Q j y : V)⟫_ℝ
    rw [hQval, hQval]
    exact (E j).inner_starProjection_left_eq_right (x : V) (y : V)
  have headj (T : ℝ) : (e T).adjoint = e T := by
    change star (∑ j : Fin n, (Real.sqrt T * T ^ (j : ℕ))⁻¹ • Q j) =
      ∑ j : Fin n, (Real.sqrt T * T ^ (j : ℕ))⁻¹ • Q j
    simp only [star_sum, star_smul, star_trivial, star_eq_adjoint, hQadj]
  have hpair : Pairwise ((· ⟂ ·) on E) := by
    intro i j hij
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hlt
    · apply Submodule.isOrtho_iff_le.mpr
      exact (le_trans inf_le_right (Submodule.orthogonal_le
        (hNnest (Nat.succ_le_of_lt hlt)))).trans
          (Submodule.orthogonal_le inf_le_left)
    · apply Submodule.isOrtho_comm.mpr
      apply Submodule.isOrtho_iff_le.mpr
      exact (le_trans inf_le_right (Submodule.orthogonal_le
        (hNnest (Nat.succ_le_of_lt hlt)))).trans
          (Submodule.orthogonal_le inf_le_left)
  have hQQ (i j : Fin n) (x : U) :
      Q i (Q j x) = if i = j then Q j x else 0 := by
    apply Subtype.ext
    rw [hQval, hQval]
    by_cases hij : i = j
    · subst i
      simp only [ite_true, hQval]
      exact (E j).starProjection_eq_self_iff.mpr
        ((E j).starProjection_apply_mem (x : V))
    · simp only [hij, ite_false, Submodule.coe_zero]
      have hh := congrArg (fun L : V →L[ℝ] V => L (x : V))
        ((hpair hij).starProjection_comp_starProjection)
      exact hh
  let L : Fin n → (V →L[ℝ] V) →L[ℝ] (U →L[ℝ] W) := fun j =>
    ((ContinuousLinearMap.compL ℝ U V W) c).comp
      ((ContinuousLinearMap.compL ℝ U V V).flip
        ((E j).starProjection.comp U.subtypeL))
  let F : ℝ → ℝ → U →L[ℝ] W := fun T s =>
    ∑ j : Fin n, (T ^ (j : ℕ))⁻¹ • L j (NormedSpace.exp ((T * s) • b))
  obtain ⟨hresolve, K, hK, herror⟩ :=
    DerivativeLayerNormalizedObservation.derivative_layer_normalized_observation B C
  have hQsum (x : U) : (∑ j : Fin n, Q j x) = x := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum, hQval] using hresolve x
  have hweighted (a : Fin n → ℝ) (i : Fin n) (x : U) :
      Q i (∑ j : Fin n, a j • Q j x) = a i • Q i x := by
    simp only [map_sum, map_smul, hQQ]
    simp
  have hinverse (T : ℝ) (hT : 0 < T) :
      (d T).comp (e T) = ContinuousLinearMap.id ℝ U ∧
      (e T).comp (d T) = ContinuousLinearMap.id ℝ U := by
    have hw (j : Fin n) : Real.sqrt T * T ^ (j : ℕ) ≠ 0 :=
      mul_ne_zero (ne_of_gt (Real.sqrt_pos.2 hT)) (pow_ne_zero _ (ne_of_gt hT))
    constructor
    · ext x
      simp only [d, e, comp_apply, ContinuousLinearMap.sum_apply, smul_apply, id_apply]
      simp only [hweighted, smul_smul]
      apply congrArg (fun y : U => (y : V))
      calc
        (∑ j : Fin n, (Real.sqrt T * T ^ (j : ℕ) *
            (Real.sqrt T * T ^ (j : ℕ))⁻¹) • Q j x) =
            ∑ j : Fin n, Q j x := by
          apply Finset.sum_congr rfl
          intro j _
          rw [mul_inv_cancel₀ (hw j), one_smul]
        _ = x := hQsum x
    · ext x
      simp only [d, e, comp_apply, ContinuousLinearMap.sum_apply, smul_apply, id_apply]
      simp only [hweighted, smul_smul]
      apply congrArg (fun y : U => (y : V))
      calc
        (∑ j : Fin n, ((Real.sqrt T * T ^ (j : ℕ))⁻¹ *
            (Real.sqrt T * T ^ (j : ℕ))) • Q j x) =
            ∑ j : Fin n, Q j x := by
          apply Finset.sum_congr rfl
          intro j _
          rw [inv_mul_cancel₀ (hw j), one_smul]
        _ = x := hQsum x
  have hFnative (T : ℝ) (hT : 0 < T) (s : ℝ) :
      Real.sqrt T • (A (T * s)).comp (e T) = F T s := by
    ext x
    simp only [A, e, F, L, comp_apply, compL_apply, flip_apply,
      ContinuousLinearMap.sum_apply, smul_apply, map_sum, map_smul, hQval]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_smul]
    congr 1
    have hs : Real.sqrt T ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hT)
    have hp : T ^ (j : ℕ) ≠ 0 := pow_ne_zero _ (ne_of_gt hT)
    field_simp [hs, hp]
    simpa only [Submodule.subtypeL_apply] using
      congrArg (fun v : V => c ((NormedSpace.exp ((T * s) • b)) v)) (hQval j x)
  have hexp : Continuous (NormedSpace.exp : (V →L[ℝ] V) → V →L[ℝ] V) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (NormedSpace.exp_analytic (𝕂 := ℝ) x).continuousAt
  have hA : Continuous A := by
    have hexp' : Continuous (fun t : ℝ => NormedSpace.exp (t • b)) :=
      hexp.comp (continuous_id.smul continuous_const)
    have hcomp : Continuous (fun f : V →L[ℝ] V => c.comp (f.comp U.subtypeL)) := by
      fun_prop
    exact hcomp.comp hexp'
  have hAg : Continuous (fun t : ℝ => (A t).adjoint.comp (A t)) :=
    (ContinuousLinearMap.adjoint.continuous.comp hA).clm_comp hA
  have hF₀ : Continuous F₀ := by dsimp [F₀]; fun_prop
  have hF (T : ℝ) : Continuous (F T) := by
    have hexp' : Continuous (fun s : ℝ => NormedSpace.exp ((T * s) • b)) :=
      hexp.comp
        ((continuous_const.mul continuous_id).smul continuous_const)
    dsimp [F]
    exact continuous_finsetSum Finset.univ (fun j _ =>
      (continuous_const : Continuous (fun _ : ℝ => (T ^ (j : ℕ))⁻¹)).smul
        ((L j).continuous.comp hexp'))
  have hFg (T : ℝ) : Continuous (fun s : ℝ => (F T s).adjoint.comp (F T s)) :=
    (ContinuousLinearMap.adjoint.continuous.comp (hF T)).clm_comp (hF T)
  have hF₀g : Continuous (fun s : ℝ => (F₀ s).adjoint.comp (F₀ s)) :=
    (ContinuousLinearMap.adjoint.continuous.comp hF₀).clm_comp hF₀
  have hnative (T : ℝ) (hT : 0 < T) :
      (e T).adjoint.comp ((G T).comp (e T)) =
        ∫ s in (0 : ℝ)..1, (F T s).adjoint.comp (F T s) := by
    let J : (U →L[ℝ] U) →L[ℝ] (U →L[ℝ] U) :=
      ((ContinuousLinearMap.compL ℝ U U U) (e T).adjoint).comp
        ((ContinuousLinearMap.compL ℝ U U U).flip (e T))
    have hJ : (e T).adjoint.comp ((G T).comp (e T)) =
        ∫ t in (0 : ℝ)..T, J ((A t).adjoint.comp (A t)) :=
      (J.intervalIntegral_comp_comm (hAg.intervalIntegrable _ _)).symm
    rw [hJ]
    have hchange := intervalIntegral.smul_integral_comp_mul_left
      (fun t : ℝ => J ((A t).adjoint.comp (A t))) T (a := 0) (b := 1)
    simp only [mul_zero, mul_one] at hchange
    rw [← hchange, ← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro s _
    change T • J ((A (T * s)).adjoint.comp (A (T * s))) =
      (F T s).adjoint.comp (F T s)
    rw [← hFnative T hT s]
    have hs : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT.le
    change T • ((e T).adjoint.comp
      (((A (T * s)).adjoint.comp (A (T * s))).comp (e T))) = _
    simp [map_smulₛₗ, adjoint_comp, smul_comp, comp_smul, smul_smul, comp_assoc, hs]
  have hpositive : ∀ x : U, x ≠ 0 → 0 < ⟪x, H x⟫_ℝ := by
    have hbpow (j : ℕ) : (b ^ j : V →L[ℝ] V) = (B ^ j).toContinuousLinearMap :=
      (map_pow (Module.End.toContinuousLinearMap V) B j).symm
    have hcoeff (j : Fin n) :
        c.comp ((b ^ (j : ℕ)).comp ((E j).starProjection.comp U.subtypeL)) =
          ((C.comp (B ^ (j : ℕ))).comp
            ((E j).starProjection.toLinearMap.comp U.subtype)).toContinuousLinearMap := by
      rw [hbpow]
      rfl
    simpa only [F₀, H, hcoeff] using
      (DerivativeLayerGramianPositivity.derivative_layer_gramian_pos B C)
  obtain ⟨M₀, hM₀⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
      hF₀.continuousOn
  let M := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hMb (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) : ‖F₀ s‖ ≤ M :=
    (hM₀ s hs).trans (le_max_left _ _)
  refine ⟨?_, hpositive, (2 * M + K) * K,
    mul_nonneg (by positivity) hK, ?_⟩
  · intro T hT
    exact ⟨(hinverse T hT).1, (hinverse T hT).2, by
      rw (occs := .pos [1]) [← headj T]
      rw [hnative T hT]
      apply intervalIntegral.integral_congr
      intro s _
      change (F T s).adjoint.comp (F T s) =
        (Real.sqrt T • (A (T * s)).comp (e T)).adjoint.comp
          (Real.sqrt T • (A (T * s)).comp (e T))
      exact congrArg (fun f : U →L[ℝ] W => f.adjoint.comp f)
        (hFnative T hT s).symm⟩
  · intro T hT hT1 hTb
    rw (occs := .pos [1]) [← headj T]
    rw [hnative T hT]
    change ‖(∫ s in (0 : ℝ)..1, (F T s).adjoint.comp (F T s)) -
      (∫ s in (0 : ℝ)..1, (F₀ s).adjoint.comp (F₀ s))‖ ≤ _
    rw [← intervalIntegral.integral_sub ((hFg T).intervalIntegrable _ _)
      (hF₀g.intervalIntegrable _ _)]
    have hbound (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
        ‖(F T s).adjoint.comp (F T s) - (F₀ s).adjoint.comp (F₀ s)‖ ≤
          ((2 * M + K) * K) * T := by
      have herr : ‖F T s - F₀ s‖ ≤ K * T := herror T hT hTb s hs
      have hnorm : ‖F T s‖ ≤ M + K := by
        have hh := norm_le_norm_add_norm_sub' (F T s) (F₀ s)
        have hKT : K * T ≤ K := by nlinarith
        linarith [hMb s hs]
      have hperturb (X Y : U →L[ℝ] W) :
          ‖X.adjoint.comp X - Y.adjoint.comp Y‖ ≤
            (‖X‖ + ‖Y‖) * ‖X - Y‖ := by
        have he : X.adjoint.comp X - Y.adjoint.comp Y =
            X.adjoint.comp (X - Y) + (X.adjoint - Y.adjoint).comp Y := by
          ext x
          simp only [comp_apply, sub_apply, add_apply, map_sub]
          abel
        rw [he]
        calc
          ‖X.adjoint.comp (X - Y) + (X.adjoint - Y.adjoint).comp Y‖ ≤
              ‖X.adjoint.comp (X - Y)‖ + ‖(X.adjoint - Y.adjoint).comp Y‖ :=
                norm_add_le _ _
          _ ≤ ‖X.adjoint‖ * ‖X - Y‖ + ‖X.adjoint - Y.adjoint‖ * ‖Y‖ :=
              add_le_add (opNorm_comp_le _ _) (opNorm_comp_le _ _)
          _ = (‖X‖ + ‖Y‖) * ‖X - Y‖ := by
            rw [← map_sub, adjoint.norm_map, adjoint.norm_map]
            ring
      calc
        ‖(F T s).adjoint.comp (F T s) - (F₀ s).adjoint.comp (F₀ s)‖
            ≤ (‖F T s‖ + ‖F₀ s‖) * ‖F T s - F₀ s‖ :=
          hperturb (F T s) (F₀ s)
        _ ≤ (2 * M + K) * (K * T) :=
          mul_le_mul (by linarith [hMb s hs]) herr (norm_nonneg _)
            (by positivity)
        _ = ((2 * M + K) * K) * T := by ring
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (fun s hs => hbound s (by
        have hs' : s ∈ Set.Ioc (0 : ℝ) 1 := by simpa using hs
        exact ⟨hs'.1.le, hs'.2⟩))
    simpa using hi


end D5.S3.Observer.Linear.DerivativeLayerNativeGramian
