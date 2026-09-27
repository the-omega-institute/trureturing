/- GID: D5/S3/Quantum/Measurement/FiniteDetectionSurvivalLimit
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/FiniteDetectionSurvivalLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Survival effects converge to the dark-space projection. -/

import D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit

open Filter Matrix Metric
open scoped ComplexOrder Matrix.Norms.L2Operator MatrixOrder Topology

/-- The vectors whose click amplitudes vanish after every number of no-click steps. -/
def darkSpace {d : ℕ} {ι : Type*}
    (Q : Matrix (Fin d) (Fin d) ℂ) (L : ι → Matrix (Fin d) (Fin d) ℂ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin d)) :=
  ⨅ n : ℕ, ⨅ x : ι, LinearMap.ker (Matrix.toEuclideanLin (L x * Q ^ n))

/-- The matrix of the orthogonal projection onto the dark space. -/
def darkProjection {d : ℕ} {ι : Type*}
    (Q : Matrix (Fin d) (Fin d) ℂ) (L : ι → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm (darkSpace Q L).starProjection

set_option maxHeartbeats 1000000 in
-- The compact-sphere norm argument and its matrix/CLM transports require extra elaboration work.
/-- **Single-Kraus survival limit.** For a complete finite measurement with no-click operator
`Q`, the survival effects `(Qᴴ)ᴺ Qᴺ` converge to the orthogonal projection onto the vectors never
detected by any click operator. Consequently every matrix-weighted trace has the corresponding
projected limit. The zero-dimensional case is included. -/
theorem finite_detection_survival_limit {d : ℕ} {ι : Type*} [Fintype ι]
    (Q : Matrix (Fin d) (Fin d) ℂ) (L : ι → Matrix (Fin d) (Fin d) ℂ)
    (hcomp : Qᴴ * Q + ∑ x, (L x)ᴴ * L x = 1) :
    Tendsto (fun N => (Qᴴ) ^ N * Q ^ N) atTop (𝓝 (darkProjection Q L)) ∧
      ∀ ρ : Matrix (Fin d) (Fin d) ℂ,
        Tendsto (fun N => (ρ * ((Qᴴ) ^ N * Q ^ N)).trace) atTop
          (𝓝 (ρ * darkProjection Q L).trace) := by
  classical
  by_cases hd : d = 0
  · subst d
    constructor
    · convert tendsto_const_nhds using 1
      funext N
      exact Subsingleton.elim _ _
    · intro ρ
      convert tendsto_const_nhds using 1
      funext N
      congr 1
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hd)
  let D := darkSpace Q L
  let q := (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) Q
  have hstar (A : Matrix (Fin d) (Fin d) ℂ) :
      (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) Aᴴ =
        ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) A).adjoint := by
    rw [← star_eq_conjTranspose, map_star]
    rfl
  have hD_kernel : D =
      LinearMap.ker (Matrix.toEuclideanLin (1 - (Qᴴ) ^ d * Q ^ d)) := by
    ext v
    simp only [D, darkSpace, Submodule.mem_iInf, LinearMap.mem_ker]
    have hzero (A : Matrix (Fin d) (Fin d) ℂ) :
        Matrix.toEuclideanLin A v = 0 ↔ A *ᵥ v.ofLp = 0 := by
      constructor
      · intro h
        have happ := Matrix.ofLp_toEuclideanLin_apply A v
        rw [h, WithLp.ofLp_zero] at happ
        exact happ.symm
      · intro h
        apply WithLp.ofLp_injective
        rw [Matrix.ofLp_toEuclideanLin_apply, h]
        rfl
    simpa only [hzero] using
      FiniteDetectionDarkSpace.dark_space_eq_survival_defect_kernel Q L hcomp v.ofLp
  have hQnorm : ‖Q‖ ≤ 1 := by
    have hpos : 0 ≤ Qᴴ * Q := (posSemidef_conjTranspose_mul_self Q).nonneg
    have hle : Qᴴ * Q ≤ 1 := by
      rw [← sub_nonneg, ← eq_sub_of_add_eq' hcomp]
      exact Finset.sum_nonneg fun x _ =>
        (posSemidef_conjTranspose_mul_self (L x)).nonneg
    have hnorm : ‖Qᴴ * Q‖ ≤ 1 :=
      (CStarAlgebra.norm_le_one_iff_of_nonneg _ hpos).2 hle
    rw [← sq_le_one_iff₀ (norm_nonneg Q), sq, ← CStarRing.norm_star_mul_self]
    simpa only [star_eq_conjTranspose] using hnorm
  have hqnorm : ‖q‖ ≤ 1 := by
    simpa only [q, Matrix.l2_opNorm_toEuclideanCLM] using hQnorm
  have hD_invariant : ∀ v, v ∈ D → q v ∈ D := by
    intro v hv
    simp only [D, darkSpace, Submodule.mem_iInf, LinearMap.mem_ker] at hv ⊢
    intro n x
    change (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (L x * Q ^ n)
      ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) Q v) = 0
    have hh := hv (n + 1) x
    change (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (L x * Q ^ (n + 1)) v = 0 at hh
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, Matrix.mul_assoc]
    simpa only [pow_succ] using hh
  have hunit : ∀ v, v ∈ D → q.adjoint (q v) = v := by
    intro v hv
    have hclick (x : ι) :
        (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (L x) v = 0 := by
      have hv' := hv
      simp only [D, darkSpace, Submodule.mem_iInf, LinearMap.mem_ker] at hv'
      change Matrix.toEuclideanLin (L x) v = 0
      simpa only [pow_zero, mul_one] using hv' 0 x
    have happ := congrArg
      (fun A : Matrix (Fin d) (Fin d) ℂ =>
        (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) A v) hcomp
    simp only [map_add, map_mul, map_sum, map_one,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply] at happ
    simp only [hstar] at happ
    change q.adjoint (q v) +
      (∑ x, ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (L x)).adjoint *
        (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (L x)) v = v at happ
    rw [_root_.sum_apply] at happ
    simp only [ContinuousLinearMap.mul_apply] at happ
    change q.adjoint (q v) +
      (∑ x, ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (L x)).adjoint
        ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (L x) v)) = v at happ
    simpa only [hclick, map_zero, Finset.sum_const_zero, add_zero] using happ
  let qD : D →ₗ[ℂ] D := q.toLinearMap.restrict hD_invariant
  have hqD_injective : Function.Injective qD := by
    intro v w hvw
    apply Subtype.ext
    have hvw' : q (v : EuclideanSpace ℂ (Fin d)) = q (w : EuclideanSpace ℂ (Fin d)) :=
      congrArg Subtype.val hvw
    have h := congrArg q.adjoint hvw'
    simpa only [hunit v v.2, hunit w w.2] using h
  have hqD_surjective : Function.Surjective qD :=
    LinearMap.surjective_of_injective hqD_injective
  have hDperp_invariant : ∀ v, v ∈ Dᗮ → q v ∈ Dᗮ := by
    intro v hv
    rw [Submodule.mem_orthogonal'] at hv ⊢
    intro z hz
    obtain ⟨w, hw⟩ := hqD_surjective ⟨z, hz⟩
    have hw' : q (w : EuclideanSpace ℂ (Fin d)) = z := congrArg Subtype.val hw
    rw [← hw', ← q.adjoint_inner_right, hunit w w.2]
    exact hv w w.2
  let r : Dᗮ →L[ℂ] Dᗮ := q.restrict hDperp_invariant
  have hrnorm : ‖r‖ ≤ 1 := by
    apply r.opNorm_le_bound zero_le_one
    intro v
    calc
      ‖r v‖ = ‖q (v : EuclideanSpace ℂ (Fin d))‖ := rfl
      _ ≤ ‖q‖ * ‖(v : EuclideanSpace ℂ (Fin d))‖ := q.le_opNorm _
      _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hqnorm (norm_nonneg _)
  have hr_pow_coe : ∀ N (v : Dᗮ),
      ((r ^ N) v : EuclideanSpace ℂ (Fin d)) =
        (q ^ N) (v : EuclideanSpace ℂ (Fin d)) := by
    intro N
    induction N with
    | zero => intro v; rfl
    | succ N ih =>
        intro v
        rw [pow_succ, pow_succ, ContinuousLinearMap.mul_apply,
          ContinuousLinearMap.mul_apply]
        exact ih (r v)
  have hr_powers : ∀ N, ‖r ^ N‖ ≤ 1 := by
    intro N
    induction N with
    | zero =>
        rw [pow_zero]
        change ‖ContinuousLinearMap.id ℂ Dᗮ‖ ≤ 1
        exact ContinuousLinearMap.norm_id_le
    | succ N ih =>
        rw [pow_succ]
        calc
          ‖r ^ N * r‖ ≤ ‖r ^ N‖ * ‖r‖ := norm_mul_le _ _
          _ ≤ 1 * 1 := mul_le_mul ih hrnorm (norm_nonneg _) zero_le_one
          _ = 1 := mul_one _
  have hrd_strict : ∀ v : Dᗮ, v ≠ 0 → ‖(r ^ d) v‖ < ‖v‖ := by
    intro v hv
    have hle : ‖(r ^ d) v‖ ≤ ‖v‖ := by
      calc
        ‖(r ^ d) v‖ ≤ ‖r ^ d‖ * ‖v‖ := (r ^ d).le_opNorm v
        _ ≤ 1 * ‖v‖ := by
          gcongr
          exact hr_powers d
        _ = ‖v‖ := one_mul _
    refine lt_of_le_of_ne hle ?_
    intro heq'
    let w : EuclideanSpace ℂ (Fin d) := v
    have heq : ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (Q ^ d)
        w‖ = ‖w‖ := by
      rw [map_pow]
      change ‖(q ^ d) w‖ = ‖w‖
      change ‖(q ^ d) (v : EuclideanSpace ℂ (Fin d))‖ = ‖v‖
      rw [← hr_pow_coe d v]
      exact heq'
    let a := (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (Q ^ d)
    have hApow : ‖Q ^ d‖ ≤ 1 :=
      (norm_pow_le Q d).trans (pow_le_one₀ (norm_nonneg Q) hQnorm)
    have hpos : 0 ≤ (Q ^ d)ᴴ * Q ^ d :=
      (posSemidef_conjTranspose_mul_self (Q ^ d)).nonneg
    have hstar_norm : ‖(Q ^ d)ᴴ * Q ^ d‖ ≤ 1 := by
      rw [← star_eq_conjTranspose, CStarRing.norm_star_mul_self]
      nlinarith [norm_nonneg (Q ^ d)]
    have hleA : (Q ^ d)ᴴ * Q ^ d ≤ 1 :=
      (CStarAlgebra.norm_le_one_iff_of_nonneg _ hpos).mp hstar_norm
    have hdefect : (1 - (Qᴴ) ^ d * Q ^ d).PosSemidef := by
      rw [← conjTranspose_pow]
      exact (sub_nonneg.mpr hleA).posSemidef
    have ha_star :
        (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) ((Qᴴ) ^ d) = a.adjoint := by
      rw [← conjTranspose_pow, hstar]
    have hdefect_apply :
        (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (1 - (Qᴴ) ^ d * Q ^ d)
            w = w - a.adjoint (a w) := by
      simp only [map_sub, map_one, map_mul, ha_star, a,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
        ContinuousLinearMap.mul_apply]
    have hinner : inner ℂ w
        ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ))
          (1 - (Qᴴ) ^ d * Q ^ d) w) = 0 := by
      rw [hdefect_apply, inner_sub_right, ContinuousLinearMap.adjoint_inner_right]
      simp only [inner_self_eq_norm_sq_to_K]
      rw [show a w =
        (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (Q ^ d) w from rfl, heq]
      ring
    have hquad : star w.ofLp ⬝ᵥ
        ((1 - (Qᴴ) ^ d * Q ^ d) *ᵥ w.ofLp) = 0 := by
      rw [EuclideanSpace.inner_eq_star_dotProduct] at hinner
      rw [dotProduct_comm] at hinner
      change star w.ofLp ⬝ᵥ
        (Matrix.toEuclideanLin (1 - (Qᴴ) ^ d * Q ^ d) w).ofLp = 0 at hinner
      rw [Matrix.ofLp_toEuclideanLin_apply] at hinner
      exact hinner
    have hveczero := (hdefect.dotProduct_mulVec_zero_iff
      w.ofLp).mp hquad
    have hlinzero : Matrix.toEuclideanLin (1 - (Qᴴ) ^ d * Q ^ d)
        w = 0 := by
      apply WithLp.ofLp_injective
      rw [Matrix.ofLp_toEuclideanLin_apply, hveczero]
      rfl
    have hvD : w ∈ D := by
      rw [hD_kernel]
      exact hlinzero
    have hvbot : w ∈ (⊥ : Submodule ℂ
        (EuclideanSpace ℂ (Fin d))) := by
      rw [← D.inf_orthogonal_eq_bot]
      exact ⟨hvD, v.2⟩
    apply hv
    apply Subtype.ext
    simpa only [Submodule.mem_bot, Submodule.coe_zero, w] using hvbot
  have hrd_norm : ‖r ^ d‖ < 1 := by
    cases subsingleton_or_nontrivial Dᗮ with
    | inl hE =>
        letI : Subsingleton Dᗮ := hE
        simpa only [Subsingleton.elim (r ^ d) 0, norm_zero] using zero_lt_one
    | inr hE =>
        letI : Nontrivial Dᗮ := hE
        have hs : (sphere (0 : Dᗮ) 1).Nonempty :=
          NormedSpace.sphere_nonempty.mpr zero_le_one
        obtain ⟨y, hy, hmax⟩ := (isCompact_sphere (0 : Dᗮ) 1).exists_isMaxOn hs
          (r ^ d).continuous.norm.continuousOn
        have hynorm : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy
        have hyne : y ≠ 0 := by
          intro h
          rw [h, norm_zero] at hynorm
          norm_num at hynorm
        have hnorm_le : ‖r ^ d‖ ≤ ‖(r ^ d) y‖ := by
          rw [← (r ^ d).sSup_sphere_eq_norm]
          apply csSup_le (hs.image fun x => ‖(r ^ d) x‖)
          intro z hz
          obtain ⟨x, hx, rfl⟩ := hz
          exact hmax hx
        exact hnorm_le.trans_lt (by simpa only [hynorm] using hrd_strict y hyne)
  have hr_pow_zero : Tendsto (fun N => r ^ N) atTop (𝓝 0) := by
    have hrd_powers : ∀ N, ‖(r ^ d) ^ N‖ ≤ ‖r ^ d‖ ^ N := by
      intro N
      induction N with
      | zero =>
          rw [pow_zero]
          change ‖ContinuousLinearMap.id ℂ Dᗮ‖ ≤ 1
          exact ContinuousLinearMap.norm_id_le
      | succ N ih =>
          rw [pow_succ, pow_succ]
          exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right ih (norm_nonneg (r ^ d)))
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun N => norm_nonneg (r ^ N))
    · intro N
      calc
        ‖r ^ N‖ = ‖r ^ (N % d) * (r ^ d) ^ (N / d)‖ := by
          congr 1
          rw [← pow_mul, ← pow_add, Nat.mod_add_div]
        _ ≤ ‖r ^ (N % d)‖ * ‖(r ^ d) ^ (N / d)‖ := norm_mul_le _ _
        _ ≤ 1 * ‖(r ^ d) ^ (N / d)‖ := by
          gcongr
          exact hr_powers (N % d)
        _ ≤ ‖r ^ d‖ ^ (N / d) := by
          simpa only [one_mul] using hrd_powers (N / d)
    · exact (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one
        (norm_nonneg (r ^ d)) hrd_norm).comp
          (Nat.tendsto_div_const_atTop hd)
  have hq_pow_mem : ∀ N v, v ∈ D → (q ^ N) v ∈ D := by
    intro N
    induction N with
    | zero => intro v hv; simpa using hv
    | succ N ih =>
        intro v hv
        rw [pow_succ', ContinuousLinearMap.mul_apply]
        exact hD_invariant _ (ih v hv)
  have hsurvival_dark : ∀ N v, v ∈ D → (q.adjoint ^ N * q ^ N) v = v := by
    intro N
    induction N with
    | zero => intro v hv; simp
    | succ N ih =>
        intro v hv
        have hpow_mem : (q ^ N) v ∈ D := hq_pow_mem N v hv
        rw [pow_succ, pow_succ', ContinuousLinearMap.mul_apply,
          ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
          hunit _ hpow_mem]
        simpa only [ContinuousLinearMap.mul_apply] using ih v hv
  have hqadj_norm : ‖q.adjoint‖ ≤ 1 := by
    exact ((ContinuousLinearMap.adjoint (𝕜 := ℂ)).norm_map q).trans_le hqnorm
  have hsurvival_bound : ∀ N,
      ‖q.adjoint ^ N * q ^ N - D.starProjection‖ ≤ ‖r ^ N‖ := by
    intro N
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (r ^ N))
    intro v
    let y := v - D.starProjection v
    have hy : y ∈ Dᗮ := Submodule.sub_starProjection_mem_orthogonal v
    have hproj : D.starProjection v ∈ D := by simp
    have hrewrite : (q.adjoint ^ N * q ^ N - D.starProjection) v =
        (q.adjoint ^ N * q ^ N) y := by
      simp only [ContinuousLinearMap.sub_apply, y, map_sub, hsurvival_dark N _ hproj]
    rw [hrewrite, ContinuousLinearMap.mul_apply]
    calc
      ‖(q.adjoint ^ N) ((q ^ N) y)‖ ≤ ‖q.adjoint ^ N‖ * ‖(q ^ N) y‖ :=
        (q.adjoint ^ N).le_opNorm _
      _ ≤ 1 * ‖(q ^ N) y‖ := by
        gcongr
        exact (norm_pow_le q.adjoint N).trans
          (pow_le_one₀ (norm_nonneg q.adjoint) hqadj_norm)
      _ = ‖(r ^ N) ⟨y, hy⟩‖ := by
        rw [one_mul]
        exact congrArg norm (hr_pow_coe N ⟨y, hy⟩).symm
      _ ≤ ‖r ^ N‖ * ‖(⟨y, hy⟩ : Dᗮ)‖ := (r ^ N).le_opNorm _
      _ ≤ ‖r ^ N‖ * ‖v‖ := by
        gcongr
        change ‖y‖ ≤ ‖v‖
        dsimp only [y]
        rw [← Submodule.starProjection_orthogonal_val (K := D) v]
        exact Dᗮ.norm_starProjection_apply_le v
  have hsurvival_clm : Tendsto (fun N => q.adjoint ^ N * q ^ N) atTop
      (𝓝 D.starProjection) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun N => norm_nonneg (q.adjoint ^ N * q ^ N - D.starProjection))
      hsurvival_bound
    exact tendsto_zero_iff_norm_tendsto_zero.mp hr_pow_zero
  have hmatrix : Tendsto (fun N => (Qᴴ) ^ N * Q ^ N) atTop
      (𝓝 (darkProjection Q L)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hnorm := tendsto_iff_norm_sub_tendsto_zero.mp hsurvival_clm
    refine hnorm.congr' (Eventually.of_forall fun N => ?_)
    change ‖q.adjoint ^ N * q ^ N - D.starProjection‖ =
      ‖(Qᴴ) ^ N * Q ^ N - darkProjection Q L‖
    rw [← Matrix.l2_opNorm_toEuclideanCLM]
    simp only [map_sub, map_mul, map_pow, hstar, darkProjection, D, q,
      StarAlgEquiv.apply_symm_apply]
  refine ⟨hmatrix, fun ρ => ?_⟩
  let tr : Matrix (Fin d) (Fin d) ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin d) ℂ ℂ)
  have hmul : Tendsto (fun N => ρ * ((Qᴴ) ^ N * Q ^ N)) atTop
      (𝓝 (ρ * darkProjection Q L)) := tendsto_const_nhds.mul hmatrix
  have htrace := (tr.continuous.tendsto (ρ * darkProjection Q L)).comp hmul
  refine htrace.congr' (Eventually.of_forall fun N => ?_)
  rfl

#print axioms finite_detection_survival_limit

end D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit
