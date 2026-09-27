/- GID: D5/S3/Quantum/Measurement/FiniteDetectionSurvivalLimit
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/FiniteDetectionSurvivalLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Survival effects converge to the dark-space projection. -/

import D5.S3.ObserverMemory.Dynamics.ResidualKernelInvariance
import D5.S3.ObserverMemory.Dynamics.MaximalUnobservableSubspace
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
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder Topology

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

/-- On the orthogonal complement of the dark space, survival defects contract geometrically in
blocks of the ambient dimension. The same gap controls arbitrary times through quotient-remainder
decomposition. -/
theorem dark_block_contraction {d : ℕ} {ι : Type*} [Fintype ι]
    (Q : Matrix (Fin d) (Fin d) ℂ) (L : ι → Matrix (Fin d) (Fin d) ℂ)
    (hcomp : Qᴴ * Q + ∑ x, (L x)ᴴ * L x = 1) (hd : d ≠ 0) :
    ∃ (g : ℝ) (c : ℕ → ℝ),
      0 < g ∧ g ≤ 1 ∧
      (∀ N, 0 ≤ c N) ∧
      (∀ N, c N ≤ 1) ∧
      (∀ N, c (N + d) ≤ (1 - g) * c N) ∧
      (∀ N, darkProjection Q L ≤ (Qᴴ) ^ N * Q ^ N) ∧
      (∀ N, (Qᴴ) ^ N * Q ^ N - darkProjection Q L =
        (1 - darkProjection Q L) * ((Qᴴ) ^ N * Q ^ N) *
          (1 - darkProjection Q L)) ∧
      0 ≤ 1 - darkProjection Q L ∧
      (∀ N, (Qᴴ) ^ N * Q ^ N - darkProjection Q L ≤
        c N • (1 - darkProjection Q L)) ∧
      (∀ N, ‖(Qᴴ) ^ N * Q ^ N - darkProjection Q L‖ ≤ c N) ∧
      1 - g = c d ∧
      (Qᴴ) ^ d * Q ^ d - darkProjection Q L ≤
        (1 - g) • (1 - darkProjection Q L) ∧
      (∀ n k, c (n + k * d) ≤ (1 - g) ^ k) ∧
      (∀ N, c N ≤ (1 - g) ^ (N / d)) ∧
      (∀ n k, (Qᴴ) ^ (n + k * d) * Q ^ (n + k * d) - darkProjection Q L ≤
        (1 - g) ^ k • (1 - darkProjection Q L)) ∧
      (∀ N, (Qᴴ) ^ N * Q ^ N - darkProjection Q L ≤
        (1 - g) ^ (N / d) • (1 - darkProjection Q L)) := by
  classical
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
  let T : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d) := q.toLinearMap
  let C : EuclideanSpace ℂ (Fin d) →ₗ[ℂ]
      PiLp 2 (fun _ : ι => EuclideanSpace ℂ (Fin d)) :=
    (WithLp.linearEquiv 2 ℂ (ι → EuclideanSpace ℂ (Fin d))).symm.toLinearMap.comp
      (LinearMap.pi fun x : ι =>
        ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (L x)).toLinearMap)
  have hC_iterate (k : ℕ) (v : EuclideanSpace ℂ (Fin d)) (x : ι) :
      (C.comp (T ^ k) v) x = Matrix.toEuclideanLin (L x * Q ^ k) v := by
    simp only [C, T, LinearMap.comp_apply, LinearEquiv.coe_coe,
      WithLp.coe_symm_linearEquiv, PiLp.toLp_apply, LinearMap.pi_apply]
    rw [← ContinuousLinearMap.toLinearMap_pow]
    change (((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (L x)) * q ^ k) v =
      Matrix.toEuclideanLin (L x * Q ^ k) v
    rw [← map_pow, ← map_mul]
    rfl
  have hD_future : D = ⨅ k : ℕ, LinearMap.ker (C.comp (T ^ k)) := by
    ext v
    simp only [D, darkSpace, Submodule.mem_iInf, LinearMap.mem_ker]
    constructor
    · intro hv k
      apply PiLp.ext
      intro x
      rw [hC_iterate, PiLp.zero_apply]
      exact hv k x
    · intro hv k x
      have hx := congrArg
        (fun z : PiLp 2 (fun _ : ι => EuclideanSpace ℂ (Fin d)) => z x) (hv k)
      simpa only [hC_iterate, PiLp.zero_apply] using hx
  have hD_invariant : Set.MapsTo q D D := by
    have hinvariant :=
      (D5.S3.ObserverMemory.Dynamics.MaximalUnobservableSubspace.future_kernel_is_maximal_invariant
        T C).2.1
    rwa [← hD_future] at hinvariant
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
    simp only [map_add, map_mul, map_sum, map_one, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.one_apply, hstar] at happ
    change q.adjoint (q v) +
      (∑ x, ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (L x)).adjoint *
        (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (L x)) v = v at happ
    rw [_root_.sum_apply] at happ
    simp only [ContinuousLinearMap.mul_apply] at happ
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
  have hD_adjoint_invariant : Set.MapsTo q.adjoint D D := by
    intro z hz
    obtain ⟨w, hw⟩ := hqD_surjective ⟨z, hz⟩
    have hw' : q (w : EuclideanSpace ℂ (Fin d)) = z := congrArg Subtype.val hw
    rw [← hw', hunit w w.2]
    exact w.2
  have hDperp_invariant : Set.MapsTo q Dᗮ Dᗮ :=
    ObserverMemory.Dynamics.ResidualKernelInvariance.residual_kernel_invariant
      q D hD_adjoint_invariant
  have hDperp_adjoint_invariant : Set.MapsTo q.adjoint Dᗮ Dᗮ := by
    apply ObserverMemory.Dynamics.ResidualKernelInvariance.residual_kernel_invariant q.adjoint D
    simpa only [ContinuousLinearMap.adjoint_adjoint] using hD_invariant
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
    rcases N with _ | N
    · rw [pow_zero]
      exact ContinuousLinearMap.norm_id_le
    · exact (norm_pow_le' r N.succ_pos).trans
        (pow_le_one₀ (norm_nonneg r) hrnorm)
  have hrd_strict : ∀ v : Dᗮ, v ≠ 0 → ‖(r ^ d) v‖ < ‖v‖ := by
    intro v hv
    have hle : ‖(r ^ d) v‖ ≤ ‖v‖ :=
      (r ^ d).le_opNorm v |>.trans
        (mul_le_mul_of_nonneg_right (hr_powers d) (norm_nonneg v) |>.trans_eq
          (one_mul _))
    refine lt_of_le_of_ne hle fun heq' => ?_
    let w : EuclideanSpace ℂ (Fin d) := v
    have heq : ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (Q ^ d) w‖ = ‖w‖ := by
      rw [map_pow]
      change ‖(q ^ d) (v : EuclideanSpace ℂ (Fin d))‖ = ‖v‖
      rwa [← hr_pow_coe d v]
    let a := (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (Q ^ d)
    have hpos : 0 ≤ (Q ^ d)ᴴ * Q ^ d :=
      (posSemidef_conjTranspose_mul_self (Q ^ d)).nonneg
    have hstar_norm : ‖(Q ^ d)ᴴ * Q ^ d‖ ≤ 1 := by
      rw [← star_eq_conjTranspose, CStarRing.norm_star_mul_self]
      simpa only [sq] using (sq_le_one_iff₀ (norm_nonneg (Q ^ d))).2
        ((norm_pow_le Q d).trans (pow_le_one₀ (norm_nonneg Q) hQnorm))
    have hdefect : (1 - (Qᴴ) ^ d * Q ^ d).PosSemidef := by
      rw [← conjTranspose_pow]
      exact (sub_nonneg.mpr
        ((CStarAlgebra.norm_le_one_iff_of_nonneg _ hpos).mp hstar_norm)).posSemidef
    have ha_star :
        (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) ((Qᴴ) ^ d) = a.adjoint := by
      rw [← conjTranspose_pow, hstar]
    have hinner : inner ℂ w
        ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ))
          (1 - (Qᴴ) ^ d * Q ^ d) w) = 0 := by
      simp only [map_sub, map_one, map_mul, ha_star, a,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
        ContinuousLinearMap.mul_apply, inner_sub_right,
        ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
      rw [show (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (Q ^ d) w = a w from rfl,
        heq]
      ring
    have hquad : star w.ofLp ⬝ᵥ
        ((1 - (Qᴴ) ^ d * Q ^ d) *ᵥ w.ofLp) = 0 := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at hinner
      change star w.ofLp ⬝ᵥ
        (Matrix.toEuclideanLin (1 - (Qᴴ) ^ d * Q ^ d) w).ofLp = 0 at hinner
      rwa [Matrix.ofLp_toEuclideanLin_apply] at hinner
    have hlinzero : Matrix.toEuclideanLin (1 - (Qᴴ) ^ d * Q ^ d) w = 0 := by
      apply WithLp.ofLp_injective
      rw [Matrix.ofLp_toEuclideanLin_apply,
        (hdefect.dotProduct_mulVec_zero_iff w.ofLp).mp hquad]
      rfl
    have hvD : w ∈ D := hD_kernel.symm ▸ hlinzero
    have hvbot : w ∈ (⊥ : Submodule ℂ (EuclideanSpace ℂ (Fin d))) := by
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
        have hyne : y ≠ 0 := fun h => by simpa [h] using hynorm
        have hnorm_le : ‖r ^ d‖ ≤ ‖(r ^ d) y‖ := by
          rw [← (r ^ d).sSup_sphere_eq_norm]
          exact csSup_le (hs.image fun x => ‖(r ^ d) x‖) fun z hz => by
            obtain ⟨x, hx, rfl⟩ := hz
            exact hmax hx
        exact hnorm_le.trans_lt (by simpa only [hynorm] using hrd_strict y hyne)
  let E := D.starProjection
  let F := 1 - E
  have hFproj : F = Dᗮ.starProjection := by
    apply ContinuousLinearMap.ext
    intro v
    simpa only [F, E, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.id_apply] using
      congrArg (fun f : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d) => f v)
        (D.starProjection_orthogonal).symm
  have hq_pow_D : ∀ N v, v ∈ D → (q ^ N) v ∈ D := by
    intro N v hv
    have hlin : (q ^ N) v = ((q : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] _) ^ N) v := by
      rw [← ContinuousLinearMap.toLinearMap_pow]
      rfl
    rw [hlin, Module.End.pow_apply]
    exact hD_invariant.iterate N hv
  have hq_pow_perp : ∀ N v, v ∈ Dᗮ → (q ^ N) v ∈ Dᗮ := by
    intro N v hv
    have hlin : (q ^ N) v = ((q : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] _) ^ N) v := by
      rw [← ContinuousLinearMap.toLinearMap_pow]
      rfl
    rw [hlin, Module.End.pow_apply]
    exact hDperp_invariant.iterate N hv
  have hqadj_pow_perp : ∀ N v, v ∈ Dᗮ → (q.adjoint ^ N) v ∈ Dᗮ := by
    intro N v hv
    have hlin : (q.adjoint ^ N) v =
        ((q.adjoint : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] _) ^ N) v := by
      rw [← ContinuousLinearMap.toLinearMap_pow]
      rfl
    rw [hlin, Module.End.pow_apply]
    exact hDperp_adjoint_invariant.iterate N hv
  have hsurvival_dark : ∀ N v, v ∈ D → (q.adjoint ^ N * q ^ N) v = v := by
    intro N
    induction N with
    | zero => intro v hv; simp
    | succ N ih =>
        intro v hv
        rw [pow_succ, pow_succ', ContinuousLinearMap.mul_apply,
          ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
          hunit _ (hq_pow_D N _ hv)]
        simpa only [ContinuousLinearMap.mul_apply] using ih v hv
  have hfactor_clm : ∀ N, q.adjoint ^ N * q ^ N - E =
      F * (q.adjoint ^ N * q ^ N) * F := by
    intro N
    apply ContinuousLinearMap.ext
    intro v
    let p := E v
    let y := v - p
    have hp : p ∈ D := D.starProjection_apply_mem v
    have hy : y ∈ Dᗮ := D.sub_starProjection_mem_orthogonal v
    have hSy : (q.adjoint ^ N * q ^ N) y ∈ Dᗮ :=
      hqadj_pow_perp N _ (hq_pow_perp N _ hy)
    have hFv : F v = y := by simp [F, E, y, p]
    have hEp : E p = p := D.starProjection_eq_self_iff.mpr hp
    have hEy : E y = 0 := D.starProjection_apply_eq_zero_iff.mpr hy
    have hFSy : F ((q.adjoint ^ N * q ^ N) y) =
        (q.adjoint ^ N * q ^ N) y := by
      rw [hFproj]
      exact Dᗮ.starProjection_eq_self_iff.mpr hSy
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hFv, hFSy]
    rw [show v = p + y by simp [p, y]]
    change (q.adjoint ^ N * q ^ N) (p + y) - E (p + y) =
      (q.adjoint ^ N * q ^ N) y
    rw [map_add, map_add, hsurvival_dark N p hp, hEp, hEy, add_zero]
    abel
  let P := darkProjection Q L
  let Pc := 1 - P
  have hPmap : (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) P = E := by
    simp only [P, darkProjection, D, E, StarAlgEquiv.apply_symm_apply]
  have hPcmap : (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) Pc = F := by
    simp only [Pc, F, map_sub, map_one, hPmap]
  have hfactor : ∀ N, (Qᴴ) ^ N * Q ^ N - P =
      Pc * ((Qᴴ) ^ N * Q ^ N) * Pc := by
    intro N
    apply (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).injective
    change (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ))
        ((Qᴴ) ^ N * Q ^ N - P) =
      (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ))
        (Pc * ((Qᴴ) ^ N * Q ^ N) * Pc)
    simp only [map_sub, map_mul, map_pow, hstar Q, hPmap, hPcmap]
    exact hfactor_clm N
  have hPc_star : Pcᴴ = Pc := by
    apply (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).injective
    change (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) Pcᴴ =
      (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) Pc
    rw [hstar Pc, hPcmap, hFproj]
    exact Dᗮ.starProjection_isSymmetric.clm_adjoint_eq
  have hPc_idem : Pc * Pc = Pc := by
    apply (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).injective
    change (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (Pc * Pc) =
      (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) Pc
    rw [map_mul, hPcmap, hFproj, Dᗮ.isIdempotentElem_starProjection.eq]
  have hPc_pos : Pc.PosSemidef := by
    simpa only [hPc_star, hPc_idem] using posSemidef_conjTranspose_mul_self Pc
  have hgram : ∀ N, (Qᴴ) ^ N * Q ^ N - P =
      (Q ^ N * Pc)ᴴ * (Q ^ N * Pc) := by
    intro N
    rw [hfactor N, conjTranspose_mul, conjTranspose_pow, hPc_star]
    simp only [Matrix.mul_assoc]
  have hP_le : ∀ N, P ≤ (Qᴴ) ^ N * Q ^ N := by
    intro N
    rw [← sub_nonneg, hgram]
    exact (posSemidef_conjTranspose_mul_self _).nonneg
  have hBnorm : ∀ N, ‖Q ^ N * Pc‖ ≤ ‖r ^ N‖ := by
    intro N
    rw [← Matrix.l2_opNorm_toEuclideanCLM]
    simp only [map_mul, map_pow, hPcmap]
    apply (q ^ N * F).opNorm_le_bound (norm_nonneg (r ^ N))
    intro v
    let y := v - E v
    have hy : y ∈ Dᗮ := D.sub_starProjection_mem_orthogonal v
    have hFv : F v = y := by simp [F, y, E]
    rw [ContinuousLinearMap.mul_apply, hFv, ← hr_pow_coe N ⟨y, hy⟩]
    exact (r ^ N).le_opNorm ⟨y, hy⟩ |>.trans
      (mul_le_mul_of_nonneg_left (by
        change ‖y‖ ≤ ‖v‖
        dsimp only [y]
        rw [← D.starProjection_orthogonal_val v]
        exact Dᗮ.norm_starProjection_apply_le v) (norm_nonneg _))
  let c : ℕ → ℝ := fun N => ‖r ^ N‖ ^ 2
  let a : ℝ := c d
  have hc_nonneg : ∀ N, 0 ≤ c N := fun N => sq_nonneg _
  have hc_le_one : ∀ N, c N ≤ 1 := by
    intro N
    dsimp only [c]
    exact (sq_le_one_iff₀ (norm_nonneg (r ^ N))).2 (hr_powers N)
  have hc_step : ∀ N, c (N + d) ≤ a * c N := by
    intro N
    dsimp only [c, a]
    rw [pow_add]
    calc
      ‖r ^ N * r ^ d‖ ^ 2 ≤ (‖r ^ N‖ * ‖r ^ d‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
          (norm_mul_le _ _)
      _ = ‖r ^ d‖ ^ 2 * ‖r ^ N‖ ^ 2 := by ring
  have ha_nonneg : 0 ≤ a := sq_nonneg _
  have ha_lt : a < 1 := by
    dsimp only [a, c]
    exact (sq_lt_one_iff₀ (norm_nonneg (r ^ d))).2 hrd_norm
  have hsurvival_norm : ∀ N, ‖(Qᴴ) ^ N * Q ^ N - P‖ ≤ c N := by
    intro N
    dsimp only [c]
    rw [hgram, ← star_eq_conjTranspose, CStarRing.norm_star_mul_self]
    have hb := hBnorm N
    calc
      ‖Q ^ N * Pc‖ * ‖Q ^ N * Pc‖ = ‖Q ^ N * Pc‖ ^ 2 := by rw [sq]
      _ ≤ ‖r ^ N‖ ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hb
  have hcontraction : ∀ N, (Qᴴ) ^ N * Q ^ N - P ≤ c N • Pc := by
    intro N
    let z := (Qᴴ) ^ N * Q ^ N - P
    have hHpos : z.PosSemidef := by
      dsimp only [z]
      rw [hgram]
      exact posSemidef_conjTranspose_mul_self _
    have hsupport : z ≤ ‖z‖ • Pc := by
      have hc := CStarAlgebra.star_left_conjugate_le_norm_smul
        (a := Pc) (b := z) (by
          simpa only [IsSelfAdjoint, star_eq_conjTranspose] using hHpos.isHermitian.eq)
      have hcut : Pc * z * Pc = z := by
        calc
          Pc * z * Pc = Pc * (Pc * ((Qᴴ) ^ N * Q ^ N) * Pc) * Pc := by
            rw [← hfactor N]
          _ = (Pc * Pc) * ((Qᴴ) ^ N * Q ^ N) * (Pc * Pc) := by
            simp only [Matrix.mul_assoc]
          _ = Pc * ((Qᴴ) ^ N * Q ^ N) * Pc := by rw [hPc_idem]
          _ = z := (hfactor N).symm
      have hPc_self : star Pc = Pc := by
        simpa only [star_eq_conjTranspose] using hPc_star
      rw [hPc_self, hcut, hPc_idem] at hc
      exact hc
    exact hsupport.trans
      (smul_le_smul_of_nonneg_right (hsurvival_norm N) hPc_pos.nonneg)
  have hblock : (Qᴴ) ^ d * Q ^ d - P ≤ a • Pc := by
    simpa only [a] using hcontraction d
  have hc_iter : ∀ n k, c (n + k * d) ≤ a ^ k := by
    intro n k
    induction k with
    | zero => simpa only [Nat.zero_mul, add_zero, pow_zero] using hc_le_one n
    | succ k ih =>
        calc
          c (n + k.succ * d) = c ((n + k * d) + d) := by
            rw [Nat.succ_mul, add_assoc]
          _ ≤ a * c (n + k * d) := hc_step (n + k * d)
          _ ≤ a * a ^ k := mul_le_mul_of_nonneg_left ih ha_nonneg
          _ = a ^ k.succ := by rw [pow_succ']
  have hc_quotient : ∀ N, c N ≤ a ^ (N / d) := by
    intro N
    have hdecomp : N = N % d + (N / d) * d := by
      rw [Nat.mul_comm, Nat.mod_add_div]
    calc
      c N = c (N % d + (N / d) * d) := congrArg c hdecomp
      _ ≤ a ^ (N / d) := hc_iter (N % d) (N / d)
  have hiterated : ∀ n k, (Qᴴ) ^ (n + k * d) * Q ^ (n + k * d) - P ≤
      a ^ k • Pc := by
    intro n k
    exact (hcontraction (n + k * d)).trans
      (smul_le_smul_of_nonneg_right (hc_iter n k) hPc_pos.nonneg)
  have hquotient : ∀ N, (Qᴴ) ^ N * Q ^ N - P ≤ a ^ (N / d) • Pc := by
    intro N
    exact (hcontraction N).trans
      (smul_le_smul_of_nonneg_right (hc_quotient N) hPc_pos.nonneg)
  let g : ℝ := 1 - a
  have hgpos : 0 < g := sub_pos.mpr ha_lt
  have hgle : g ≤ 1 := by
    dsimp only [g]
    exact sub_le_self 1 ha_nonneg
  refine ⟨g, c, hgpos, hgle, hc_nonneg, hc_le_one, ?_, hP_le, hfactor,
    hPc_pos.nonneg, hcontraction, hsurvival_norm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N
    simpa only [g, sub_sub_cancel] using hc_step N
  · simp only [g, sub_sub_cancel, a]
  · simpa only [g, sub_sub_cancel] using hblock
  · simpa only [g, sub_sub_cancel] using hc_iter
  · simpa only [g, sub_sub_cancel] using hc_quotient
  · simpa only [g, sub_sub_cancel] using hiterated
  · simpa only [g, sub_sub_cancel] using hquotient

#print axioms dark_block_contraction

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
  obtain ⟨g, c, hgpos, hgle, hc_nonneg, _hc_le_one, _hc_step, _hP_le, _hfactor,
    _hPc_nonneg, _hcontraction, hsurvival_norm, _hgap, _hblock, _hc_iter, hc_bound,
    _hiterated, _hquotient⟩ :=
    dark_block_contraction Q L hcomp hd
  change ∀ N, ‖(Qᴴ) ^ N * Q ^ N - darkProjection Q L‖ ≤ c N at hsurvival_norm
  let a : ℝ := 1 - g
  have ha_nonneg : 0 ≤ a := sub_nonneg.mpr hgle
  have ha_lt : a < 1 := sub_lt_self 1 hgpos
  change ∀ N, c N ≤ a ^ (N / d) at hc_bound
  have hc_tendsto : Tendsto c atTop (𝓝 0) := by
    apply squeeze_zero hc_nonneg hc_bound
    exact (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one ha_nonneg ha_lt).comp
      (Nat.tendsto_div_const_atTop hd)
  have hmatrix : Tendsto (fun N => (Qᴴ) ^ N * Q ^ N) atTop
      (𝓝 (darkProjection Q L)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun N => norm_nonneg _) hsurvival_norm hc_tendsto
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
