/- GID: D5/S3/Quantum/Measurement/FiniteDetectionTailBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/FiniteDetectionTailBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Survival beyond the dark weight has a geometric operator tail and finite mean. -/
import D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit
import D5.S3.Weil.ZetaLinear.RankTrace
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Quantum.Measurement.FiniteDetectionTailBound
open Filter Matrix Metric
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder Topology
open D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit
theorem finite_detection_tail_bound {d : ℕ} {ι : Type*} [Fintype ι]
    (Q : Matrix (Fin d) (Fin d) ℂ) (L : ι → Matrix (Fin d) (Fin d) ℂ)
    (hcomp : Qᴴ * Q + ∑ x, (L x)ᴴ * L x = 1) :
    ∃ g : ℝ, 0 < g ∧ g ≤ 1 ∧
      (∀ m : ℕ, 0 ≤ (Qᴴ) ^ (m * d) * Q ^ (m * d) - darkProjection Q L ∧
        (Qᴴ) ^ (m * d) * Q ^ (m * d) - darkProjection Q L ≤
          (1 - g) ^ m • (1 - darkProjection Q L)) ∧
      ∀ ρ : Matrix (Fin d) (Fin d) ℂ,
        ρ.PosSemidef → ρ.trace = 1 → darkProjection Q L * ρ = 0 →
          Summable (fun N : ℕ => (ρ * ((Qᴴ) ^ N * Q ^ N)).trace.re) ∧
          ∑' N : ℕ, (ρ * ((Qᴴ) ^ N * Q ^ N)).trace.re ≤ (d : ℝ) / g := by
  classical
  by_cases hd : d = 0
  · subst d
    refine ⟨1, zero_lt_one, le_rfl, ?_, ?_⟩
    · intro m
      exact ⟨le_of_eq (Subsingleton.elim _ _), le_of_eq (Subsingleton.elim _ _)⟩
    · intro ρ _ htrace _
      have : False := by simpa [Matrix.trace] using htrace
      exact this.elim
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hd)
  letI : NeZero d := ⟨hd⟩
  let D := darkSpace Q L
  let q := (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) Q
  have hstar (A : Matrix (Fin d) (Fin d) ℂ) : (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) Aᴴ = ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) A).adjoint := by
    rw [← star_eq_conjTranspose, map_star]; rfl
  have hD_kernel : D = LinearMap.ker (Matrix.toEuclideanLin (1 - (Qᴴ) ^ d * Q ^ d)) := by
    ext v
    simp only [D, darkSpace, Submodule.mem_iInf, LinearMap.mem_ker]
    have hzero (A : Matrix (Fin d) (Fin d) ℂ) : Matrix.toEuclideanLin A v = 0 ↔ A *ᵥ v.ofLp = 0 := by
      constructor
      · intro h
        have happ := Matrix.ofLp_toEuclideanLin_apply A v
        rw [h, WithLp.ofLp_zero] at happ; exact happ.symm
      · intro h
        apply WithLp.ofLp_injective
        rw [Matrix.ofLp_toEuclideanLin_apply, h]; rfl
    simpa only [hzero] using FiniteDetectionDarkSpace.dark_space_eq_survival_defect_kernel
      Q L hcomp v.ofLp
  have hQnorm : ‖Q‖ ≤ 1 := by
    have hpos : 0 ≤ Qᴴ * Q := (posSemidef_conjTranspose_mul_self Q).nonneg
    have hle : Qᴴ * Q ≤ 1 := by
      rw [← sub_nonneg, ← eq_sub_of_add_eq' hcomp]
      exact Finset.sum_nonneg fun x _ => (posSemidef_conjTranspose_mul_self (L x)).nonneg
    have hnorm : ‖Qᴴ * Q‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hpos).2 hle
    rw [← sq_le_one_iff₀ (norm_nonneg Q), sq, ← CStarRing.norm_star_mul_self]
    simpa only [star_eq_conjTranspose] using hnorm
  have hqnorm : ‖q‖ ≤ 1 := by simpa only [q, Matrix.l2_opNorm_toEuclideanCLM] using hQnorm
  let T : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d) := q.toLinearMap
  let C : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] PiLp 2 (fun _ : ι => EuclideanSpace ℂ (Fin d)) :=
    (WithLp.linearEquiv 2 ℂ (ι → EuclideanSpace ℂ (Fin d))).symm.toLinearMap.comp (LinearMap.pi
      fun x : ι => ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (L x)).toLinearMap)
  have hC_iterate (k : ℕ) (v : EuclideanSpace ℂ (Fin d)) (x : ι) : (C.comp (T ^ k) v) x = Matrix.toEuclideanLin (L x * Q ^ k) v := by
    simp only [C, T, LinearMap.comp_apply, LinearEquiv.coe_coe, WithLp.coe_symm_linearEquiv,
      PiLp.toLp_apply, LinearMap.pi_apply]
    rw [← ContinuousLinearMap.toLinearMap_pow]
    change (((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (L x)) * q ^ k) v =
      Matrix.toEuclideanLin (L x * Q ^ k) v
    rw [← map_pow, ← map_mul]; rfl
  have hD_future : D = ⨅ k : ℕ, LinearMap.ker (C.comp (T ^ k)) := by
    ext v
    simp only [D, darkSpace, Submodule.mem_iInf, LinearMap.mem_ker]
    constructor
    · intro hv k
      apply PiLp.ext; intro x
      rw [hC_iterate, PiLp.zero_apply]; exact hv k x
    · intro hv k x
      have hx := congrArg (fun z : PiLp 2 (fun _ : ι => EuclideanSpace ℂ (Fin d)) => z x) (hv k)
      simpa only [hC_iterate, PiLp.zero_apply] using hx
  have hD_invariant : Set.MapsTo q D D := by
    have hinvariant := (D5.S3.ObserverMemory.Dynamics.MaximalUnobservableSubspace.future_kernel_is_maximal_invariant T C).2.1
    rwa [← hD_future] at hinvariant
  have hunit : ∀ v, v ∈ D → q.adjoint (q v) = v := by
    intro v hv
    have hclick (x : ι) : (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (L x) v = 0 := by
      have hv' := hv
      simp only [D, darkSpace, Submodule.mem_iInf, LinearMap.mem_ker] at hv'
      change Matrix.toEuclideanLin (L x) v = 0
      simpa only [pow_zero, mul_one] using hv' 0 x
    have happ := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ =>
      (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) A v) hcomp
    simp only [map_add, map_mul, map_sum, map_one, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.one_apply, hstar] at happ
    change q.adjoint (q v) + (∑ x, ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ))
      (L x)).adjoint * (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (L x)) v = v at happ
    rw [_root_.sum_apply] at happ; simp only [ContinuousLinearMap.mul_apply] at happ
    simpa only [hclick, map_zero, Finset.sum_const_zero, add_zero] using happ
  let qD : D →ₗ[ℂ] D := q.toLinearMap.restrict hD_invariant
  have hqD_injective : Function.Injective qD := by
    intro v w hvw; apply Subtype.ext
    have hvw' : q (v : EuclideanSpace ℂ (Fin d)) = q (w : EuclideanSpace ℂ (Fin d)) := congrArg Subtype.val hvw
    have h := congrArg q.adjoint hvw'
    simpa only [hunit v v.2, hunit w w.2] using h
  have hqD_surjective : Function.Surjective qD := LinearMap.surjective_of_injective hqD_injective
  have hD_adjoint_invariant : Set.MapsTo q.adjoint D D := by
    intro z hz
    obtain ⟨w, hw⟩ := hqD_surjective ⟨z, hz⟩
    have hw' : q (w : EuclideanSpace ℂ (Fin d)) = z := congrArg Subtype.val hw
    rw [← hw', hunit w w.2]; exact w.2
  have hDperp_invariant : Set.MapsTo q Dᗮ Dᗮ := ObserverMemory.Dynamics.ResidualKernelInvariance.residual_kernel_invariant q D hD_adjoint_invariant
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
  have hr_pow_coe : ∀ N (v : Dᗮ), ((r ^ N) v : EuclideanSpace ℂ (Fin d)) = (q ^ N) (v : EuclideanSpace ℂ (Fin d)) := by
    intro N
    induction N with
    | zero => intro v; rfl
    | succ N ih =>
        intro v; rw [pow_succ, pow_succ, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply]
        exact ih (r v)
  have hr_powers : ∀ N, ‖r ^ N‖ ≤ 1 := by
    intro N
    rcases N with _ | N
    · rw [pow_zero]
      exact ContinuousLinearMap.norm_id_le
    · exact (norm_pow_le' r N.succ_pos).trans (pow_le_one₀ (norm_nonneg r) hrnorm)
  have hrd_strict : ∀ v : Dᗮ, v ≠ 0 → ‖(r ^ d) v‖ < ‖v‖ := by
    intro v hv
    have hle : ‖(r ^ d) v‖ ≤ ‖v‖ := (r ^ d).le_opNorm v |>.trans
      (mul_le_mul_of_nonneg_right (hr_powers d) (norm_nonneg v) |>.trans_eq (one_mul _))
    refine lt_of_le_of_ne hle fun heq' => ?_
    let w : EuclideanSpace ℂ (Fin d) := v
    have heq : ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (Q ^ d) w‖ = ‖w‖ := by
      rw [map_pow]
      change ‖(q ^ d) (v : EuclideanSpace ℂ (Fin d))‖ = ‖v‖
      rwa [← hr_pow_coe d v]
    let a := (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (Q ^ d)
    have hApow : ‖Q ^ d‖ ≤ 1 := (norm_pow_le Q d).trans (pow_le_one₀ (norm_nonneg Q) hQnorm)
    have hpos : 0 ≤ (Q ^ d)ᴴ * Q ^ d := (posSemidef_conjTranspose_mul_self (Q ^ d)).nonneg
    have hstar_norm : ‖(Q ^ d)ᴴ * Q ^ d‖ ≤ 1 := by
      rw [← star_eq_conjTranspose, CStarRing.norm_star_mul_self]; nlinarith [norm_nonneg (Q ^ d)]
    have hdefect : (1 - (Qᴴ) ^ d * Q ^ d).PosSemidef := by
      rw [← conjTranspose_pow]
      exact (sub_nonneg.mpr ((CStarAlgebra.norm_le_one_iff_of_nonneg _ hpos).mp hstar_norm)).posSemidef
    have ha_star : (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) ((Qᴴ) ^ d) = a.adjoint := by rw [← conjTranspose_pow, hstar]
    have hinner : inner ℂ w ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ))
        (1 - (Qᴴ) ^ d * Q ^ d) w) = 0 := by
      simp only [map_sub, map_one, map_mul, ha_star, a,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
        ContinuousLinearMap.mul_apply, inner_sub_right,
        ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
      rw [show (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (Q ^ d) w = a w from rfl, heq]
      ring
    have hquad : star w.ofLp ⬝ᵥ ((1 - (Qᴴ) ^ d * Q ^ d) *ᵥ w.ofLp) = 0 := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at hinner
      change star w.ofLp ⬝ᵥ (Matrix.toEuclideanLin (1 - (Qᴴ) ^ d * Q ^ d) w).ofLp = 0 at hinner
      rwa [Matrix.ofLp_toEuclideanLin_apply] at hinner
    have hlinzero : Matrix.toEuclideanLin (1 - (Qᴴ) ^ d * Q ^ d) w = 0 := by
      apply WithLp.ofLp_injective
      rw [Matrix.ofLp_toEuclideanLin_apply, (hdefect.dotProduct_mulVec_zero_iff w.ofLp).mp hquad]
      rfl
    have hvD : w ∈ D := hD_kernel.symm ▸ hlinzero
    have hvbot : w ∈ (⊥ : Submodule ℂ (EuclideanSpace ℂ (Fin d))) := by
      rw [← D.inf_orthogonal_eq_bot]; exact ⟨hvD, v.2⟩
    apply hv; apply Subtype.ext
    simpa only [Submodule.mem_bot, Submodule.coe_zero, w] using hvbot
  have hrd_norm : ‖r ^ d‖ < 1 := by
    cases subsingleton_or_nontrivial Dᗮ with
    | inl hE =>
        letI : Subsingleton Dᗮ := hE
        simpa only [Subsingleton.elim (r ^ d) 0, norm_zero] using zero_lt_one
    | inr hE =>
        letI : Nontrivial Dᗮ := hE
        have hs : (sphere (0 : Dᗮ) 1).Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
        obtain ⟨y, hy, hmax⟩ := (isCompact_sphere (0 : Dᗮ) 1).exists_isMaxOn hs
          (r ^ d).continuous.norm.continuousOn
        have hynorm : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy
        have hyne : y ≠ 0 := fun h => by simpa [h] using hynorm
        have hnorm_le : ‖r ^ d‖ ≤ ‖(r ^ d) y‖ := by
          rw [← (r ^ d).sSup_sphere_eq_norm]
          exact csSup_le (hs.image fun x => ‖(r ^ d) x‖) fun z hz => by
            obtain ⟨x, hx, rfl⟩ := hz; exact hmax hx
        exact hnorm_le.trans_lt (by simpa only [hynorm] using hrd_strict y hyne)
  let E := D.starProjection
  let F := 1 - E
  have hFproj : F = Dᗮ.starProjection := by
    apply ContinuousLinearMap.ext; intro v
    simpa only [F, E, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.id_apply] using
      congrArg (fun f : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d) => f v)
        (D.starProjection_orthogonal).symm
  have hq_pow_D : ∀ N v, v ∈ D → (q ^ N) v ∈ D := by
    intro N v hv
    have hlin : (q ^ N) v = ((q : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] _) ^ N) v := by
      rw [← ContinuousLinearMap.toLinearMap_pow]; rfl
    rw [hlin, Module.End.pow_apply]; exact hD_invariant.iterate N hv
  have hq_pow_perp : ∀ N v, v ∈ Dᗮ → (q ^ N) v ∈ Dᗮ := by
    intro N v hv
    have hlin : (q ^ N) v = ((q : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] _) ^ N) v := by
      rw [← ContinuousLinearMap.toLinearMap_pow]; rfl
    rw [hlin, Module.End.pow_apply]; exact hDperp_invariant.iterate N hv
  have hqadj_pow_perp : ∀ N v, v ∈ Dᗮ → (q.adjoint ^ N) v ∈ Dᗮ := by
    intro N v hv
    have hlin : (q.adjoint ^ N) v = ((q.adjoint : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] _) ^ N) v := by
      rw [← ContinuousLinearMap.toLinearMap_pow]; rfl
    rw [hlin, Module.End.pow_apply]; exact hDperp_adjoint_invariant.iterate N hv
  have hsurvival_dark : ∀ N v, v ∈ D → (q.adjoint ^ N * q ^ N) v = v := by
    intro N
    induction N with
    | zero => intro v hv; simp
    | succ N ih =>
        intro v hv
        rw [pow_succ, pow_succ', ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
          ContinuousLinearMap.mul_apply, hunit _ (hq_pow_D N _ hv)]
        simpa only [ContinuousLinearMap.mul_apply] using ih v hv
  have hfactor_clm : ∀ N, q.adjoint ^ N * q ^ N - E =
      F * (q.adjoint ^ N * q ^ N) * F := by
    intro N
    apply ContinuousLinearMap.ext; intro v
    let p := E v
    let y := v - p
    have hp : p ∈ D := D.starProjection_apply_mem v
    have hy : y ∈ Dᗮ := D.sub_starProjection_mem_orthogonal v
    have hSy : (q.adjoint ^ N * q ^ N) y ∈ Dᗮ := hqadj_pow_perp N _ (hq_pow_perp N _ hy)
    have hFv : F v = y := by simp [F, E, y, p]
    have hEp : E p = p := D.starProjection_eq_self_iff.mpr hp
    have hEy : E y = 0 := D.starProjection_apply_eq_zero_iff.mpr hy
    have hFSy : F ((q.adjoint ^ N * q ^ N) y) = (q.adjoint ^ N * q ^ N) y := by
      rw [hFproj]; exact Dᗮ.starProjection_eq_self_iff.mpr hSy
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.mul_apply, hFv, hFSy]
    rw [show v = p + y by simp [p, y]]
    change (q.adjoint ^ N * q ^ N) (p + y) - E (p + y) = (q.adjoint ^ N * q ^ N) y
    rw [map_add, map_add, hsurvival_dark N p hp, hEp, hEy, add_zero]
    abel
  let P := darkProjection Q L
  let Pc := 1 - P
  have hPmap : (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) P = E := by
    simp only [P, E, darkProjection, D, StarAlgEquiv.apply_symm_apply]
  have hPcmap : (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) Pc = F := by
    simp only [Pc, F, map_sub, map_one, hPmap]
  have hfactor : ∀ N, (Qᴴ) ^ N * Q ^ N - P = Pc * ((Qᴴ) ^ N * Q ^ N) * Pc := by
    intro N
    apply (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).injective
    change (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) ((Qᴴ) ^ N * Q ^ N - P) =
      (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (Pc * ((Qᴴ) ^ N * Q ^ N) * Pc)
    simp only [map_sub, map_mul, map_pow, hstar Q, hPmap, hPcmap]
    exact hfactor_clm N
  have hPc_star : Pcᴴ = Pc := by
    apply (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).injective
    change (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) Pcᴴ = (Matrix.toEuclideanCLM
      (n := Fin d) (𝕜 := ℂ)) Pc
    rw [hstar Pc, hPcmap, hFproj]
    exact Dᗮ.starProjection_isSymmetric.clm_adjoint_eq
  have hPc_idem : Pc * Pc = Pc := by
    apply (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).injective
    change (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (Pc * Pc) = (Matrix.toEuclideanCLM
      (n := Fin d) (𝕜 := ℂ)) Pc
    rw [map_mul, hPcmap, hFproj, Dᗮ.isIdempotentElem_starProjection.eq]
  have hPc_pos : Pc.PosSemidef := by simpa only [hPc_star, hPc_idem] using posSemidef_conjTranspose_mul_self Pc
  have hgram : ∀ N, (Qᴴ) ^ N * Q ^ N - P = (Q ^ N * Pc)ᴴ * (Q ^ N * Pc) := by
    intro N; rw [hfactor N, conjTranspose_mul, conjTranspose_pow, hPc_star]
    simp only [Matrix.mul_assoc]
  have hr_block : ∀ N, ‖r ^ N‖ ≤ ‖r ^ d‖ ^ (N / d) := by
    intro N
    calc
      ‖r ^ N‖ = ‖r ^ (N % d) * (r ^ d) ^ (N / d)‖ := by
        congr 1; rw [← pow_mul, ← pow_add, Nat.mod_add_div]
      _ ≤ ‖r ^ (N % d)‖ * ‖(r ^ d) ^ (N / d)‖ := norm_mul_le _ _
      _ ≤ 1 * ‖(r ^ d) ^ (N / d)‖ := by gcongr; exact hr_powers _
      _ ≤ ‖r ^ d‖ ^ (N / d) := by
        simp only [one_mul]
        rcases hdiv : N / d with _ | k
        · rw [pow_zero, pow_zero]
          exact ContinuousLinearMap.norm_id_le
        · exact norm_pow_le' (r ^ d) (by simp [hdiv])
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
    exact (r ^ N).le_opNorm ⟨y, hy⟩ |>.trans (mul_le_mul_of_nonneg_left (by
      change ‖y‖ ≤ ‖v‖; dsimp only [y]; rw [← D.starProjection_orthogonal_val v]
      exact Dᗮ.norm_starProjection_apply_le v) (norm_nonneg _))
  let a : ℝ := ‖r ^ d‖ ^ 2
  have ha_nonneg : 0 ≤ a := sq_nonneg _
  have ha_lt : a < 1 := by dsimp only [a]; nlinarith [norm_nonneg (r ^ d)]
  have htail : ∀ N, 0 ≤ (Qᴴ) ^ N * Q ^ N - P ∧
      (Qᴴ) ^ N * Q ^ N - P ≤ a ^ (N / d) • Pc := by
    intro N
    let z := (Qᴴ) ^ N * Q ^ N - P
    have hHpos : z.PosSemidef := by
      dsimp only [z]; rw [hgram]; exact posSemidef_conjTranspose_mul_self _
    have hHnorm : ‖z‖ ≤ a ^ (N / d) := by
      dsimp only [z]
      rw [hgram, ← star_eq_conjTranspose, CStarRing.norm_star_mul_self]
      have hb := (hBnorm N).trans (hr_block N)
      calc
        ‖Q ^ N * Pc‖ * ‖Q ^ N * Pc‖ = ‖Q ^ N * Pc‖ ^ 2 := by rw [sq]
        _ ≤ (‖r ^ d‖ ^ (N / d)) ^ 2 := (sq_le_sq₀ (norm_nonneg _)
          (pow_nonneg (norm_nonneg _) _)).2 hb
        _ = a ^ (N / d) := by
          dsimp only [a]; rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    constructor
    · exact hHpos.nonneg
    · have hsupport : z ≤ ‖z‖ • Pc := by
        have hc := CStarAlgebra.star_left_conjugate_le_norm_smul
          (a := Pc) (b := z) (by simpa only [IsSelfAdjoint, star_eq_conjTranspose] using
            hHpos.isHermitian.eq)
        have hcut : Pc * z * Pc = z := by
          calc
            Pc * z * Pc = Pc * (Pc * ((Qᴴ) ^ N * Q ^ N) * Pc) * Pc := by
              rw [← hfactor N]
            _ = (Pc * Pc) * ((Qᴴ) ^ N * Q ^ N) * (Pc * Pc) := by simp only [Matrix.mul_assoc]
            _ = Pc * ((Qᴴ) ^ N * Q ^ N) * Pc := by rw [hPc_idem]
            _ = z := (hfactor N).symm
        have hPc_self : star Pc = Pc := by simpa only [star_eq_conjTranspose] using hPc_star
        rw [hPc_self, hcut, hPc_idem] at hc; exact hc
      exact hsupport.trans (smul_le_smul_of_nonneg_right hHnorm hPc_pos.nonneg)
  let g : ℝ := 1 - a
  have hgpos : 0 < g := sub_pos.mpr ha_lt
  have hgle : g ≤ 1 := by dsimp only [g]; linarith
  refine ⟨g, hgpos, hgle, ?_, ?_⟩
  · intro m
    have hm := htail (m * d)
    have hmd : m * d / d = m := by rw [Nat.mul_comm, Nat.mul_div_right m (Nat.pos_of_ne_zero hd)]
    rw [hmd] at hm
    simpa only [P, Pc, g, sub_sub_cancel] using hm
  · intro ρ hρ htrace hsupp
    have hρP : (ρ * P).trace = 0 := by rw [Matrix.trace_mul_comm, hsupp, Matrix.trace_zero]
    have hρPc : (ρ * Pc).trace.re = 1 := by
      simp only [Pc, Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Complex.sub_re,
        htrace, hρP, Complex.one_re, Complex.zero_re, sub_zero]
    have hterm_nonneg : ∀ N, 0 ≤ (ρ * ((Qᴴ) ^ N * Q ^ N)).trace.re := by
      intro N
      have hH := RHLinalg.trace_mul_nonneg_of_posSemidef hρ (htail N).1.posSemidef
      have heq : (ρ * ((Qᴴ) ^ N * Q ^ N)).trace.re =
          (ρ * ((Qᴴ) ^ N * Q ^ N - P)).trace.re := by
        simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, hρP, sub_zero]
      rwa [heq]
    have hterm_le : ∀ N,
        (ρ * ((Qᴴ) ^ N * Q ^ N)).trace.re ≤ a ^ (N / d) := by
      intro N
      have hdiff := RHLinalg.trace_mul_nonneg_of_posSemidef hρ
        (Matrix.le_iff.mp (htail N).2)
      have heq : (ρ * ((Qᴴ) ^ N * Q ^ N)).trace.re =
          (ρ * ((Qᴴ) ^ N * Q ^ N - P)).trace.re := by
        simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, hρP, sub_zero]
      rw [heq]
      simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul] at hdiff
      change 0 ≤ (a ^ (N / d) • (ρ * Pc).trace -
        ((ρ * ((Qᴴ) ^ N * Q ^ N)).trace - (ρ * P).trace)).re at hdiff
      simp only [Complex.sub_re, Complex.smul_re, hρPc, hρP, Complex.zero_re,
        smul_eq_mul, mul_one, sub_zero] at hdiff
      linarith
    have hgeom : Summable (fun m : ℕ => a ^ m) := summable_geometric_of_lt_one ha_nonneg ha_lt
    have hprod : Summable (fun p : ℕ × Fin d => a ^ p.1) := by
      rw [summable_prod_of_nonneg (fun p => pow_nonneg ha_nonneg p.1)]
      constructor
      · exact fun _ => (hasSum_fintype _).summable
      · simpa only [tsum_fintype, Finset.sum_const, Finset.card_fin, nsmul_eq_mul] using hgeom.mul_left (d : ℝ)
    have hmajor : Summable (fun N : ℕ => a ^ (N / d)) := by
      change Summable (fun N : ℕ => a ^ ((Nat.divModEquiv d N).1))
      exact hprod.comp_injective (Nat.divModEquiv d).injective
    have hseries : Summable (fun N : ℕ => (ρ * ((Qᴴ) ^ N * Q ^ N)).trace.re) :=
      Summable.of_nonneg_of_le hterm_nonneg hterm_le hmajor
    have hsum_le := hseries.tsum_le_tsum hterm_le hmajor
    refine ⟨hseries, hsum_le.trans_eq ?_⟩
    calc
      ∑' N : ℕ, a ^ (N / d) = ∑' p : ℕ × Fin d, a ^ p.1 := by
        change (∑' N : ℕ, a ^ (Nat.divModEquiv d N).1) = _
        exact (Nat.divModEquiv d).tsum_eq (fun p : ℕ × Fin d => a ^ p.1)
      _ = ∑' m : ℕ, ∑' _i : Fin d, a ^ m := hprod.tsum_prod
      _ = ∑' m : ℕ, (d : ℝ) * a ^ m := by simp
      _ = (d : ℝ) * ∑' m : ℕ, a ^ m := tsum_mul_left
      _ = (d : ℝ) * (1 - a)⁻¹ := by rw [tsum_geometric_of_lt_one ha_nonneg ha_lt]
      _ = (d : ℝ) / g := by simp only [g, div_eq_mul_inv]
#print axioms finite_detection_tail_bound
end D5.S3.Quantum.Measurement.FiniteDetectionTailBound
