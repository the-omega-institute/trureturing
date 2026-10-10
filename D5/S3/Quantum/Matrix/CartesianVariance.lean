/- GID: D5/S3/Quantum/Matrix/CartesianVariance
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/CartesianVariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cartesian matrix variance attains its density maximum at a pure vector. -/

/-
admission_basis: escape-witness
proof_shape: frobSq_eq_sum: bind-only; consumer: frobSq_block, frobSq_columns, vectorize_norm_sq; escape_witness: none
proof_shape: frobSq_nonneg: bind-only; consumer: commutatorDensity_density, commutator_norm_bound_of_pure, commutator_pure_max_bound, commutator_variance_bound, defect_lower_bound, frobSq_project_le, gap_nonnegative, projection_K_quadratic, projection_adjoint_bound, projection_channel_from_translation, translation_gap, two_level_from_projection_gap; escape_witness: none
proof_shape: vectorize_norm_sq: bind-only; consumer: commutator_norm_bound_of_pure, frobSq_eq_zero_iff, gap_bound, trace_product_cauchy; escape_witness: none
proof_shape: pureState_density: bind-only; consumer: density_nonempty, pure_of_density_linear_max, pure_variance_maximizer; escape_witness: none
proof_shape: density_nonempty: bind-only; consumer: density_compact, density_convex, density_variance_max; escape_witness: none
proof_shape: density_compact: bind-only; consumer: density_variance_max; escape_witness: none
proof_shape: density_convex: bind-only; consumer: variance_maximizer_linear; escape_witness: none
proof_shape: density_variance_max: bind-only; consumer: pure_variance_maximizer; escape_witness: none
proof_shape: first_order_coefficient_nonpos: bind-only; consumer: variance_maximizer_linear; escape_witness: none
proof_shape: trace_density_adjoint: bind-only; consumer: variance_centered, variance_mixture_expansion; escape_witness: none
proof_shape: variance_mixture_expansion: bind-only; consumer: variance_maximizer_linear; escape_witness: none
proof_shape: cartesian_hermitian: bind-only; consumer: centeredCartesian_hermitian; escape_witness: none
proof_shape: centeredCartesian_hermitian: bind-only; consumer: pure_variance_maximizer; escape_witness: none
proof_shape: variance_maximizer_linear: bind-only; consumer: pure_variance_maximizer; escape_witness: none
proof_shape: hermitian_spectral_sum: bind-only; consumer: hermitian_trace_spectral; escape_witness: none
proof_shape: density_eigenvalues_sum: bind-only; consumer: pure_of_density_linear_max; escape_witness: none
proof_shape: hermitian_trace_spectral: bind-only; consumer: pure_of_density_linear_max; escape_witness: none
proof_shape: pure_of_density_linear_max: content; escape_witness: pure_of_density_linear_max
proof_shape: variance_centered: bind-only; consumer: pure_variance_maximizer; escape_witness: none
proof_shape: pure_variance_maximizer: content; escape_witness: sphere_image_eq_ball_image, pure_of_density_linear_max, blochPure_surjective
proof_shape: matrix_pairing: bind-only; consumer: comm_adjoint_quadratic, trace_pairing_columns, trace_product_cauchy; escape_witness: none
proof_shape: frobSq_star: bind-only; consumer: frobSq_left_project_le, projection_K_quadratic, projection_channel_from_translation, trace_product_cauchy; escape_witness: none
proof_shape: frobSq_eq_zero_iff: bind-only; consumer: commutatorDensity_density, commutator_variance_bound; escape_witness: none
proof_shape: trace_cycle_four: bind-only; consumer: commutator_variance_identity; escape_witness: none
proof_shape: commutator_variance_identity: bind-only; consumer: commutator_variance_bound; escape_witness: none
proof_shape: trace_commutator_mean: bind-only; consumer: commutator_variance_bound; escape_witness: none
proof_shape: trace_product_cauchy: bind-only; consumer: commutator_variance_bound, projection_channel_from_translation; escape_witness: none
proof_shape: commutatorDensity_density: bind-only; consumer: commutator_pure_max_bound; escape_witness: none
proof_shape: commutator_variance_bound: bind-only; consumer: commutator_pure_max_bound; escape_witness: none
proof_shape: commutator_pure_max_bound: bind-only; consumer: maximizing_block_frame; escape_witness: none
escape_witness: pure_of_density_linear_max / pure_variance_maximizer
Direct frozen dependencies:
  owner GID: D5/S3/Weil/ZetaLinear/PosIndex; declaration: RHLinalg.frobSq
    declaration statement_id: sha256:a1114d4731d26d6c5ef81acb0a254cdc6e0ed6e629ccb2dcf75d7faa00f4ccce
  owner GID: D5/S3/Observer/HiddenFlow/ProjectionCommutatorIdentity; declaration: D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator
    declaration statement_id: sha256:4b14c2bab713c5f81d97b9a10d285ee0878e4a933dc5a6b66387f846355b44aa
  owner GID: D5/S3/Quantum/Fibers/PhysicalFiber; declaration: D5.S3.Quantum.Fibers.PhysicalFiber.physicalFiber
    declaration statement_id: sha256:65270b91c4986d1de9cdd6a6ad41ca004284b27ede01d27532432d4b8c3b6ced
  owner GID: D5/S3/Quantum/Fibers/PhysicalFiber; declaration: D5.S3.Quantum.Fibers.PhysicalFiber.finite_dimensional_physical_fiber
    declaration statement_id: sha256:20c3cc4b8eb976ba90fe5823cc1a6fb4ef0812d411aa5a82926a53aa578aa013
  baseline-frozen owner GID: D5/S3/Quantum/BlockNorm/EssentiallyHermitian; public declaration: D5.S3.Quantum.BlockNorm.EssentiallyHermitian.outer_pairing_trace
    declaration statement_id (producing Lean report): sha256:026aa081134ae367a4943807fd4e09d088eccaac327f2c3b990afb796e124a28
  baseline-frozen owner GID: D5/S3/Quantum/Entanglement/UniversalReplacementCapacityGrowth; public declaration: D5.S3.Quantum.Entanglement.UniversalReplacementCapacityGrowth.pure_trace
    declaration statement_id (producing Lean report): sha256:10a7dafe6e7a6b1cf2bcce71b142fca1562280cfd40a3330284db5fc95180878
  Other lane imports are same-delivery prerequisites, not baseline-frozen dependencies.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S3.Quantum.Matrix.NumericalRange
import D5.S3.Quantum.Entanglement.UniversalReplacementCapacityGrowth
import D5.S3.Quantum.BlockNorm.EssentiallyHermitian
import D5.S3.Quantum.Fibers.PhysicalFiber
import D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity

noncomputable section
open Matrix Set Unitary Filter
open scoped ComplexInnerProductSpace ComplexOrder Topology
namespace D5.S3.Quantum.Matrix.CartesianVariance
open D5.S3.Quantum.Matrix.NumericalRange
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum
open D5.S3.Quantum.Fibers.PhysicalFiber

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem frobSq_eq_sum {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ)) :
    RHLinalg.frobSq A = ∑ i, ∑ j, Complex.normSq (A j i) := by
  simp [RHLinalg.frobSq, Matrix.trace, Matrix.mul_apply, Complex.normSq_apply, Complex.mul_re]

theorem frobSq_nonneg {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ)) : 0 ≤ RHLinalg.frobSq A := by
  exact (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self A).trace_nonneg).1

def vectorize (n : ℕ) : (Matrix (Fin n) (Fin n) ℂ) ≃ₗ[ℂ] (EuclideanSpace ℂ (Fin n × Fin n)) :=
  (LinearEquiv.curry ℂ ℂ (Fin n) (Fin n)).symm.trans
    (WithLp.linearEquiv 2 ℂ (Fin n × Fin n → ℂ)).symm

theorem vectorize_norm_sq {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ)) :
    ‖vectorize n A‖ ^ 2 = RHLinalg.frobSq A := by
  rw [EuclideanSpace.norm_sq_eq, frobSq_eq_sum, Finset.sum_comm]
  change (∑ ij : Fin n × Fin n, ‖A ij.1 ij.2‖ ^ 2) =
    ∑ i, ∑ j, Complex.normSq (A i j)
  simp only [Fintype.sum_prod_type, Complex.normSq_eq_norm_sq]

def cartesian {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ)) : (Matrix (Fin n) (Fin n) ℂ) := (1/2 : ℝ) • (Aᴴ*A+A*Aᴴ)

def variance {n : ℕ} (A ρ : (Matrix (Fin n) (Fin n) ℂ)) : ℝ :=
  (Matrix.trace (ρ * cartesian A)).re -
    Complex.normSq (Matrix.trace (ρ * A))

private theorem pureState_density {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) (hv : ‖v‖ = 1) :
    ((((Matrix.vecMulVec (WithLp.ofLp v) (star (WithLp.ofLp v))))).PosSemidef ∧ Matrix.trace ((Matrix.vecMulVec (WithLp.ofLp v) (star (WithLp.ofLp v)))) = 1) := by
  refine ⟨Matrix.posSemidef_vecMulVec_self_star v.ofLp, ?_⟩
  rw [D5.S3.Quantum.Entanglement.UniversalReplacementCapacityGrowth.pure_trace,hv]
  norm_num

private theorem density_nonempty {n : ℕ} (hn : 0 < n) : {ρ : (Matrix (Fin n) (Fin n) ℂ) | ((ρ).PosSemidef ∧ Matrix.trace ρ = 1)}.Nonempty := by
  refine ⟨(Matrix.vecMulVec (WithLp.ofLp (EuclideanSpace.single ⟨0,hn⟩ 1)) (star (WithLp.ofLp (EuclideanSpace.single ⟨0,hn⟩ 1)))),pureState_density _ ?_⟩
  simp

private theorem density_compact {n : ℕ} (hn : 0 < n) : IsCompact {ρ : (Matrix (Fin n) (Fin n) ℂ) | ((ρ).PosSemidef ∧ Matrix.trace ρ = 1)} := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  obtain ⟨ρ,hρ⟩ := density_nonempty hn
  let L : (Matrix (Fin n) (Fin n) ℂ) →ₗ[ℂ] (Empty → ℂ) := 0
  have h := finite_dimensional_physical_fiber L ρ hρ.1 hρ.2
  have he : physicalFiber L ρ = {ρ : (Matrix (Fin n) (Fin n) ℂ) | ((ρ).PosSemidef ∧ Matrix.trace ρ = 1)} := by
    ext σ; simp [physicalFiber,L]
  rw [he] at h
  exact h.2.1

private theorem density_convex {n : ℕ} (hn : 0 < n) : Convex ℝ {ρ : (Matrix (Fin n) (Fin n) ℂ) | ((ρ).PosSemidef ∧ Matrix.trace ρ = 1)} := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  obtain ⟨ρ,hρ⟩ := density_nonempty hn
  let L : (Matrix (Fin n) (Fin n) ℂ) →ₗ[ℂ] (Empty → ℂ) := 0
  have h := finite_dimensional_physical_fiber L ρ hρ.1 hρ.2
  have he : physicalFiber L ρ = {ρ : (Matrix (Fin n) (Fin n) ℂ) | ((ρ).PosSemidef ∧ Matrix.trace ρ = 1)} := by
    ext σ; simp [physicalFiber,L]
  rw [he] at h
  exact h.2.2

private theorem density_variance_max {n : ℕ} (hn : 0 < n) (A : (Matrix (Fin n) (Fin n) ℂ)) :
    ∃ ρ : (Matrix (Fin n) (Fin n) ℂ), ((ρ).PosSemidef ∧ Matrix.trace ρ = 1) ∧ ∀ σ : (Matrix (Fin n) (Fin n) ℂ), ((σ).PosSemidef ∧ Matrix.trace σ = 1) → variance A σ ≤ variance A ρ := by
  have hc : Continuous (variance A) := by
    unfold variance Matrix.trace
    fun_prop
  obtain ⟨ρ,hρ,hm⟩ := (density_compact hn).exists_isMaxOn (density_nonempty hn) hc.continuousOn
  exact ⟨ρ,hρ,hm⟩

private theorem first_order_coefficient_nonpos (x y : ℝ) (hy : 0 ≤ y)
    (h : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t*x-t^2*y ≤ 0) : x ≤ 0 := by
  have hlim : Tendsto (fun t : ℝ => x-t*y) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    have hc : Continuous (fun t : ℝ => x-t*y) := by fun_prop
    have hl : Tendsto (fun t : ℝ => x-t*y) (𝓝[>] (0 : ℝ)) (𝓝 (x-0*y)) :=
      hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa using hl
  apply le_of_tendsto hlim
  have hlt : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hlt] with t ht ht1
  have hp := h t (le_of_lt ht) (le_of_lt ht1)
  have he : t * (x-t*y) ≤ 0 := by nlinarith only [hp]
  exact nonpos_of_mul_nonpos_right he ht

private def centeredCartesian {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ)) (z : ℂ) : (Matrix (Fin n) (Fin n) ℂ) :=
  cartesian A - star z • A - z • Aᴴ

private theorem trace_density_adjoint {n : ℕ} (A ρ : (Matrix (Fin n) (Fin n) ℂ)) (hρ : ((ρ).PosSemidef ∧ Matrix.trace ρ = 1)) :
    Matrix.trace (ρ*Aᴴ) = star (Matrix.trace (ρ*A)) := by
  rw [←Matrix.trace_conjTranspose,Matrix.conjTranspose_mul,hρ.1.isHermitian,
    Matrix.trace_mul_comm]

private theorem variance_mixture_expansion {n : ℕ} (A ρ σ : (Matrix (Fin n) (Fin n) ℂ)) (hρ : ((ρ).PosSemidef ∧ Matrix.trace ρ = 1)) (hσ : ((σ).PosSemidef ∧ Matrix.trace σ = 1))
    (t : ℝ) :
    variance A ((1-t) • ρ+t • σ) - variance A ρ =
      t*((Matrix.trace ((σ-ρ)*centeredCartesian A (Matrix.trace (ρ*A)))).re) -
      t^2*Complex.normSq (Matrix.trace ((σ-ρ)*A)) := by
  have hconj := trace_density_adjoint A ρ hρ
  have hconjσ := trace_density_adjoint A σ hσ
  simp only [variance,centeredCartesian,cartesian,Matrix.add_mul,Matrix.smul_mul,
    Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_smul,Matrix.trace_add,Matrix.trace_sub,
    Matrix.trace_smul,hconj,hconjσ,Complex.real_smul,smul_eq_mul,Complex.star_def,Complex.add_re,Complex.sub_re,Complex.mul_re,
    Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,
    Complex.normSq_apply,Complex.add_im,Complex.sub_im,Complex.conj_re,Complex.conj_im]
  ring

private theorem cartesian_hermitian {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ)) : (cartesian A).IsHermitian := by
  unfold cartesian
  apply Matrix.IsHermitian.smul _ (IsSelfAdjoint.all _)
  exact (Matrix.isHermitian_conjTranspose_mul_self A).add
    (Matrix.isHermitian_mul_conjTranspose_self A)

private theorem centeredCartesian_hermitian {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ)) (z : ℂ) :
    (centeredCartesian A z).IsHermitian := by
  change (centeredCartesian A z)ᴴ = centeredCartesian A z
  simp only [centeredCartesian,Matrix.conjTranspose_sub,Matrix.conjTranspose_smul,
    (cartesian_hermitian A).eq,Matrix.conjTranspose_conjTranspose,star_star]
  abel

private theorem variance_maximizer_linear {n : ℕ} (hn : 0 < n) (A ρ : (Matrix (Fin n) (Fin n) ℂ)) (hρ : ((ρ).PosSemidef ∧ Matrix.trace ρ = 1))
    (hm : ∀ σ : (Matrix (Fin n) (Fin n) ℂ), ((σ).PosSemidef ∧ Matrix.trace σ = 1) → variance A σ ≤ variance A ρ) :
    ∀ σ : (Matrix (Fin n) (Fin n) ℂ), ((σ).PosSemidef ∧ Matrix.trace σ = 1) →
      (Matrix.trace (σ*centeredCartesian A (Matrix.trace (ρ*A)))).re ≤
      (Matrix.trace (ρ*centeredCartesian A (Matrix.trace (ρ*A)))).re := by
  intro σ hσ
  have hcoef : (Matrix.trace ((σ-ρ)*centeredCartesian A (Matrix.trace (ρ*A)))).re ≤ 0 := by
    apply first_order_coefficient_nonpos _ _ (Complex.normSq_nonneg _)
    intro t ht ht1
    have hd := density_convex hn hρ hσ (by linarith : 0 ≤ 1-t) ht (by ring : 1-t+t=1)
    have h := hm _ hd
    rw [←variance_mixture_expansion A ρ σ hρ hσ t]
    linarith
  simpa only [Matrix.sub_mul,Matrix.trace_sub,Complex.sub_re,sub_nonpos] using hcoef

private theorem hermitian_spectral_sum {n : ℕ} (ρ : (Matrix (Fin n) (Fin n) ℂ)) (hρ : ρ.IsHermitian) :
    ρ = ∑ i, hρ.eigenvalues i • (Matrix.vecMulVec (WithLp.ofLp (hρ.eigenvectorBasis i)) (star (WithLp.ofLp (hρ.eigenvectorBasis i)))) := by
  ext j k
  conv_lhs => rw [hρ.spectral_theorem,Unitary.conjStarAlgAut_apply,Matrix.mul_apply]
  simp only [Matrix.sum_apply,Matrix.smul_apply,Matrix.vecMulVec,smul_eq_mul,Complex.real_smul]
  apply Finset.sum_congr rfl
  intro i _
  simp [Matrix.mul_diagonal,Matrix.conjTranspose_apply,
    Matrix.IsHermitian.eigenvectorUnitary_apply]
  ring

private theorem density_eigenvalues_sum {n : ℕ} (ρ : (Matrix (Fin n) (Fin n) ℂ)) (hρ : ((ρ).PosSemidef ∧ Matrix.trace ρ = 1)) :
    ∑ i, hρ.1.isHermitian.eigenvalues i = 1 := by
  have h := hρ.1.isHermitian.trace_eq_sum_eigenvalues.symm.trans hρ.2
  simpa using congrArg Complex.re h

private theorem hermitian_trace_spectral {n : ℕ} (ρ A : (Matrix (Fin n) (Fin n) ℂ)) (hρ : ρ.IsHermitian) :
    Matrix.trace (ρ*A) = ∑ i, hρ.eigenvalues i •
      inner ℂ (hρ.eigenvectorBasis i) (Matrix.toEuclideanLin A (hρ.eigenvectorBasis i)) := by
  have hcast {k : ℕ} (M : Matrix (Fin k) (Fin k) ℂ) (x : EuclideanSpace ℂ (Fin k)) :
      Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) M x = Matrix.toEuclideanLin M x := by rfl
  conv_lhs => rw [hermitian_spectral_sum ρ hρ]
  simp only [Matrix.sum_mul,Matrix.trace_sum,Matrix.smul_mul,Matrix.trace_smul,D5.S3.Quantum.BlockNorm.EssentiallyHermitian.outer_pairing_trace,hcast]

private theorem pure_of_density_linear_max {n : ℕ} (A K ρ : (Matrix (Fin n) (Fin n) ℂ))
    (hK : K.IsHermitian) (hρ : ((ρ).PosSemidef ∧ Matrix.trace ρ = 1))
    (hm : ∀ σ : (Matrix (Fin n) (Fin n) ℂ), ((σ).PosSemidef ∧ Matrix.trace σ = 1) → (Matrix.trace (σ*K)).re ≤ (Matrix.trace (ρ*K)).re) :
    ∃ v : EuclideanSpace ℂ (Fin n), ‖v‖ = 1 ∧
      Matrix.trace ((Matrix.vecMulVec (WithLp.ofLp v) (star (WithLp.ofLp v)))*A) = Matrix.trace (ρ*A) ∧
      (Matrix.trace ((Matrix.vecMulVec (WithLp.ofLp v) (star (WithLp.ofLp v)))*K)).re = (Matrix.trace (ρ*K)).re := by
  have hcast {k : ℕ} (M : Matrix (Fin k) (Fin k) ℂ) (x : EuclideanSpace ℂ (Fin k)) :
      Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) M x = Matrix.toEuclideanLin M x := by rfl
  classical
  let T := (Matrix.toEuclideanLin K).toContinuousLinearMap
  let lam : ℝ := (Matrix.trace (ρ*K)).re
  let p : Fin n → ℝ := hρ.1.isHermitian.eigenvalues
  let v : Fin n → EuclideanSpace ℂ (Fin n) := hρ.1.isHermitian.eigenvectorBasis
  let q : Fin n → ℝ := fun i => (Matrix.trace ((Matrix.vecMulVec (WithLp.ofLp (v i)) (star (WithLp.ofLp (v i))))*K)).re
  have hv : ∀ i, ‖v i‖ = 1 := hρ.1.isHermitian.eigenvectorBasis.orthonormal.norm_eq_one
  have hp : ∀ i, 0 ≤ p i := hρ.1.eigenvalues_nonneg
  have hp1 : ∑ i, p i = 1 := density_eigenvalues_sum ρ hρ
  have hupper : ∀ w : EuclideanSpace ℂ (Fin n), ‖w‖ = 1 →
      (inner ℂ w (T w)).re ≤ lam := by
    intro w hw
    simpa only [D5.S3.Quantum.BlockNorm.EssentiallyHermitian.outer_pairing_trace,hcast,T,lam,LinearMap.coe_toContinuousLinearMap'] using hm ((Matrix.vecMulVec (WithLp.ofLp w) (star (WithLp.ofLp w)))) (pureState_density w hw)
  have hqle : ∀ i, q i ≤ lam := fun i => hm _ (pureState_density _ (hv i))
  have havg : ∑ i, p i*q i = lam := by
    have h := hermitian_trace_spectral ρ K hρ.1.isHermitian
    have hh := congrArg Complex.re h
    simpa only [lam,p,q,v,D5.S3.Quantum.BlockNorm.EssentiallyHermitian.outer_pairing_trace,hcast,Complex.re_sum,Complex.real_smul,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hh.symm
  have hsumdiff : ∑ i, p i*(lam-q i) = 0 := by
    simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,hp1,one_mul,havg,sub_self]
  have hzero : ∀ i, p i*(lam-q i) = 0 := by
    have h := Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => mul_nonneg (hp i) (sub_nonneg.mpr (hqle i)))
    exact fun i => h.mp hsumdiff i (Finset.mem_univ i)
  have hT : IsSelfAdjoint T := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hK)
  let S : Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
    Module.End.eigenspace (Matrix.toEuclideanLin K) (lam : ℂ)
  have hsupport : ∀ i, p i ≠ 0 → v i ∈ S := by
    intro i hpi
    have hqi : q i = lam := (sub_eq_zero.mp ((mul_eq_zero.mp (hzero i)).resolve_left hpi)).symm
    have hqinner : T.reApplyInnerSelf (v i) = lam := by
      rw [ContinuousLinearMap.reApplyInnerSelf_apply,inner_re_symm]
      simpa [q,T,D5.S3.Quantum.BlockNorm.EssentiallyHermitian.outer_pairing_trace,hcast] using hqi
    have hmax : IsMaxOn T.reApplyInnerSelf (Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) ‖v i‖) (v i) := by
      intro w hw
      have hwnorm : ‖w‖ = 1 := by simpa [hv i] using hw
      change T.reApplyInnerSelf w ≤ T.reApplyInnerSelf (v i)
      rw [hqinner,ContinuousLinearMap.reApplyInnerSelf_apply,inner_re_symm]
      exact hupper w hwnorm
    have heig := hT.eq_smul_self_of_isLocalExtrOn (Or.inr hmax.localize)
    have hray : T.rayleighQuotient (v i) = lam := by
      change T.reApplyInnerSelf (v i) / ‖v i‖^2 = lam
      rw [hqinner,hv i]
      simp
    rw [hray] at heig
    exact Module.End.mem_eigenspace_iff.mpr heig
  have hμ : Matrix.trace (ρ*A) ∈ subspaceNumericalRange A S := by
    have hconv := subspace_numericalRange_convex A S
    have hz : ∀ i, p i ≠ 0 → inner ℂ (v i) (Matrix.toEuclideanLin A (v i)) ∈ subspaceNumericalRange A S := by
      intro i hpi
      exact ⟨⟨v i,hsupport i hpi⟩,hv i,rfl⟩
    have hcomb := hconv.finsum_mem hp (by simpa only [finsum_eq_sum_of_fintype] using hp1) hz
    have hdecomp := hermitian_trace_spectral ρ A hρ.1.isHermitian
    rw [hdecomp]
    simpa only [p,v,finsum_eq_sum_of_fintype] using hcomb
  obtain ⟨ψ,hψ,hmean⟩ := hμ
  refine ⟨ψ,hψ,?_,?_⟩
  · rw [D5.S3.Quantum.BlockNorm.EssentiallyHermitian.outer_pairing_trace,hcast]
    exact hmean.symm
  · have heig : Matrix.toEuclideanLin K (ψ : EuclideanSpace ℂ (Fin n)) =
        (lam : ℂ) • (ψ : EuclideanSpace ℂ (Fin n)) := Module.End.mem_eigenspace_iff.mp ψ.property
    rw [D5.S3.Quantum.BlockNorm.EssentiallyHermitian.outer_pairing_trace,hcast,heig,inner_smul_right,inner_self_eq_norm_sq_to_K]
    have hψambient : ‖(ψ : EuclideanSpace ℂ (Fin n))‖ = 1 := hψ
    simp [lam,hψambient]

private theorem variance_centered {n : ℕ} (A ρ : (Matrix (Fin n) (Fin n) ℂ)) (hρ : ((ρ).PosSemidef ∧ Matrix.trace ρ = 1)) (z : ℂ)
    (hz : Matrix.trace (ρ*A) = z) :
    variance A ρ = (Matrix.trace (ρ*centeredCartesian A z)).re + Complex.normSq z := by
  have hstar : Matrix.trace (ρ*Aᴴ) = star z := by rw [trace_density_adjoint A ρ hρ,hz]
  simp only [variance,centeredCartesian,cartesian,Matrix.mul_sub,Matrix.mul_smul,
    Matrix.trace_sub,Matrix.trace_smul,hz,hstar,smul_eq_mul,Complex.star_def,
    Complex.sub_re,Complex.mul_re,Complex.conj_re,Complex.conj_im,Complex.normSq_apply]
  ring

theorem pure_variance_maximizer {n : ℕ} (hn : 0 < n) (A : (Matrix (Fin n) (Fin n) ℂ)) :
    ∃ v : EuclideanSpace ℂ (Fin n), ‖v‖ = 1 ∧
      ∀ ρ : (Matrix (Fin n) (Fin n) ℂ), ((ρ).PosSemidef ∧ Matrix.trace ρ = 1) → variance A ρ ≤ variance A ((Matrix.vecMulVec (WithLp.ofLp v) (star (WithLp.ofLp v)))) := by
  obtain ⟨ρ,hρ,hm⟩ := density_variance_max hn A
  let z := Matrix.trace (ρ*A)
  let K := centeredCartesian A z
  obtain ⟨v,hv,hmean,hlinear⟩ := pure_of_density_linear_max A K ρ
    (centeredCartesian_hermitian A z) hρ (variance_maximizer_linear hn A ρ hρ hm)
  refine ⟨v,hv,?_⟩
  have heq : variance A ((Matrix.vecMulVec (WithLp.ofLp v) (star (WithLp.ofLp v)))) = variance A ρ := by
    rw [variance_centered A ρ hρ z rfl,
      variance_centered A ((Matrix.vecMulVec (WithLp.ofLp v) (star (WithLp.ofLp v)))) (pureState_density v hv) z hmean,hlinear]
  intro σ hσ
  rw [heq]
  exact hm σ hσ

theorem matrix_pairing {n : ℕ} (A B : (Matrix (Fin n) (Fin n) ℂ)) :
    inner ℂ (vectorize n A) (vectorize n B) = Matrix.trace (Aᴴ*B) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ ij : Fin n × Fin n, B ij.1 ij.2 * star (A ij.1 ij.2)) =
    ∑ i, ∑ j, star (A j i)*B j i
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem frobSq_star {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ)) : RHLinalg.frobSq Aᴴ = RHLinalg.frobSq A := by
  simpa only [RHLinalg.frobSq, Matrix.conjTranspose_conjTranspose,
    RCLike.re_eq_complex_re] using congrArg Complex.re (Matrix.trace_mul_comm A Aᴴ)

private theorem frobSq_eq_zero_iff {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ)) : RHLinalg.frobSq A = 0 ↔ A=0 := by
  rw [←vectorize_norm_sq,sq_eq_zero_iff,norm_eq_zero]
  exact (vectorize n).map_eq_zero_iff

private theorem trace_cycle_four {n : ℕ} (A B C D : (Matrix (Fin n) (Fin n) ℂ)) :
    Matrix.trace (A*B*C*D) = Matrix.trace (B*C*D*A) := by
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm A (B*C*D)

private theorem commutator_variance_identity {n : ℕ} (A B : (Matrix (Fin n) (Fin n) ℂ)) :
    RHLinalg.frobSq (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B)+RHLinalg.frobSq (Bᴴ*A+A*Bᴴ) =
      (Matrix.trace ((Bᴴ*B+B*Bᴴ)*(Aᴴ*A+A*Aᴴ))).re := by
  have h1 : Matrix.trace (Bᴴ*Aᴴ*A*B) = Matrix.trace (B*Bᴴ*Aᴴ*A) := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle (Bᴴ*Aᴴ) A B
  have h2 := trace_cycle_four Bᴴ Aᴴ B A
  have h3 := (trace_cycle_four B Aᴴ Bᴴ A).symm
  have h4 := trace_cycle_four Aᴴ Bᴴ B A
  have h5 := trace_cycle_four Aᴴ B Bᴴ A
  have h7 : Matrix.trace (B*Aᴴ*A*Bᴴ) = Matrix.trace (Bᴴ*B*Aᴴ*A) := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle (B*Aᴴ) A Bᴴ
  simp only [RHLinalg.frobSq,D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator,Matrix.conjTranspose_sub,Matrix.conjTranspose_add,
    Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_sub,
    Matrix.sub_mul,Matrix.mul_add,Matrix.add_mul,Matrix.trace_sub,Matrix.trace_add,
    ←Matrix.mul_assoc]
  rw [h1,h2,h3,h4,h5,h7]
  simp only [RCLike.re_eq_complex_re, Complex.add_re, Complex.sub_re]
  ring

private theorem trace_commutator_mean {n : ℕ} (A B : (Matrix (Fin n) (Fin n) ℂ)) :
    Matrix.trace ((Bᴴ*B+B*Bᴴ)*A) = Matrix.trace ((Bᴴ*A+A*Bᴴ)*B) := by
  simp only [Matrix.add_mul,Matrix.trace_add,←Matrix.mul_assoc]
  rw [Matrix.trace_mul_cycle Bᴴ B A,←Matrix.trace_mul_cycle Bᴴ A B,add_comm]

theorem trace_product_cauchy {n : ℕ} (Q B : (Matrix (Fin n) (Fin n) ℂ)) :
    Complex.normSq (Matrix.trace (Q*B)) ≤ RHLinalg.frobSq Q*RHLinalg.frobSq B := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (vectorize n Qᴴ) (vectorize n B)
  rw [matrix_pairing,Matrix.conjTranspose_conjTranspose] at h
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  rw [mul_pow,vectorize_norm_sq,vectorize_norm_sq,frobSq_star,←Complex.normSq_eq_norm_sq] at hs
  exact hs

private def commutatorDensity {n : ℕ} (B : (Matrix (Fin n) (Fin n) ℂ)) : (Matrix (Fin n) (Fin n) ℂ) :=
  (2*RHLinalg.frobSq B)⁻¹ • (Bᴴ*B+B*Bᴴ)

private theorem commutatorDensity_density {n : ℕ} (B : (Matrix (Fin n) (Fin n) ℂ)) (hB : B ≠ 0) :
    (((commutatorDensity B)).PosSemidef ∧ Matrix.trace (commutatorDensity B) = 1) := by
  have hu : 0 < RHLinalg.frobSq B := lt_of_le_of_ne (frobSq_nonneg B)
    (fun h => hB ((frobSq_eq_zero_iff B).mp h.symm))
  refine ⟨?_,?_⟩
  · apply Matrix.PosSemidef.smul _ (by positivity : 0 ≤ (2*RHLinalg.frobSq B)⁻¹)
    exact (Matrix.posSemidef_conjTranspose_mul_self B).add (by simpa using Matrix.posSemidef_conjTranspose_mul_self Bᴴ)
  · have hreal : Matrix.trace (Bᴴ*B) = (RHLinalg.frobSq B : ℂ) := by
      have hh := (Matrix.posSemidef_conjTranspose_mul_self B).isHermitian.trace_eq_sum_eigenvalues
      rw [hh]
      apply Complex.ext
      · simp [RHLinalg.frobSq,hh]
      · simp
    have he : Matrix.trace (B*Bᴴ) = Matrix.trace (Bᴴ*B) := Matrix.trace_mul_comm _ _
    simp [commutatorDensity,Matrix.trace_smul,Matrix.trace_add,he,hreal]
    field_simp
    norm_num

private theorem commutator_variance_bound {n : ℕ} (A B : (Matrix (Fin n) (Fin n) ℂ)) (hB : B ≠ 0) :
    RHLinalg.frobSq (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B) ≤ 4*RHLinalg.frobSq B*variance A (commutatorDensity B) := by
  have hu : 0 < RHLinalg.frobSq B := lt_of_le_of_ne (frobSq_nonneg B)
    (fun h => hB ((frobSq_eq_zero_iff B).mp h.symm))
  have hc := trace_product_cauchy (Bᴴ*A+A*Bᴴ) B
  have hv : 4*(RHLinalg.frobSq B)^2*variance A (commutatorDensity B) =
      RHLinalg.frobSq B*(RHLinalg.frobSq (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B)+RHLinalg.frobSq (Bᴴ*A+A*Bᴴ))-
        Complex.normSq (Matrix.trace ((Bᴴ*A+A*Bᴴ)*B)) := by
    rw [commutator_variance_identity,←trace_commutator_mean]
    simp only [variance,cartesian,commutatorDensity,Matrix.smul_mul,Matrix.mul_smul,
      Matrix.trace_smul,Complex.real_smul,smul_eq_mul,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,zero_add,sub_zero,
      Complex.normSq_apply]
    field_simp [hu.ne']
    ring
  have h : RHLinalg.frobSq B*RHLinalg.frobSq (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B) ≤
      RHLinalg.frobSq B*(4*RHLinalg.frobSq B*variance A (commutatorDensity B)) := by nlinarith
  exact le_of_mul_le_mul_left h hu

theorem commutator_pure_max_bound {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ))
    (v : EuclideanSpace ℂ (Fin n)) (hv : ‖v‖ = 1)
    (hm : ∀ ρ : (Matrix (Fin n) (Fin n) ℂ), ((ρ).PosSemidef ∧ Matrix.trace ρ = 1) → variance A ρ ≤ variance A ((Matrix.vecMulVec (WithLp.ofLp v) (star (WithLp.ofLp v))))) (B : (Matrix (Fin n) (Fin n) ℂ)) :
    RHLinalg.frobSq (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B) ≤ 4*RHLinalg.frobSq B*variance A ((Matrix.vecMulVec (WithLp.ofLp v) (star (WithLp.ofLp v)))) := by
  by_cases hB : B=0
  · subst B
    simp [D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator,RHLinalg.frobSq]
  · have hb := commutator_variance_bound A B hB
    exact hb.trans (mul_le_mul_of_nonneg_left (hm _ (commutatorDensity_density B hB))
      (mul_nonneg (by norm_num) (frobSq_nonneg B)))

#print axioms frobSq_eq_sum
#print axioms frobSq_nonneg
#print axioms vectorize_norm_sq
#print axioms D5.S3.Quantum.BlockNorm.EssentiallyHermitian.outer_pairing_trace
#print axioms pure_variance_maximizer
#print axioms matrix_pairing
#print axioms frobSq_star
#print axioms trace_product_cauchy
#print axioms commutator_pure_max_bound

end D5.S3.Quantum.Matrix.CartesianVariance
