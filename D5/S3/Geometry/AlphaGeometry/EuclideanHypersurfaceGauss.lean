/- GID: D5/S3/Geometry/AlphaGeometry/EuclideanHypersurfaceGauss
   generality: G
   mirror-B: D5/B/S3/Geometry/AlphaGeometry/EuclideanHypersurfaceGauss
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coordinate Gauss tensor and its scalar trace contraction. -/

/-
admission_basis: escape-witness
escape_witness: ricci_of_structure
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15716
Mixed partial symmetry and differentiated frame structure produce the Ricci contraction. The frozen PositiveSimplexGeometryAndMixing coordinate formulas are specific to its simplex metric; christoffel, ricci and scalarCurvature here accept a general metric. Specializing this metric to that frozen metric gives the same three formulas definitionally.
Direct frozen dependencies: none.
Per-declaration classification; non-proposition definitions carry no content claim.
proof_shape: christoffel: bind-only; escape_witness: none; consumers: EuclideanHypersurfaceGauss.ricci, EuclideanHypersurfaceGauss.ricci_of_structure, QuantumCubeRootScalarCurvatureMonotone.Transport.christoffel_scale, QuantumCubeRootScalarCurvatureMonotone.Transport.christoffel_scale_eventually, QuantumCubeRootScalarCurvatureMonotone.Transport.ricci_scale, QuantumCubeRootScalarCurvatureMonotone.Transport.christoffel_congr_nhds, QuantumCubeRootScalarCurvatureMonotone.Transport.christoffel_eventually_congr, QuantumCubeRootScalarCurvatureMonotone.Transport.ricci_congr_nhds, QuantumCubeRootScalarCurvatureMonotone.christoffel_frame, QuantumCubeRootScalarCurvatureMonotone.christoffel_smooth, QuantumCubeRootScalarCurvatureMonotone.frame_structure, QuantumCubeRootScalarCurvatureMonotone.coordinate_ricci; frozen_dependencies: none
proof_shape: ricci: bind-only; escape_witness: none; consumers: EuclideanHypersurfaceGauss.scalarCurvature, EuclideanHypersurfaceGauss.scalar_as_matrix_trace, EuclideanHypersurfaceGauss.coordinate_gauss_scalar_of_ricci, EuclideanHypersurfaceGauss.ricci_of_structure, QuantumCubeRootScalarCurvatureMonotone.Transport.ricci_scale, QuantumCubeRootScalarCurvatureMonotone.Transport.scalar_curvature_dilation, QuantumCubeRootScalarCurvatureMonotone.Transport.ricci_congr_nhds, QuantumCubeRootScalarCurvatureMonotone.Transport.scalarCurvature_congr_nhds, QuantumCubeRootScalarCurvatureMonotone.coordinate_ricci, QuantumCubeRootScalarCurvatureMonotone.ricci_matrix_gauss; frozen_dependencies: none
proof_shape: scalarCurvature: bind-only; escape_witness: none; consumers: EuclideanHypersurfaceGauss.scalar_as_matrix_trace, EuclideanHypersurfaceGauss.coordinate_gauss_scalar_of_ricci, QuantumCubeRootScalarCurvatureMonotone.scal3, QuantumCubeRootScalarCurvatureMonotone.Transport.scalar_curvature_dilation, QuantumCubeRootScalarCurvatureMonotone.Transport.scalar_curvature_embedding_dilation_three, QuantumCubeRootScalarCurvatureMonotone.Transport.scalarCurvature_congr_nhds, QuantumCubeRootScalarCurvatureMonotone.coordinate_gauss_scalar, QuantumCubeRootScalarCurvatureMonotone.coordinate_shape_gauss, QuantumCubeRootScalarCurvatureMonotone.chart_scalar_spectral, QuantumCubeRootScalarCurvatureMonotone.scal3_eq_spectral_ratio; frozen_dependencies: none
proof_shape: scalar_as_matrix_trace: bind-only; escape_witness: none; consumers: EuclideanHypersurfaceGauss.coordinate_gauss_scalar_of_ricci; frozen_dependencies: none
proof_shape: coordinate_gauss_scalar_of_ricci: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.coordinate_gauss_scalar; frozen_dependencies: none
proof_shape: structureRHS: bind-only; escape_witness: none; consumers: EuclideanHypersurfaceGauss.structure_partial, EuclideanHypersurfaceGauss.dual_first_partial, EuclideanHypersurfaceGauss.dual_second_partial, EuclideanHypersurfaceGauss.ricci_of_structure, QuantumCubeRootScalarCurvatureMonotone.frame_structure, QuantumCubeRootScalarCurvatureMonotone.coordinate_ricci; frozen_dependencies: none
proof_shape: structure_partial: bind-only; escape_witness: none; consumers: EuclideanHypersurfaceGauss.dual_second_partial; frozen_dependencies: none
proof_shape: dual_first_partial: bind-only; escape_witness: none; consumers: EuclideanHypersurfaceGauss.dual_second_partial; frozen_dependencies: none
proof_shape: dual_second_partial: content; escape_witness: EuclideanHypersurfaceGauss.dual_second_partial; consumers: EuclideanHypersurfaceGauss.ricci_of_structure; frozen_dependencies: none
proof_shape: ricci_of_structure: content; escape_witness: EuclideanHypersurfaceGauss.ricci_of_structure; consumers: QuantumCubeRootScalarCurvatureMonotone.coordinate_ricci; frozen_dependencies: none
proof_shape: det_contDiffAt: bind-only; escape_witness: none; consumers: EuclideanHypersurfaceGauss.adjugate_entry_contDiffAt, EuclideanHypersurfaceGauss.inverse_entry_contDiffAt; frozen_dependencies: none
proof_shape: adjugate_entry_contDiffAt: bind-only; escape_witness: none; consumers: EuclideanHypersurfaceGauss.inverse_entry_contDiffAt; frozen_dependencies: none
proof_shape: inverse_entry_contDiffAt: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.inverse_metric_smooth; frozen_dependencies: none
-/


import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul

noncomputable section
open scoped BigOperators Topology
open Filter
namespace D5.S3.Geometry.AlphaGeometry.EuclideanHypersurfaceGauss

open Matrix

def christoffel {m : ℕ} (g : (Fin m → ℝ) → Matrix (Fin m) (Fin m) ℝ)
    (x : Fin m → ℝ) (k i j : Fin m) : ℝ :=
  (1/2 : ℝ) * ∑ l, (g x)⁻¹ k l *
    (fderiv ℝ (fun t => g t l j) x (Pi.single i 1) +
     fderiv ℝ (fun t => g t l i) x (Pi.single j 1) -
     fderiv ℝ (fun t => g t i j) x (Pi.single l 1))

def ricci {m : ℕ} (g : (Fin m → ℝ) → Matrix (Fin m) (Fin m) ℝ)
    (x : Fin m → ℝ) (i j : Fin m) : ℝ :=
  ∑ k, (fderiv ℝ (fun t => christoffel g t k i j) x (Pi.single k 1) -
    fderiv ℝ (fun t => christoffel g t k i k) x (Pi.single j 1) +
    ∑ l, (christoffel g x k k l * christoffel g x l i j -
      christoffel g x k j l * christoffel g x l i k))

def scalarCurvature {m : ℕ} (g : (Fin m → ℝ) → Matrix (Fin m) (Fin m) ℝ)
    (x : Fin m → ℝ) : ℝ := ∑ i, ∑ j, (g x)⁻¹ i j * ricci g x i j

section
set_option backward.isDefEq.respectTransparency false
open Matrix

private lemma scalar_as_matrix_trace {m : ℕ} (g : (Fin m → ℝ) → Matrix (Fin m) (Fin m) ℝ)
    (x : Fin m → ℝ) : scalarCurvature g x = ((g x)⁻¹ᵀ * (Matrix.of (fun i j => ricci g x i j))).trace := by
  change (∑ i, ∑ j, (g x)⁻¹ i j * ricci g x i j) =
    ∑ i, ∑ j, (g x)⁻¹ j i * ricci g x j i
  rw [Finset.sum_comm]

theorem coordinate_gauss_scalar_of_ricci {m : ℕ}
    (g : (Fin m → ℝ) → Matrix (Fin m) (Fin m) ℝ) (x : Fin m → ℝ)
    (b : Matrix (Fin m) (Fin m) ℝ) (hg : (g x).IsSymm)
    (hRicci : (Matrix.of (fun i j => ricci g x i j)) = ((g x)⁻¹*b).trace • b - b*(g x)⁻¹*b) :
    scalarCurvature g x = ((g x)⁻¹*b).trace^2 - (((g x)⁻¹*b)^2).trace := by
  rw [scalar_as_matrix_trace, hg.inv.eq,hRicci,Matrix.mul_sub,Matrix.mul_smul,
    Matrix.trace_sub,Matrix.trace_smul]
  have he : (g x)⁻¹*(b*(g x)⁻¹*b) = ((g x)⁻¹*b)^2 := by noncomm_ring
  rw [he]
  simp only [smul_eq_mul,pow_two]

end

section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Filter
variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def structureRHS (e : Fin m → (Fin m → ℝ) → E) (N : (Fin m → ℝ) → E)
    (Γ : (Fin m → ℝ) → Fin m → Fin m → Fin m → ℝ)
    (b : (Fin m → ℝ) → Fin m → Fin m → ℝ) (i j : Fin m) (t : (Fin m → ℝ)) : E :=
  (∑ l, Γ t l i j • e l t) + b t i j • N t

private lemma structure_partial (e : Fin m → (Fin m → ℝ) → E) (N : (Fin m → ℝ) → E)
    (Γ : (Fin m → ℝ) → Fin m → Fin m → Fin m → ℝ)
    (b : (Fin m → ℝ) → Fin m → Fin m → ℝ) (x : (Fin m → ℝ))
    (he : ∀ l, DifferentiableAt ℝ (e l) x) (hN : DifferentiableAt ℝ N x)
    (hΓ : ∀ l i j, DifferentiableAt ℝ (fun t => Γ t l i j) x)
    (hb : ∀ i j, DifferentiableAt ℝ (fun t => b t i j) x) (i j k : Fin m) :
    fderiv ℝ (structureRHS e N Γ b i j) x (Pi.single k 1) =
      (∑ l, (fderiv ℝ (fun t => Γ t l i j) x (Pi.single k 1) • e l x +
        Γ x l i j • fderiv ℝ (e l) x (Pi.single k 1))) +
      fderiv ℝ (fun t => b t i j) x (Pi.single k 1) • N x +
        b x i j • fderiv ℝ N x (Pi.single k 1) := by
  have hp := (HasFDerivAt.fun_sum (u := Finset.univ)
    (fun l _ => (hΓ l i j).hasFDerivAt.smul (he l).hasFDerivAt)).add
      ((hb i j).hasFDerivAt.smul hN.hasFDerivAt)
  rw [show structureRHS e N Γ b i j = (fun t => (∑ l, Γ t l i j • e l t) + b t i j • N t) from rfl]
  change HasFDerivAt (structureRHS e N Γ b i j) _ x at hp
  rw [← show structureRHS e N Γ b i j = (fun t => (∑ l, Γ t l i j • e l t) + b t i j • N t) from rfl]
  rw [hp.fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.smul_apply]
  simp only [Finset.sum_add_distrib]
  abel

private lemma dual_first_partial (e : Fin m → (Fin m → ℝ) → E) (N : (Fin m → ℝ) → E)
    (Γ : (Fin m → ℝ) → Fin m → Fin m → Fin m → ℝ)
    (b : (Fin m → ℝ) → Fin m → Fin m → ℝ) (x : (Fin m → ℝ)) (a : Fin m → E →L[ℝ] ℝ)
    (ha : ∀ k l, a k (e l x) = if k=l then 1 else 0)
    (hN : ∀ k, a k (N x) = 0)
    (hstr : ∀ i j, fderiv ℝ (e i) x (Pi.single j 1) = structureRHS e N Γ b i j x)
    (k i j : Fin m) : a k (fderiv ℝ (e i) x (Pi.single j 1)) = Γ x k i j := by
  rw [hstr]
  simp [structureRHS,map_sum,map_add,map_smul,ha,hN]

private lemma dual_second_partial (e : Fin m → (Fin m → ℝ) → E) (N : (Fin m → ℝ) → E)
    (Γ : (Fin m → ℝ) → Fin m → Fin m → Fin m → ℝ)
    (b : (Fin m → ℝ) → Fin m → Fin m → ℝ) (x : (Fin m → ℝ)) (a : Fin m → E →L[ℝ] ℝ)
    (he : ∀ l, DifferentiableAt ℝ (e l) x) (hN : DifferentiableAt ℝ N x)
    (hΓ : ∀ l i j, DifferentiableAt ℝ (fun t => Γ t l i j) x)
    (hb : ∀ i j, DifferentiableAt ℝ (fun t => b t i j) x)
    (ha : ∀ k l, a k (e l x) = if k=l then 1 else 0)
    (haN : ∀ k, a k (N x) = 0)
    (hstr : ∀ i j, (fun t => fderiv ℝ (e i) t (Pi.single j 1)) =ᶠ[𝓝 x] structureRHS e N Γ b i j)
    (l i j k : Fin m) :
    a l (fderiv ℝ (fun t => fderiv ℝ (e i) t (Pi.single j 1)) x (Pi.single k 1)) =
      fderiv ℝ (fun t => Γ t l i j) x (Pi.single k 1) +
        (∑ r, Γ x r i j * Γ x l r k) + b x i j * a l (fderiv ℝ N x (Pi.single k 1)) := by
  rw [(hstr i j).fderiv_eq,structure_partial e N Γ b x he hN hΓ hb]
  have hs : ∀ i j, fderiv ℝ (e i) x (Pi.single j 1) = structureRHS e N Γ b i j x :=
    fun i j => (hstr i j).eq_of_nhds
  simp only [map_add,map_sum,map_smul,smul_eq_mul,ha,haN]
  have hf (r : Fin m) : a l (fderiv ℝ (e r) x (Pi.single k 1)) = Γ x l r k :=
    dual_first_partial e N Γ b x a ha haN hs l r k
  simp_rw [hf]
  simp [Finset.sum_add_distrib]

theorem ricci_of_structure
    (g : (Fin m → ℝ) → Matrix (Fin m) (Fin m) ℝ)
    (e : Fin m → (Fin m → ℝ) → E) (N : (Fin m → ℝ) → E)
    (b : (Fin m → ℝ) → Fin m → Fin m → ℝ) (x : (Fin m → ℝ)) (a : Fin m → E →L[ℝ] ℝ)
    (he : ∀ l, DifferentiableAt ℝ (e l) x) (hN : DifferentiableAt ℝ N x)
    (hΓ : ∀ l i j, DifferentiableAt ℝ (fun t => christoffel g t l i j) x)
    (hb : ∀ i j, DifferentiableAt ℝ (fun t => b t i j) x)
    (ha : ∀ k l, a k (e l x) = if k=l then 1 else 0)
    (haN : ∀ k, a k (N x) = 0)
    (hstr : ∀ i j, (fun t => fderiv ℝ (e i) t (Pi.single j 1)) =ᶠ[𝓝 x]
      structureRHS e N (christoffel g) b i j)
    (hmixed : ∀ i j k,
      fderiv ℝ (fun t => fderiv ℝ (e i) t (Pi.single j 1)) x (Pi.single k 1) =
      fderiv ℝ (fun t => fderiv ℝ (e i) t (Pi.single k 1)) x (Pi.single j 1))
    (hΓsym : ∀ k i j, christoffel g x k i j = christoffel g x k j i)
    (hshape : ∀ k j, a k (fderiv ℝ N x (Pi.single j 1)) = -∑ l, (g x)⁻¹ k l*b x j l)
    (i j : Fin m) :
    ricci g x i j = b x i j * (∑ k, ∑ l, (g x)⁻¹ k l*b x k l) -
      ∑ k, ∑ l, b x i k*(g x)⁻¹ k l*b x j l := by
  have hcoeff (k : Fin m) :
      fderiv ℝ (fun t => christoffel g t k i j) x (Pi.single k 1) -
        fderiv ℝ (fun t => christoffel g t k i k) x (Pi.single j 1) +
        (∑ l, (christoffel g x k k l*christoffel g x l i j -
          christoffel g x k j l*christoffel g x l i k)) =
      b x i j*(∑ l, (g x)⁻¹ k l*b x k l) -
        b x i k*(∑ l, (g x)⁻¹ k l*b x j l) := by
    have h1 := dual_second_partial e N (christoffel g) b x a he hN hΓ hb ha haN hstr k i j k
    have h2 := dual_second_partial e N (christoffel g) b x a he hN hΓ hb ha haN hstr k i k j
    have hv := (h1.symm.trans (congrArg (a k) (hmixed i j k))).trans h2
    have hp1 : (∑ r, christoffel g x r i j*christoffel g x k r k) =
        ∑ r, christoffel g x k k r*christoffel g x r i j := by
      apply Finset.sum_congr rfl
      intro r _
      rw [hΓsym k r k]
      ring
    have hp2 : (∑ r, christoffel g x r i k*christoffel g x k r j) =
        ∑ r, christoffel g x k j r*christoffel g x r i k := by
      apply Finset.sum_congr rfl
      intro r _
      rw [hΓsym k r j]
      ring
    rw [hp1,hp2,hshape,hshape] at hv
    rw [Finset.sum_sub_distrib]
    linarith
  unfold ricci
  simp_rw [hcoeff]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

end

section
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}

private lemma det_contDiffAt (g : E → Matrix (Fin m) (Fin m) ℝ) (x : E)
    (hg : ∀ i j, ContDiffAt ℝ (⊤ : ℕ∞) (fun t => g t i j) x) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun t => (g t).det) x := by
  simp_rw [Matrix.det_apply']
  apply ContDiffAt.sum
  intro σ _
  apply contDiffAt_const.mul
  apply contDiffAt_prod
  intro i _
  exact hg (σ i) i

private lemma adjugate_entry_contDiffAt (g : E → Matrix (Fin m) (Fin m) ℝ) (x : E)
    (hg : ∀ i j, ContDiffAt ℝ (⊤ : ℕ∞) (fun t => g t i j) x) (i j : Fin m) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun t => (g t).adjugate i j) x := by
  simp_rw [Matrix.adjugate_apply]
  apply det_contDiffAt
  intro a b
  by_cases h : a = j
  · subst a
    simp only [Matrix.updateRow_self]
    change ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : E => (Pi.single i (1 : ℝ) : Fin m → ℝ) b) x
    exact contDiffAt_const
  · simpa [Matrix.updateRow_apply,h] using hg a b

lemma inverse_entry_contDiffAt (g : E → Matrix (Fin m) (Fin m) ℝ) (x : E)
    (hg : ∀ i j, ContDiffAt ℝ (⊤ : ℕ∞) (fun t => g t i j) x)
    (hdet : (g x).det ≠ 0) (i j : Fin m) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun t => (g t)⁻¹ i j) x := by
  simp_rw [Matrix.inv_def,Ring.inverse_eq_inv',Matrix.smul_apply,smul_eq_mul]
  exact ((det_contDiffAt g x hg).inv hdet).mul (adjugate_entry_contDiffAt g x hg i j)

end

end D5.S3.Geometry.AlphaGeometry.EuclideanHypersurfaceGauss
