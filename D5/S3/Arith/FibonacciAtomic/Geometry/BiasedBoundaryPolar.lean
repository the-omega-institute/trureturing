/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPolar
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPolar
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Real polar coordinates identify the original form and operator domains and total resolvent. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySpectralForm
import Mathlib.Analysis.Normed.Lp.lpHolder

/-! The original real polar realization and its two distinct range domains. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryPolar

open FiniteSourceHardy (H)
open BiasedBoundaryTrace (G J)
open BiasedBoundaryPathSplit (constG)
open BiasedBoundaryCentering (Pi C mean centered_suffix_residual)
open BiasedBoundaryStopping (G0)
open BiasedBoundaryFreeRootForm (D K Sigma mean_Pi Pi_idem adjoint_mem_K
  weakGraph free_root_least_energy free_root_variational_graph represented_of_centered)
open BiasedBoundaryOperator (boundaryOperator boundaryResolvent boundaryCovariance
  actual_self_adjoint_realization actual_compact_resolvent)
open BiasedBoundarySpectralForm (actual_spectral_form_energy)
open InnerProductSpace Filter
open scoped Topology ENNReal

private def polar (b : HilbertBasis ℕ ℝ G0) (k : HilbertBasis ℕ ℝ K) :
    K ≃ₗᵢ[ℝ] G0 := k.repr.trans b.repr.symm

private def traceK : K →L[ℝ] G0 :=
  (C.codRestrict G0 (fun z => mean_Pi (J z))).comp K.subtypeL

private def root (b : HilbertBasis ℕ ℝ G0) (k : HilbertBasis ℕ ℝ K) : K →L[ℝ] K :=
  (polar b k).symm.toLinearIsometry.toContinuousLinearMap.comp traceK

private def covarianceK : K →L[ℝ] K :=
  (Sigma.codRestrict K (fun z => adjoint_mem_K (C z))).comp K.subtypeL

private def inverseOneAdd (k : HilbertBasis ℕ ℝ K) (mu : ℕ → ℝ)
    (hp : ∀ i, 0 < mu i) : K →L[ℝ] K :=
  k.repr.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((lp.mapCLM 2 (fun i : ℕ => (1 + mu i)⁻¹ • (1 : ℝ →L[ℝ] ℝ))
      (by norm_num : (0 : ℝ) ≤ 1) (fun i => by
        rw [norm_smul, norm_one, mul_one, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr (by linarith [hp i]))]
        exact inv_le_one_of_one_le₀ (by linarith [hp i]))).comp
      k.repr.toLinearIsometry.toContinuousLinearMap)

private theorem inverseOneAdd_coeff (k : HilbertBasis ℕ ℝ K) (mu : ℕ → ℝ)
    (hp : ∀ i, 0 < mu i) (x : K) (i : ℕ) :
    k.repr (inverseOneAdd k mu hp x) i = (1 + mu i)⁻¹ * k.repr x i := by
  simp [inverseOneAdd]

private theorem polar_coeff (b : HilbertBasis ℕ ℝ G0) (k : HilbertBasis ℕ ℝ K)
    (x : K) (i : ℕ) : b.repr (polar b k x) i = k.repr x i := by
  simp [polar]

private theorem adjoint_basis (b : HilbertBasis ℕ ℝ G0) (k : HilbertBasis ℕ ℝ K)
    (mu : ℕ → ℝ) (hp : ∀ i, 0 < mu i)
    (hk : ∀ i, Sigma (k i).val = mu i • (k i).val)
    (hC : ∀ i, C (k i).val = Real.sqrt (mu i) • (b i).val) (i : ℕ) :
    C.adjoint (b i).val = Real.sqrt (mu i) • (k i).val := by
  apply smul_right_injective (M := H) (Real.sqrt_pos.mpr (hp i)).ne'
  calc
    Real.sqrt (mu i) • C.adjoint (b i).val =
        C.adjoint (Real.sqrt (mu i) • (b i).val) := (map_smul _ _ _).symm
    _ = C.adjoint (C (k i).val) := by rw [hC]
    _ = Sigma (k i).val := rfl
    _ = mu i • (k i).val := hk i
    _ = Real.sqrt (mu i) • (Real.sqrt (mu i) • (k i).val) := by
      rw [smul_smul, ← pow_two, Real.sq_sqrt (hp i).le]

private theorem trace_coeff (b : HilbertBasis ℕ ℝ G0) (k : HilbertBasis ℕ ℝ K)
    (mu : ℕ → ℝ) (hp : ∀ i, 0 < mu i)
    (hk : ∀ i, Sigma (k i).val = mu i • (k i).val)
    (hC : ∀ i, C (k i).val = Real.sqrt (mu i) • (b i).val) (x : K) (i : ℕ) :
    b.repr (traceK x) i = Real.sqrt (mu i) * k.repr x i := by
  rw [b.repr_apply_apply, k.repr_apply_apply]
  change inner ℝ (b i).val (C x.val) =
    Real.sqrt (mu i) * inner ℝ (k i).val x.val
  rw [← C.adjoint_inner_left, adjoint_basis b k mu hp hk hC, real_inner_smul_left]

private theorem adjoint_coeff (b : HilbertBasis ℕ ℝ G0) (k : HilbertBasis ℕ ℝ K)
    (mu : ℕ → ℝ)
    (hC : ∀ i, C (k i).val = Real.sqrt (mu i) • (b i).val) (u : G0) (i : ℕ) :
    k.repr ⟨C.adjoint u.val, adjoint_mem_K u.val⟩ i =
      Real.sqrt (mu i) * b.repr u i := by
  rw [k.repr_apply_apply, b.repr_apply_apply]
  change inner ℝ (k i).val (C.adjoint u.val) =
    Real.sqrt (mu i) * inner ℝ (b i).val u.val
  rw [C.adjoint_inner_right, hC, real_inner_smul_left]

private theorem root_coeff (b : HilbertBasis ℕ ℝ G0) (k : HilbertBasis ℕ ℝ K)
    (mu : ℕ → ℝ) (hp : ∀ i, 0 < mu i)
    (hk : ∀ i, Sigma (k i).val = mu i • (k i).val)
    (hC : ∀ i, C (k i).val = Real.sqrt (mu i) • (b i).val) (x : K) (i : ℕ) :
    k.repr (root b k x) i = Real.sqrt (mu i) * k.repr x i := by
  change k.repr ((polar b k).symm (traceK x)) i = _
  simpa [polar] using trace_coeff b k mu hp hk hC x i

private theorem covariance_coeff (b : HilbertBasis ℕ ℝ G0) (k : HilbertBasis ℕ ℝ K)
    (mu : ℕ → ℝ) (hp : ∀ i, 0 < mu i)
    (hk : ∀ i, Sigma (k i).val = mu i • (k i).val)
    (hC : ∀ i, C (k i).val = Real.sqrt (mu i) • (b i).val) (x : K) (i : ℕ) :
    k.repr (covarianceK x) i = mu i * k.repr x i := by
  change k.repr ⟨C.adjoint (traceK x).val, adjoint_mem_K _⟩ i = _
  rw [adjoint_coeff b k mu hC, trace_coeff b k mu hp hk hC,
    ← mul_assoc, ← pow_two, Real.sq_sqrt (hp i).le]

private theorem covariance_polar (b : HilbertBasis ℕ ℝ G0) (k : HilbertBasis ℕ ℝ K)
    (mu : ℕ → ℝ) (hp : ∀ i, 0 < mu i)
    (hk : ∀ i, Sigma (k i).val = mu i • (k i).val)
    (hC : ∀ i, C (k i).val = Real.sqrt (mu i) • (b i).val) (x : K) :
    boundaryCovariance (polar b k x).val = (polar b k (covarianceK x)).val := by
  have he : (⟨boundaryCovariance (polar b k x).val,
      mean_Pi (J (C.adjoint (polar b k x).val))⟩ : G0) =
      polar b k (covarianceK x) := by
    apply b.repr.injective
    apply lp.ext
    funext i
    change b.repr (traceK ⟨C.adjoint (polar b k x).val, adjoint_mem_K _⟩) i = _
    rw [trace_coeff b k mu hp hk hC, adjoint_coeff b k mu hC,
      polar_coeff, polar_coeff, covariance_coeff b k mu hp hk hC,
      ← mul_assoc, ← pow_two, Real.sq_sqrt (hp i).le]
  exact congrArg Subtype.val he

private theorem polar_root (b : HilbertBasis ℕ ℝ G0) (k : HilbertBasis ℕ ℝ K)
    (x : K) : (polar b k (root b k x)).val = C x.val := by
  change ((polar b k) ((polar b k).symm (traceK x))).val = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

private theorem square_root (b : HilbertBasis ℕ ℝ G0) (k : HilbertBasis ℕ ℝ K)
    (mu : ℕ → ℝ) (hp : ∀ i, 0 < mu i)
    (hk : ∀ i, Sigma (k i).val = mu i • (k i).val)
    (hC : ∀ i, C (k i).val = Real.sqrt (mu i) • (b i).val) (x : K) :
    root b k (root b k x) = covarianceK x := by
  apply k.repr.injective
  apply lp.ext
  funext i
  rw [root_coeff b k mu hp hk hC, root_coeff b k mu hp hk hC,
    covariance_coeff b k mu hp hk hC, ← mul_assoc, ← pow_two,
    Real.sq_sqrt (hp i).le]

private theorem adjoint_polar (b : HilbertBasis ℕ ℝ G0) (k : HilbertBasis ℕ ℝ K)
    (mu : ℕ → ℝ) (hp : ∀ i, 0 < mu i)
    (hk : ∀ i, Sigma (k i).val = mu i • (k i).val)
    (hC : ∀ i, C (k i).val = Real.sqrt (mu i) • (b i).val) (u : G0) :
    C.adjoint u.val = (root b k ((polar b k).symm u)).val := by
  have he : (⟨C.adjoint u.val, adjoint_mem_K _⟩ : K) =
      root b k ((polar b k).symm u) := by
    apply k.repr.injective
    apply lp.ext
    funext i
    rw [adjoint_coeff b k mu hC, root_coeff b k mu hp hk hC]
    simp [polar]
  exact congrArg Subtype.val he

private theorem form_domain (b : HilbertBasis ℕ ℝ G0) (k : HilbertBasis ℕ ℝ K)
    (u : G0) : u.val ∈ D ↔ ∃ x : K, polar b k (root b k x) = u := by
  constructor
  · intro hu
    let F : D := ⟨u.val, hu⟩
    let x : K := ⟨BiasedBoundaryFreeRootForm.lift F, (free_root_least_energy F).1⟩
    refine ⟨x, Subtype.ext ?_⟩
    rw [polar_root]
    have he := (free_root_least_energy F).2.1
    have hi : Pi u.val = u.val := by
      rw [centered_suffix_residual.2.2.1, show mean u.val = 0 from u.property,
        map_zero, sub_zero]
    exact he.trans hi
  · rintro ⟨x, hx⟩
    apply represented_of_centered u.val x.val
    rw [← polar_root b k x, hx]
    rw [centered_suffix_residual.2.2.1, show mean u.val = 0 from u.property,
      map_zero, sub_zero]

private theorem graph_polar (b : HilbertBasis ℕ ℝ G0) (k : HilbertBasis ℕ ℝ K)
    (mu : ℕ → ℝ) (hp : ∀ i, 0 < mu i)
    (hk : ∀ i, Sigma (k i).val = mu i • (k i).val)
    (hC : ∀ i, C (k i).val = Real.sqrt (mu i) • (b i).val) (u h : G) :
    (u,h) ∈ boundaryOperator.graph ↔
      ∃ x : K, h = (polar b k x).val ∧ Pi u = (polar b k (covarianceK x)).val := by
  rw [actual_self_adjoint_realization.2.2.2.2.2.2.1,
    free_root_variational_graph.2.2.2.2.2]
  constructor
  · rintro ⟨hh, hu⟩
    let v : G0 := ⟨h, hh⟩
    let x := (polar b k).symm v
    have hx : polar b k x = v := (polar b k).apply_symm_apply v
    refine ⟨x, (congrArg Subtype.val hx).symm, ?_⟩
    rw [hu, map_add, BiasedBoundaryCentering.Pi_const, zero_add]
    change Pi (Pi (J (C.adjoint h))) = _
    rw [Pi_idem]
    change boundaryCovariance h = _
    rw [← congrArg Subtype.val hx]
    exact covariance_polar b k mu hp hk hC x
  · rintro ⟨x, rfl, hu⟩
    refine ⟨(polar b k x).property, ?_⟩
    rw [← covariance_polar b k mu hp hk hC] at hu
    change Pi u = C (C.adjoint (polar b k x).val) at hu
    rw [← hu, centered_suffix_residual.2.2.1]
    abel

private theorem operator_domain (b : HilbertBasis ℕ ℝ G0) (k : HilbertBasis ℕ ℝ K)
    (mu : ℕ → ℝ) (hp : ∀ i, 0 < mu i)
    (hk : ∀ i, Sigma (k i).val = mu i • (k i).val)
    (hC : ∀ i, C (k i).val = Real.sqrt (mu i) • (b i).val) (u : G0) :
    u.val ∈ boundaryOperator.domain ↔ ∃ x : K, polar b k (covarianceK x) = u := by
  rw [LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨h, hh⟩
    obtain ⟨x, _, hx⟩ := (graph_polar b k mu hp hk hC _ _).mp hh
    refine ⟨x, Subtype.ext ?_⟩
    rw [← hx, centered_suffix_residual.2.2.1,
      show mean u.val = 0 from u.property, map_zero, sub_zero]
  · rintro ⟨x, hx⟩
    refine ⟨(polar b k x).val, (graph_polar b k mu hp hk hC _ _).mpr ⟨x,rfl,?_⟩⟩
    rw [hx, centered_suffix_residual.2.2.1,
      show mean u.val = 0 from u.property, map_zero, sub_zero]

private theorem shift_inverse (b : HilbertBasis ℕ ℝ G0) (k : HilbertBasis ℕ ℝ K)
    (mu : ℕ → ℝ) (hp : ∀ i, 0 < mu i)
    (hk : ∀ i, Sigma (k i).val = mu i • (k i).val)
    (hC : ∀ i, C (k i).val = Real.sqrt (mu i) • (b i).val) (x : K) :
    inverseOneAdd k mu hp x + covarianceK (inverseOneAdd k mu hp x) = x ∧
      inverseOneAdd k mu hp (x + covarianceK x) = x := by
  constructor <;> apply k.repr.injective <;> apply lp.ext <;> funext i
  · simp only [map_add, lp.coeFn_add, Pi.add_apply,
      covariance_coeff b k mu hp hk hC, inverseOneAdd_coeff]
    have hn : 1 + mu i ≠ 0 := by linarith [hp i]
    field_simp
    <;> ring
  · simp only [inverseOneAdd_coeff, map_add, lp.coeFn_add, Pi.add_apply,
      covariance_coeff b k mu hp hk hC]
    have hn : 1 + mu i ≠ 0 := by linarith [hp i]
    field_simp
    <;> ring

private theorem resolvent_polar (b : HilbertBasis ℕ ℝ G0) (k : HilbertBasis ℕ ℝ K)
    (mu : ℕ → ℝ) (hp : ∀ i, 0 < mu i)
    (hk : ∀ i, Sigma (k i).val = mu i • (k i).val)
    (hC : ∀ i, C (k i).val = Real.sqrt (mu i) • (b i).val) (F : G) :
    boundaryResolvent F = constG (mean F) +
      (polar b k (covarianceK (inverseOneAdd k mu hp
        ((polar b k).symm ⟨Pi F, mean_Pi F⟩)))).val := by
  let x := inverseOneAdd k mu hp ((polar b k).symm ⟨Pi F, mean_Pi F⟩)
  let u := constG (mean F) + (polar b k (covarianceK x)).val
  let h := (polar b k x).val
  have hg : (u,h) ∈ boundaryOperator.graph := by
    apply (graph_polar b k mu hp hk hC u h).mpr
    refine ⟨x,rfl,?_⟩
    simp only [u, map_add, BiasedBoundaryCentering.Pi_const, zero_add]
    rw [centered_suffix_residual.2.2.1,
      show mean (polar b k (covarianceK x)).val = 0 from (polar b k (covarianceK x)).property,
      map_zero, sub_zero]
  have hs : u + h = F := by
    have he := congrArg (fun y : K => (polar b k y).val)
      (shift_inverse b k mu hp hk hC ((polar b k).symm ⟨Pi F, mean_Pi F⟩)).1
    simp only [map_add, Submodule.coe_add, LinearIsometryEquiv.apply_symm_apply] at he
    change (polar b k x).val + (polar b k (covarianceK x)).val = Pi F at he
    dsimp [u,h]
    rw [add_assoc, add_comm (polar b k (covarianceK x)).val, he,
      centered_suffix_residual.2.2.1]
    abel
  have he := (actual_compact_resolvent.2.1 u h).mp hg
  rw [hs] at he
  exact he

/-- On the actual real carriers, the paired bases give a unitary W, a bounded
positive square root S and covariance T, and the total bounded inverse of I+T.
Their ranges are the original centered form and operator domains. -/
theorem actual_polar_domains_resolvent :
    ∃ (b : HilbertBasis ℕ ℝ G0) (k : HilbertBasis ℕ ℝ K) (mu : ℕ → ℝ)
      (W : K ≃ₗᵢ[ℝ] G0) (S T R : K →L[ℝ] K),
      (∀ i, 0 < mu i) ∧
      (∀ x : K, ∀ i, b.repr (W x) i = k.repr x i) ∧
      (∀ x : K, ∀ i, k.repr (S x) i = Real.sqrt (mu i) * k.repr x i) ∧
      (∀ x : K, ∀ i, k.repr (T x) i = mu i * k.repr x i) ∧
      (∀ x : K, ∀ i, k.repr (R x) i = (1 + mu i)⁻¹ * k.repr x i) ∧
      (∀ x : K, (T x).val = Sigma x.val) ∧
      (∀ x : K, S (S x) = T x) ∧
      (∀ x : K, (W (S x)).val = C x.val) ∧
      (∀ u : G0, C.adjoint u.val = (S (W.symm u)).val) ∧
      (∀ u : G0, u.val ∈ D ↔ ∃ x : K, W (S x) = u) ∧
      (∀ u : G0, u.val ∈ boundaryOperator.domain ↔ ∃ x : K, W (T x) = u) ∧
      (∀ u h : G, (u,h) ∈ boundaryOperator.graph ↔
        ∃ x : K, h = (W x).val ∧ Pi u = (W (T x)).val) ∧
      (∀ x : K, R x + T (R x) = x ∧ R (x + T x) = x) ∧
      (∀ F : G, boundaryResolvent F = constG (mean F) +
        (W (T (R (W.symm ⟨Pi F,mean_Pi F⟩)))).val) := by
  obtain ⟨b,k,mu,hp,_,_,_,_,_,hk,hC,_,_,_⟩ := actual_spectral_form_energy
  exact ⟨b,k,mu,polar b k,root b k,covarianceK,inverseOneAdd k mu hp,hp,
    polar_coeff b k,root_coeff b k mu hp hk hC,covariance_coeff b k mu hp hk hC,
    inverseOneAdd_coeff k mu hp,(fun _ => rfl),square_root b k mu hp hk hC,
    polar_root b k,adjoint_polar b k mu hp hk hC,form_domain b k,
    operator_domain b k mu hp hk hC,graph_polar b k mu hp hk hC,
    shift_inverse b k mu hp hk hC,resolvent_polar b k mu hp hk hC⟩

#print axioms actual_polar_domains_resolvent

end D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryPolar
