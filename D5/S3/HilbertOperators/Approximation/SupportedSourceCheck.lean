import D5.S3.HilbertOperators.Approximation.SupportedSingular
import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCounting
import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryPolar
import Mathlib.Analysis.PSeries

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupportedSourceCheck
open D5.S3.Arith.FibonacciAtomic.Geometry
open FiniteSourceHardy (H)
open BiasedBoundaryTrace (G b)
open BiasedBoundaryStopping (G0)
open BiasedBoundaryCentering (C)
open BiasedBoundaryFreeRootForm (K Sigma adjoint_mem_K C_project)
open BiasedBoundaryOperator (centeredTrace)
open BiasedBoundaryPolar (traceK trace_coeff covarianceK covariance_coeff)
open BiasedBoundaryCounting (actual_spectral_counting B positiveEigenvalue)
open D5.S3.HilbertOperators.Approximation.SupportedSingular
open Filter
open scoped Topology

example : ∃ (e : HilbertBasis ℕ ℝ G0) (k : HilbertBasis ℕ ℝ K) (mu : ℕ → ℝ),
    (∀ i, 0 < mu i) ∧ Antitone mu ∧ Tendsto mu atTop (𝓝 0) ∧
    (∀ i, Sigma (k i).val = mu i • (k i).val) ∧
    (∀ i, C (k i).val = Real.sqrt (mu i) • (e i).val) ∧
    (∀ n, approximationNumber Sigma n = mu n ∧
      approximationNumber centeredTrace n = Real.sqrt (mu n) ∧
      approximationNumber C n = Real.sqrt (mu n)) := by
  obtain ⟨hB,e,k,mu,hp,ha,ht,hmi,hti,hg,hk,hC,rest⟩ := actual_spectral_counting
  have hcenter (x : H) : centeredTrace x = traceK (K.orthogonalProjectionOnto x) := by
    apply Subtype.ext
    exact (C_project x).symm
  have htrace (x : H) (i : ℕ) :
      e.repr (centeredTrace x) i = Real.sqrt (mu i) * k.repr (K.orthogonalProjectionOnto x) i := by
    rw [hcenter]
    exact trace_coeff e k mu hp hk hC _ i
  let A : H →L[ℝ] K := Sigma.codRestrict K (fun x => adjoint_mem_K (C x))
  have hcov (x : H) (i : ℕ) :
      k.repr (A x) i = mu i * k.repr (K.orthogonalProjectionOnto x) i := by
    have he : A x = covarianceK (K.orthogonalProjectionOnto x) := by
      apply Subtype.ext
      change C.adjoint (C x) = C.adjoint (C (K.starProjection x))
      rw [C_project]
    rw [he]
    exact covariance_coeff e k mu hp hk hC _ i
  have hasqrt : Antitone (fun i => Real.sqrt (mu i)) := fun i j hij => Real.sqrt_le_sqrt (ha hij)
  refine ⟨e,k,mu,hp,ha,ht,hk,hC,?_⟩
  intro n
  refine ⟨?_,?_,?_⟩
  · exact approximationNumber_eq_supported Sigma A K.subtypeₗᵢ K k k mu
      (fun i => (hp i).le) ha (fun _ => rfl) hcov n
  · exact approximationNumber_eq_supported centeredTrace centeredTrace (LinearIsometry.id ℝ G0)
      K k e (fun i => Real.sqrt (mu i)) (fun i => Real.sqrt_nonneg _) hasqrt
      (fun _ => rfl) htrace n
  · exact approximationNumber_eq_supported C centeredTrace G0.subtypeₗᵢ
      K k e (fun i => Real.sqrt (mu i)) (fun i => Real.sqrt_nonneg _) hasqrt
      (fun _ => rfl) htrace n
end SupportedSourceCheck
