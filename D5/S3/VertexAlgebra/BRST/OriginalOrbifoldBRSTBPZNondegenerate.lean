/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTBPZNondegenerate
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTBPZNondegenerate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.TensorProduct.Basis]
   utility: none
   digest: Trivial left and right radicals of the original full matter-ghost BPZ form. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTBPZWard
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! Each algebraic tensor has a finite expansion in a basis of its left factor.
Pairing against pure tensors detects each coefficient through the factor forms. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTBPZNondegenerate

noncomputable section

open OriginalOrbifoldCriticalMatter (Orbifold Matter State hyperbolicData hyperbolic_gram)
open OriginalOrbifoldMatterBPZ (fixedBPZ negativeBPZ orbifoldBPZ hyperbolicBPZ matterBPZ
  fixedBPZ_nondegenerate negativeBPZ_nondegenerate)
open OriginalOrbifoldBRSTGhostBPZ (beta beta_left_radical beta_right_radical)
open OriginalOrbifoldBRSTBPZWard (betaTotal)
open SourceBPZ.OriginalSourcePairing (sourcePairing_nondegenerate)

private theorem tensor_separatingLeft
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (B : LinearMap.BilinForm K V) (C : LinearMap.BilinForm K W)
    (D : LinearMap.BilinForm K (V ⊗[K] W))
    (hB : B.SeparatingLeft) (hC : C.SeparatingLeft)
    (hPair : ∀ (x : V) (u : W) (y : V) (v : W),
      D (x ⊗ₜ[K] u) (y ⊗ₜ[K] v) = C u v • B x y) :
    D.SeparatingLeft := by
  classical
  let basis := Module.Basis.ofVectorSpace K V
  intro x hx
  obtain ⟨coeff, rfl⟩ := TensorProduct.eq_repr_basis_left basis x
  have contraction_zero (v : W) :
      (∑ i ∈ coeff.support, C (coeff i) v • basis i) = 0 := by
    apply hB
    intro y
    let test : V ⊗[K] W →ₗ[K] K := D.flip (y ⊗ₜ[K] v)
    calc
      B (∑ i ∈ coeff.support, C (coeff i) v • basis i) y =
          ∑ i ∈ coeff.support, C (coeff i) v • B (basis i) y := by
        change B.flip y (∑ i ∈ coeff.support, C (coeff i) v • basis i) = _
        rw [map_sum]
        exact Finset.sum_congr rfl (fun i _ => (B.flip y).map_smul _ _)
      _ = test (coeff.sum fun i u => basis i ⊗ₜ[K] u) := by
        change _ = test (∑ i ∈ coeff.support, basis i ⊗ₜ[K] coeff i)
        rw [map_sum]
        exact Finset.sum_congr rfl (fun i _ => (hPair (basis i) (coeff i) y v).symm)
      _ = 0 := hx (y ⊗ₜ[K] v)
  have hcoeff : coeff = 0 := by
    apply Finsupp.ext
    intro i
    change coeff i = 0
    by_cases hi : i ∈ coeff.support
    · apply hC (coeff i)
      intro v
      have hcoord := congrArg (basis.coord i) (contraction_zero v)
      rw [map_sum, map_zero] at hcoord
      calc
        C (coeff i) v = ∑ j ∈ coeff.support, basis.coord i (C (coeff j) v • basis j) := by
          rw [Finset.sum_eq_single_of_mem i hi]
          · simp only [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
              Finsupp.single_eq_same, smul_eq_mul, mul_one]
          · intro j _ hji
            simp only [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
              Finsupp.single_eq_of_ne' hji, smul_zero]
        _ = 0 := hcoord
    · exact Finsupp.notMem_support_iff.mp hi
  rw [hcoeff, Finsupp.sum_zero_index]

private theorem tensor_nondegenerate
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (B : LinearMap.BilinForm K V) (C : LinearMap.BilinForm K W)
    (hB : B.Nondegenerate) (hC : C.Nondegenerate) :
    (B.tmul C).Nondegenerate := by
  have hPair (x y : V) (u v : W) : (B.tmul C) (x ⊗ₜ[K] u) (y ⊗ₜ[K] v) = C u v • B x y :=
    LinearMap.BilinForm.tensorDistrib_tmul K K B C x u y v
  refine ⟨tensor_separatingLeft B C (B.tmul C) hB.1 hC.1 (fun x u y v => hPair x y u v), ?_⟩
  change (B.tmul C).flip.SeparatingLeft
  exact tensor_separatingLeft B.flip C.flip (B.tmul C).flip hB.2 hC.2
    (fun x u y v => hPair y x v u)

/-- Testing against each sector separately detects both components of an orbifold state. -/
theorem orbifoldBPZ_nondegenerate : orbifoldBPZ.Nondegenerate := by
  constructor
  · intro x hx
    apply Prod.ext
    · exact fixedBPZ_nondegenerate.1 x.1 (fun y => by
        have h := hx ((y, 0) : Orbifold)
        change fixedBPZ x.1 y + negativeBPZ x.2 0 = 0 at h
        simpa only [map_zero, add_zero] using h)
    · exact negativeBPZ_nondegenerate.1 x.2 (fun y => by
        have h := hx ((0, y) : Orbifold)
        change fixedBPZ x.1 0 + negativeBPZ x.2 y = 0 at h
        simpa only [map_zero, zero_add] using h)
  · intro x hx
    apply Prod.ext
    · exact fixedBPZ_nondegenerate.2 x.1 (fun y => by
        have h := hx ((y, 0) : Orbifold)
        change fixedBPZ y x.1 + negativeBPZ 0 x.2 = 0 at h
        simpa only [map_zero, LinearMap.zero_apply, add_zero] using h)
    · exact negativeBPZ_nondegenerate.2 x.2 (fun y => by
        have h := hx ((0, y) : Orbifold)
        change fixedBPZ 0 x.1 + negativeBPZ y x.2 = 0 at h
        simpa only [map_zero, LinearMap.zero_apply, zero_add] using h)

/-- The hyperbolic source form is nondegenerate since its integral Gram determinant is `-1`. -/
theorem hyperbolicBPZ_nondegenerate : hyperbolicBPZ.Nondegenerate := by
  have hdet : hyperbolicData.G.det = -1 := by
    calc
      hyperbolicData.G.det = OrderedHyperbolicExtension.U.det :=
        congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M.det) hyperbolic_gram
      _ = -1 := by simp [OrderedHyperbolicExtension.U, Matrix.det_fin_two_of]
  apply sourcePairing_nondegenerate hyperbolicData
  rw [hdet]
  exact isUnit_neg_one

/-- The actual critical matter form has trivial left and right radicals. -/
theorem matterBPZ_nondegenerate : matterBPZ.Nondegenerate := by
  change (orbifoldBPZ.tmul hyperbolicBPZ).Nondegenerate
  exact tensor_nondegenerate orbifoldBPZ hyperbolicBPZ
    orbifoldBPZ_nondegenerate hyperbolicBPZ_nondegenerate

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

/-- The actual BPZ form on all algebraic matter-ghost states has trivial left and right radicals. -/
theorem betaTotal_nondegenerate : betaTotal.Nondegenerate := by
  change (matterBPZ.tmul beta).Nondegenerate
  exact tensor_nondegenerate matterBPZ beta matterBPZ_nondegenerate
    ⟨beta_left_radical, beta_right_radical⟩

#print axioms orbifoldBPZ_nondegenerate
#print axioms hyperbolicBPZ_nondegenerate
#print axioms matterBPZ_nondegenerate
#print axioms betaTotal_nondegenerate

end

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTBPZNondegenerate
